extern crate tempdir;

use clap::Parser;
use fs_extra::dir::*;
use log::{info, trace, warn};
use std::fs::{remove_file, File};
use std::io::{BufRead, BufReader, Read};
use std::process::Stdio;
use std::{
    env, fs,
    io::{self},
    path::Path,
    path::PathBuf,
};

use jwalk::WalkDir;

use tempdir::TempDir;

const BENCH_DIR: &'static str = "benchs";

const PROOF_DIR: &'static str = "proofs";

const RUN_DIR: &'static str = "run";

const ELAB_DIR: &'static str = "elabs";

const TRANSLATED_DIR: &'static str = "translated";

const RESULT_DIR: &'static str = "results";

const OUTPUT_DIR: &'static str = "output";

use thiserror::Error;

#[derive(Error, Debug)]
enum ErrorBench {
    #[error("IO erro")]
    IoErr(io::Error),
    #[error("IO erro")]
    FsEXtra(fs_extra::error::Error),
    #[error("Lambdapi check failed")]
    LambdapiError,
    #[error("Carcara failed to translate")]
    CarcaraError,
    #[error("Setup")]
    Setup(String),
}

impl From<io::Error> for ErrorBench {
    fn from(item: io::Error) -> Self {
        Self::IoErr(item)
    }
}

impl From<fs_extra::error::Error> for ErrorBench {
    fn from(item: fs_extra::error::Error) -> Self {
        Self::FsEXtra(item)
    }
}

/// Simple program to cgreet a person
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// If specified, only run tests containing this string in their names
    #[arg(short, long)]
    testname: Option<String>,
    /// Elaborate and translate, but don't run lambdapi check
    #[arg(short, long)]
    no_check: bool,
    /// Directory where the benchmarks will run and save its results
    #[arg(short, long)]
    rundir: Option<PathBuf>,
    /// Save the benchmarks output
    #[arg(short, long)]
    savedir: Option<PathBuf>,
    /// Alethe proof directory
    #[arg(short, long)]
    proofdir: Option<PathBuf>,
}

fn main() -> Result<(), ErrorBench> {
    env_logger::init();

    let curr_dir = env::current_dir().expect("No current directory?");

    let args = Args::parse();

    // Check benchmarks directory

    let bench_dir = curr_dir.join(BENCH_DIR);

    check_setup(&bench_dir)?;

    let proof_dir: PathBuf = if let Some(proofdir) = args.proofdir {
        println!("HI {}", proofdir.to_string_lossy());
        if fs::exists(&proofdir).is_ok() {
            trace!("Proof directory found so we do not regenerate the proof");
            Ok(proofdir)
        } else {
            Err(ErrorBench::Setup(format!(
                "Could not find the proof directory located at {}",
                proofdir.to_string_lossy()
            )))
        }
    } else {
        let p = curr_dir.join(PROOF_DIR);
        fs::create_dir(&p)?;
        replicate_dir_hierarchy(bench_dir.as_path(), p.as_path())?;
        generate_cvc5_proofs(bench_dir.as_path(), p.as_path())?;
        Ok(p)
    }?;

    // Create the temporary directory for benchmarks
    let run_dir = if let Some(dir) = args.rundir {
        TempDir::new_in(dir, RUN_DIR)?
    } else {
        TempDir::new(RUN_DIR)?
    };

    trace!(
        "Temporary directory for the benchmark located at {}",
        run_dir.path().to_string_lossy()
    );

    // Populate elab and translated directory

    let elab_dir = run_dir.path().join(ELAB_DIR);
    std::fs::create_dir(elab_dir.as_path())?;

    let translated_dir = run_dir.path().join(TRANSLATED_DIR);

    replicate_dir_hierarchy(bench_dir.as_path(), elab_dir.as_path())?;

    replicate_dir_hierarchy(bench_dir.as_path(), translated_dir.as_path())?;

    generate_alethe_proofs(&bench_dir, &proof_dir, &elab_dir)?;

    if let Some(dir) = args.savedir {
        let options = CopyOptions::new();
        trace!(
            "Copying {} to {}..",
            run_dir.path().to_string_lossy(),
            dir.to_string_lossy()
        );
        fs_extra::copy_items(&[run_dir.into_path()], dir, &options)
            .expect("Cannot copy the result");
    }

    Ok(())
}

fn replicate_dir_hierarchy(src: impl AsRef<Path>, dst: impl AsRef<Path>) -> io::Result<()> {
    fs::create_dir_all(&dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            replicate_dir_hierarchy(entry.path(), dst.as_ref().join(entry.file_name()))?;
        }
    }
    Ok(())
}

fn generate_cvc5_proofs(src: &Path, dst: &Path) -> Result<(), ErrorBench> {
    for entry in WalkDir::new(src) {
        let entry = entry.map_err(|_| ErrorBench::Setup("".to_string()))?;

        if entry.metadata().unwrap().is_file() {
            let entry_path: PathBuf = entry.path();

            if entry_path.extension().unwrap() == "smt2" {
                let entry_file = std::fs::File::open(&entry_path)?;

                let br = BufReader::new(&entry_file);
                let is_unsat = br
                    .lines()
                    .filter_map(Result::ok)
                    .any(|line| line.contains("unsat"));

                if is_unsat {
                    let entry_prefix = entry_path.strip_prefix(src).unwrap();
                    let proof_file_path = dst.join(entry_prefix).with_extension("alethe");

                    let proof_file = fs::File::create_new(&proof_file_path)?;

                    trace!(
                        "Generating proof for {}",
                        proof_file_path.as_path().to_string_lossy()
                    );

                    let status = std::process::Command::new("cvc5")
                        .arg("--dag-thresh=0")
                        .arg("--tlimit=500")
                        .arg("--produce-proofs")
                        .arg("--dump-proofs")
                        .arg("--proof-format-mode=alethe")
                        .arg("--proof-granularity=dsl-rewrite")
                        .arg("--proof-alethe-res-pivots")
                        .arg("--proof-elim-subtypes")
                        .arg("--print-arith-lit-token")
                        .arg(entry_path)
                        .stdout(Stdio::from(proof_file))
                        .status()?;

                    if status.success() == false {
                        remove_file(proof_file_path)?;
                    }
                }
            }
        }
    }
    Ok(())
}

fn generate_alethe_proofs(
    bench_dir: &Path,
    proof_dir: &Path,
    elab_dir: &Path,
) -> Result<(), ErrorBench> {
    info!("Generating elaborated alethe proof...");

    for entry in WalkDir::new(proof_dir) {
        let entry = entry.map_err(|e| ErrorBench::Setup(format!("{}", e)))?;

        if entry.metadata().unwrap().is_file() {
            let alethe_file_path: PathBuf = entry.path();

            let entry_prefix = alethe_file_path.strip_prefix(proof_dir).unwrap();

            let elab_proof_path = elab_dir.join(entry_prefix);

            let problem_file_path: PathBuf = bench_dir.join(entry_prefix).with_extension("smt2");

            let elab_proof = File::create_new(&elab_proof_path)?;

            let _ = std::process::Command::new("carcara")
                .arg("elaborate")
                .arg("-i")
                .args(["--log", "off"])
                .arg("--expand-let-bindings")
                .arg(alethe_file_path)
                .arg(problem_file_path)
                .arg("--no-print-with-sharing")
                .stdout(Stdio::from(elab_proof))
                .status()?;
        }
    }
    Ok(())
}

fn check_setup(bench_dir: &PathBuf) -> Result<(), ErrorBench> {
    info!("Checking setup...");

    std::process::Command::new("cvc5")
        .arg("--help")
        .stdout(Stdio::null())
        .spawn()?;
    info!("CVC5 found");

    std::process::Command::new("carcara")
        .arg("--help")
        .stdout(Stdio::null())
        .spawn()?;
    info!("Carcara found");

    std::process::Command::new("lambdapi")
        .arg("--help")
        .stdout(Stdio::null())
        .spawn()?;
    info!("Lambdapi found");

    if std::path::Path::new(&bench_dir).exists() {
        info!("Benchmarks directory {} found", bench_dir.to_string_lossy());
    } else {
        return Err(ErrorBench::Setup(format!(
            "Benchmarks directory not found {}",
            bench_dir.to_string_lossy()
        )));
    }

    Ok(())
}
