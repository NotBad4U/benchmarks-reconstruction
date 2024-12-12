use std::io;
use std::io::BufRead;
use std::path::PathBuf;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;

use file_test_runner::collect_and_run_tests;
use file_test_runner::collection::strategies::TestPerFileCollectionStrategy;
use file_test_runner::collection::CollectOptions;
use file_test_runner::collection::CollectedTest;
use file_test_runner::RunOptions;
use file_test_runner::TestResult;

use std::fs::File;
use thiserror::Error;


#[derive(Error, Debug)]
enum ErrorBench {
  #[error("Io erro")]
  IoErr(io::Error),
  #[error("Lambdapi check failed")]
  LambdapiError,
  #[error("Carcara failed to translate")]
  CarcaraError,
}



fn main() {
    collect_and_run_tests(
        CollectOptions {
            base: "tests/benchs".into(),
            strategy: Box::new(TestPerFileCollectionStrategy {
                file_pattern: Some("^.*\\.alethe$".to_owned()),
            }),
            filter_override: None,
        },
        RunOptions { parallel: true },
        |test| {
            if count_lines(&test.path) != 0 {
              let res = run_test(test);

              if let Ok(code) = res {
                if code.code().unwrap() == 0 {
                  TestResult::Passed
                } else {
                    TestResult::Failed { output: vec![] }
                }
              } else {
                TestResult::Failed { output: vec![] }
              }
            } else {
              TestResult::Ignored
            }           
        },
    )
}

fn run_test(test: &CollectedTest) -> Result<ExitStatus, ErrorBench> {
    // let file_name = &test.name;
    let alethe_file = test.path.clone();
    let problem_file = test.path.with_extension("smt2");

    let tmpdir: PathBuf = PathBuf::from("tmp");
    let lp_file_path = tmpdir.join(test.path.with_extension("lp").file_name().unwrap());

    let file = File::create(lp_file_path.clone()).unwrap();

    let status = Command::new("carcara")
      .arg("translate")
      .args(["--log", "off"])
      .arg("--expand-let-bindings")
      .arg("-i")
      .arg(alethe_file)
      .arg(problem_file)
      .stdout(Stdio::from(file))
      .stderr(Stdio::null())
      .status()
      .map_err(|e| ErrorBench::IoErr(e))
      ?;

    if status.code().unwrap() != 0 {
      std::fs::remove_file(lp_file_path).unwrap();
      return Err(ErrorBench::CarcaraError)
    }

    let status = Command::new("lambdapi")
      .args(["check", "-v0", "-w", "--timeout=100"])
      .arg(lp_file_path.clone())
      .status()
      .map_err(|e| ErrorBench::IoErr(e))
      ?;

    std::fs::remove_file(lp_file_path).unwrap();

    Ok(status)
}

fn count_lines(path: &PathBuf) -> usize {
    let lines = std::io::BufReader::new(std::fs::File::open(path).unwrap()).lines();
    let line_count = lines.count();
    line_count
}