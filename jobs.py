#!/usr/bin/env python3

"""
run_benchmark.py — Simple script to initialize a benchmark job.

Usage:
    python run_benchmark.py --benchmark-dir /path/to/benchmarks [--output-dir /path/to/output] [--max-stage N]

Stage mapping:
  0: generate proofs only
  1: + elaborate
  2: + translate
  3: + lambdapi check (default if --max-stage omitted)
"""

import argparse
import uuid
from pathlib import Path
import subprocess
import sys
import re
import logging
import os
import shlex  # needed by load_env_file

# Configure the logging system once
logging.basicConfig(
    level=logging.DEBUG,  # or INFO for less verbosity
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)]
)

# Define shortcut aliases for convenience
debug = logging.debug
info = logging.info
error = logging.error
warning = logging.warning

def load_env_file(env_path: Path) -> dict:
    """
    Load KEY=VAL lines from env_path into os.environ.
    Ignores comments (#) and empty lines. Returns a dict of loaded values.
    """
    loaded = {}
    if not env_path.exists():
        return loaded

    try:
        text = env_path.read_text()
    except Exception:
        return loaded

    for line in text.splitlines():
        # strip comments and whitespace
        line = line.split("#", 1)[0].strip()
        if not line or "=" not in line:
            continue
        k, v = line.split("=", 1)
        k = k.strip()
        v = v.strip()
        # remove optional surrounding quotes and parse safely
        if (v.startswith('"') and v.endswith('"')) or (v.startswith("'") and v.endswith("'")):
            v = v[1:-1]
        try:
            v = shlex.split(v)[0]
        except Exception:
            pass
        os.environ[k] = v
        loaded[k] = v
    return loaded


# New helper: remove empty directories under proofs_dir (bottom-up)
def remove_empty_dirs(proofs_dir: Path) -> int:
    """Remove empty directories under proofs_dir. Returns number of removed dirs."""
    removed = 0
    # iterate depth-first (deepest first) so we can remove nested empty dirs
    for d in sorted((p for p in proofs_dir.rglob("*") if p.is_dir()), key=lambda p: len(p.parts), reverse=True):
        try:
            # if directory is empty, rmdir it
            next(d.iterdir())
        except StopIteration:
            try:
                d.rmdir()
                removed += 1
            except Exception as e:
                print(f"Failed to remove empty dir {d}: {e}", file=sys.stderr)
    return removed

def remove_empty_entries(root: Path) -> (int, int):
    """
    Remove empty files and empty directories under `root`.
    Returns (removed_files_count, removed_dirs_count).
    Does not attempt to remove `root` itself.
    """
    removed_files = 0
    removed_dirs = 0

    # Remove empty files first
    for f in root.rglob("*"):
        try:
            if f.is_file():
                try:
                    if f.stat().st_size == 0:
                        f.unlink()
                        removed_files += 1
                except Exception as e:
                    error(f"Failed to check/remove file {f}: {e}")
        except Exception:
            # ignore entries we can't stat
            continue

    # Remove empty directories bottom-up (deepest first)
    for d in sorted((p for p in root.rglob("*") if p.is_dir()), key=lambda p: len(p.parts), reverse=True):
        if d == root:
            continue
        try:
            # if directory is empty, rmdir it
            next(d.iterdir())
        except StopIteration:
            try:
                d.rmdir()
                removed_dirs += 1
            except Exception as e:
                error(f"Failed to remove empty dir {d}: {e}")

    return removed_files, removed_dirs

def clamp(n: int, lo: int, hi: int) -> int:
    return max(lo, min(hi, n))

def main():
    parser = argparse.ArgumentParser(description="Initialize a benchmark job.")
    parser.add_argument(
        "--benchmark-dir",
        required=True,
        type=Path,
        help="Path to the benchmark directory.",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("./output"),
        help="Optional output directory (default: ./output).",
    )
    parser.add_argument(
        "--max-stage",
        type=int,
        default=3,
        help="Stop after this stage: 0=gen-proof, 1=elaborate, 2=translate, 3=check (default: 3).",
    )
    args = parser.parse_args()

    benchmark_dir = args.benchmark_dir.resolve()
    output_dir = args.output_dir.resolve()
    max_stage = clamp(args.max_stage, 0, 3)

    # Run check-setup.sh and propagate its exit code if it fails
    script_dir = Path(__file__).resolve().parent

    check_script = script_dir / "check-setup.sh"
    if check_script.exists():
        rc = subprocess.run(["bash", str(check_script)], cwd=str(script_dir)).returncode
        if rc != 0:
            print(f"check-setup.sh failed with exit code {rc}", file=sys.stderr)
            sys.exit(rc)
    else:
        print("check-setup.sh not found; skipping", file=sys.stderr)

    if not benchmark_dir.is_dir():
        raise NotADirectoryError(f"Benchmark directory does not exist: {benchmark_dir}")
    
    # load config.env into environment so subprocesses inherit the values
    env_file = script_dir / "config.env"
    loaded_env = load_env_file(env_file)
    if loaded_env:
        info(f"Loaded config.env: {', '.join(f'{k}={v}' for k,v in loaded_env.items())}")

    # Ensure base output dir exists
    output_dir.mkdir(parents=True, exist_ok=True)

    # Generate job id and create job-specific directory
    job_id = uuid.uuid4()
    job_dir = output_dir / str(job_id)
    job_dir.mkdir(parents=True, exist_ok=True)

    # Ensure required subdirectories exist under the job directory
    subdirs = [
        job_dir / "logs",
        job_dir / "proofs",
        job_dir / "run" / "alethe",
        job_dir / "run" / "convert",
        job_dir / "run" / "results",
    ]
    for d in subdirs:
        d.mkdir(parents=True, exist_ok=True)

    info(f"Generated job UUID:  {job_id}")
    info(f"Benchmark directory: {benchmark_dir}")
    info(f"Output directory:    {output_dir}")
    info(f"Job directory:       {job_dir}")
    info(f"Max stage:           {max_stage}")

    # Write job info to file (job id and benchmark directory path)
    job_file = job_dir / "job_id.txt"
    job_file.write_text(f"job_id: {job_id}\nbenchmark_dir: {benchmark_dir}\n")
    info(f"Saved job info to:   {job_file}")

    # Run maintenance / proof scripts, propagating failures
    def run_script(script_path, args):
        if not script_path.exists():
            info(f"{script_path.name} not found; skipping", file=sys.stderr)
            return 0
        rc = subprocess.run(["bash", str(script_path)] + [str(a) for a in args], cwd=str(script_dir)).returncode
        if rc != 0:
            error(f"{script_path.name} failed with exit code {rc}", file=sys.stderr)
            sys.exit(rc)
        return rc

    proofs_dir = job_dir / "proofs"
    logs_dir = job_dir / "logs"

    # -------- Stage 0: generate cvc5/veriT proofs --------
    # clean-benchs.sh <benchmark_dir>
    run_script(script_dir / "clean-benchs.sh", [benchmark_dir])

    # gen-proof.sh <benchmark_dir> <job_dir>
    run_script(script_dir / "gen-proof.sh", [benchmark_dir, job_dir])

    # optional cleaning under proofs/
    (remfiles, remdirs) = remove_empty_entries(proofs_dir)
    debug(f"Removed {remfiles} empty files and {remdirs} directories under {proofs_dir}")

    if max_stage == 0:
        info("Stopping after stage 0 (proof generation).")
        return

    # -------- Stage 1: elaborate (Alethe elaboration) --------
    run_script(script_dir / "elaborate.sh", [job_dir, benchmark_dir])

    (remfiles, remdirs) = remove_empty_entries(job_dir / "run" / "alethe")
    debug(f"Removed {remfiles} empty files and {remdirs} directories under {job_dir / 'run' / 'alethe'}")

    if max_stage == 1:
        info("Stopping after stage 1 (elaboration).")
        return

    # -------- Stage 2: translate to Lambdapi --------
    run_script(script_dir / "translate.sh", [job_dir, benchmark_dir])

    (remfiles, remdirs) = remove_empty_entries(job_dir / "run" / "convert")
    debug(f"Removed {remfiles} empty files and {remdirs} directories under {job_dir / 'run' / 'convert'}")

    if max_stage == 2:
        info("Stopping after stage 2 (translation).")
        return

    # -------- Stage 3: check with Lambdapi --------
    run_script(script_dir / "check-lp.sh", [job_dir])

    (remfiles, remdirs) = remove_empty_entries(job_dir / "run" / "results")
    debug(f"Removed {remfiles} empty files and {remdirs} directories under {job_dir / 'run' / 'results'}")

    info("Pipeline completed successfully (stage 3).")

if __name__ == "__main__":
    main()
