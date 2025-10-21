#!./python

"""
run_benchmark.py — Simple script to initialize a benchmark job.

Usage:
    python run_benchmark.py --benchmark-dir /path/to/benchmarks [--output-dir /path/to/output]
"""

import argparse
import uuid
from pathlib import Path
import subprocess
import sys
import re
import logging

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

# def check_last_index(proofs_dir: Path, limit: int = 2000):
#     """Scan .proof files under proofs_dir and print the last t<number> index found for each file.
#     Delete files where the last step index exceeds `limit`.
#     """
#     step_pattern = re.compile(r'^\(step\s+t(\d+)\b', re.MULTILINE)

#     for p in sorted(proofs_dir.rglob("*.proof")):
#         try:
#             with p.open("rb") as f:
#                 # Read only the tail (last 8 KB) for speed
#                 f.seek(0, 2)
#                 size = f.tell()
#                 f.seek(max(size - 8192, 0))
#                 tail = f.read().decode("utf-8", errors="ignore")
#         except Exception as e:
#             print(f"{p}: <could not read> ({e})", file=sys.stderr)
#             continue

#         matches = step_pattern.findall(tail)
#         if not matches:
#             print(f"{p}: <no step found>")
#             continue

#         last = int(matches[-1])
#         if last > limit:
#             try:
#                 p.unlink()
#                 debug(f"{p}: {last} steps → removed (too large)")
#             except Exception as e:
#                 error(f"{p}: {last} → failed to remove ({e})", file=sys.stderr)

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
    args = parser.parse_args()

    benchmark_dir = args.benchmark_dir.resolve()
    output_dir = args.output_dir.resolve()

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

    # Write job info to file (job id and benchmark directory path)
    job_file = job_dir / "job_id.txt"
    job_file.write_text(f"job_id: {job_id}\nbenchmark_dir: {benchmark_dir}\n")
    info(f"Saved job info to:   {job_file}")

    # Run maintenance / proof scripts, propagating failures
    def run_script(script_path, args):
        if not script_path.exists():
            info(f"{script_path.name} not found; skipping", file=sys.stderr)
            return
        rc = subprocess.run(["bash", str(script_path)] + [str(a) for a in args], cwd=str(script_dir)).returncode
        if rc != 0:
            error(f"{script_path.name} failed with exit code {rc}", file=sys.stderr)
            sys.exit(rc)

    proofs_dir = job_dir / "proofs"
    logs_dir = job_dir / "logs"

    # clean-benchs.sh <benchmark_dir>
    run_script(script_dir / "clean-benchs.sh", [benchmark_dir])

    # gen-proof.sh <benchmark_dir> <proofs_dir> <logs_dir>
    run_script(script_dir / "gen-proof.sh", [benchmark_dir, job_dir])

    # clean-proof.sh <benchmark_dir> <proofs_dir> <logs_dir>
    #run_script(script_dir / "clean-proof.sh", [benchmark_dir, proofs_dir, logs_dir])

    info("Setup and auxiliary scripts completed successfully.")

    # Check last t<number> index in each proof file (done in Python)
    # check_last_index(proofs_dir,10000)

    # Remove empty directories left in proofs/ after cleaning
    (remfiles, remdirs) = remove_empty_entries(proofs_dir)
    debug(f"Removed {remfiles} empty files and {remdirs} directories under {proofs_dir}")

    run_script(script_dir / "elaborate.sh", [job_dir, benchmark_dir])

    (remfiles, remdirs) = remove_empty_entries(job_dir / "run" / "alethe")
    debug(f"Removed {remfiles} empty files and {remdirs} directories under {job_dir / "run" / "alethe"}")

    run_script(script_dir / "translate.sh", [job_dir, benchmark_dir])

    (remfiles, remdirs) = remove_empty_entries(job_dir / "run" / "convert")
    debug(f"Removed {remfiles} empty files and {remdirs} directories under {job_dir / "run" / "convert"}")

    run_script(script_dir / "check-lp.sh", [job_dir])

    (remfiles, remdirs) = remove_empty_entries(job_dir / "run" / "results")
    debug(f"Removed {remfiles} empty files and {remdirs} directories under {job_dir / "run" / "results"}")

if __name__ == "__main__":
    main()
