#!/usr/bin/env python3
"""
dodo.py — the proof-reconstruction pipeline as a doit task graph.

Replaces: jobs.py + gen-proof.sh + clean-proof.sh + elaborate.sh + translate.sh
          + check-lp.sh + the joblog-regex half of jobres.py/parselogs.py.

Design notes
------------
* Identity is a *stem* (e.g. "QF_UF/eq_diamond/eq_diamond31"), carried explicitly
  from task to task.  Nothing is ever parsed back out of a command string.
* Each task writes a status record to <job>/status/<stage>/<stem>.json at the
  moment the tool runs.  That record — not the tool's artifact — is the doit
  target, so a tool that legitimately fails (timeout, no proof for `unsat`)
  still produces a target and does not abort the graph.
* Stages 1-3 are `@create_after` (delayed) creators.  They enumerate the
  artifacts that actually exist, which reproduces the current pipeline's
  "filter by filesystem state" semantics *and* gives us the dynamic
  small/large split, which a static Makefile cannot express.
* Measurement is deliberately left identical to check-lp.sh (hyperfine with the
  same flags, one outer wall-clock limit) so results are directly comparable to
  an existing job dir.  See the note on `runexec` at the bottom of this file.

Usage
-----
    BENCH_DIR=benchs/QF_UF/eq_diamond JOB_DIR=output/doit-run doit -n 8
    doit list --all          # inspect the graph
    doit clean               # remove targets
    python3 collects.py output/doit-run --csv out.csv

Parallelism: prefer threads.  Every action is subprocess-bound, so the GIL is
released while waiting, and threads avoid pickling the action closures:

    doit -n 8 --parallel-type thread
"""

from __future__ import annotations

import contextlib
import fcntl
import json
import os
import re
import shlex
import signal
import socket
import subprocess
import sys
import time
import uuid
from pathlib import Path
from typing import Iterable, Iterator

from doit import create_after

# =========================
# Configuration
# =========================

SCRIPT_DIR = Path(__file__).resolve().parent


def load_env_file(env_path: Path) -> dict:
    """Load KEY=VAL lines into os.environ (same semantics as jobs.py)."""
    loaded = {}
    if not env_path.exists():
        return loaded
    for line in env_path.read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if not line or "=" not in line:
            continue
        k, v = (part.strip() for part in line.split("=", 1))
        if len(v) >= 2 and v[0] == v[-1] and v[0] in "\"'":
            v = v[1:-1]
        os.environ.setdefault(k, v)
        loaded[k] = v
    return loaded


load_env_file(SCRIPT_DIR / os.environ.get("CONFIG_ENV", "config.env"))

BENCH_DIR = Path(os.environ.get("BENCH_DIR", "benchs")).resolve()
# NOTE: JOB_DIR must be stable across invocations — that is what makes resume work.
JOB_DIR = Path(os.environ.get("JOB_DIR", "output/doit-run")).resolve()

CVC5_TIMEOUT = float(os.environ.get("CVC5_TIMEOUT", 30))
ELAB_TIMEOUT = float(os.environ.get("CARCARA_CHECK_ELAB_TIMEOUT", 60))
TRANSLATE_TIMEOUT = float(os.environ.get("CARCARA_TRANSLATE_TIMEOUT", 60))
CHECK_TIMEOUT = float(os.environ.get("LAMBDAPI_CHECK_TIMEOUT", 60))
TRANSLATE_TARGET = os.environ.get("TRANSLATE_TARGET", "lambdapi")

# Parsing options that elaborate and translate MUST share.  carcara 1.1's
# `translate` re-elaborates its input (the old `--no-elab` is gone), so it has
# to parse the problem exactly as `elaborate` did.  With `--expand-let-bindings`
# on one side only, the let-expanded `assume` steps in the .elab no longer match
# the problem's assertions and carcara panics (exit 101):
#   "trying to elaborate assume, but it is invalid!"  (src/elaborator/mod.rs:270)
# That was 3,251 of 3,571 translations on full QF_UF.
PARSE_FLAGS = ["--expand-let-bindings"]
# dsl-rewrite makes cvc5 emit `rare_rewrite` steps, which carcara can only
# check when given the RARE database via --rare-file.  Without that file every
# elaboration fails with "the rule <name> wasn't found".
PROOF_GRANULARITY = os.environ.get("PROOF_GRANULARITY", "dsl-rewrite")
MAX_RUNS_SMALL = os.environ.get("MAX_RUN_HYPERFINE_SMALL", "10")
MAX_RUNS_LARGE = os.environ.get("MAX_RUN_HYPERFINE_LARGE", "1")

# gen-proof.sh globs '-e smt2' only, so the 36 *.smt files under TLAPS/Allocator
# are silently skipped today.  Kept as-is so runs stay comparable; add "*.smt"
# here (and teach problem_for() to find it) to fix that.
BENCH_GLOBS = ("*.smt2",)

PROOFS = JOB_DIR / "proofs"
ALETHE = JOB_DIR / "run" / "alethe"
SMALL = JOB_DIR / "run" / "convert" / "small"
LARGE = JOB_DIR / "run" / "convert" / "large"
RESULTS = JOB_DIR / "run" / "results"
STATUS = JOB_DIR / "status"
LOGS = JOB_DIR / "logs"

for _d in (PROOFS, ALETHE, SMALL, LARGE, RESULTS, STATUS, LOGS):
    _d.mkdir(parents=True, exist_ok=True)

DOIT_CONFIG = {
    "dep_file": str(JOB_DIR / ".doit.db"),
    "default_tasks": ["gen_proof", "elaborate", "translate", "check", "joblogs"],
    "verbosity": 1,
}


def _parse_size(spec: str) -> int:
    """Parse an fd --size spec ('1M', '500k', '2mi') into bytes, fd's way:
    bare k/m/g are decimal, ki/mi/gi are binary."""
    m = re.fullmatch(r"\s*(\d+)\s*([kmgt]i?|b)?\s*", spec, re.IGNORECASE)
    if not m:
        raise ValueError(f"bad size spec: {spec!r}")
    n, unit = int(m.group(1)), (m.group(2) or "b").lower()
    factors = {"b": 1, "k": 10**3, "m": 10**6, "g": 10**9, "t": 10**12,
               "ki": 2**10, "mi": 2**20, "gi": 2**30, "ti": 2**40}
    return n * factors[unit]


SPLIT_LIMIT = os.environ.get("PROOF_SPLIT_LIMIT", "1M")
SPLIT_BYTES = _parse_size(SPLIT_LIMIT)

# SKIP_LARGE=1: do not translate or check proofs over PROOF_SPLIT_LIMIT.
# Large proofs dominate the run time (on eq_diamond, translation took a median
# 0.13s small vs 5.9s large), so this is for iterating quickly.  Stages 0-1
# still run on everything, since a proof's size is only known once it has been
# elaborated.  Unset it and rerun the same JOB_DIR to do the large ones later:
# the small ones are up to date and are skipped.
SKIP_LARGE = os.environ.get("SKIP_LARGE", "").strip().lower() in ("1", "true", "yes", "on")

# RETRY_FAILED=translate,check reruns the tasks in those stages whose last
# record is not a success, and nothing else.  Needed because doit only watches
# files: installing a Lambdapi library, fixing a tool flag or changing a
# timeout changes no file it tracks, and a failed tool still leaves a valid
# record, so without this the failures count as done forever.
# Stages: gen_proof, elaborate, translate, check -- or `all`.
STAGES = ("gen_proof", "elaborate", "translate", "check")


def _parse_retry(spec: str) -> frozenset:
    spec = spec.strip().lower()
    if spec in ("", "0", "false", "no", "off"):
        return frozenset()
    if spec in ("1", "true", "yes", "on", "all"):
        return frozenset(STAGES)
    names = {x.strip() for x in spec.split(",") if x.strip()}
    unknown = names - set(STAGES)
    if unknown:
        sys.exit(f"RETRY_FAILED: unknown stage(s) {', '.join(sorted(unknown))}; "
                 f"choose from {', '.join(STAGES)}, or all")
    return frozenset(names)


RETRY_FAILED = _parse_retry(os.environ.get("RETRY_FAILED", ""))
if RETRY_FAILED:
    print("RETRY_FAILED: rerunning failed tasks in: "
          + ", ".join(x for x in STAGES if x in RETRY_FAILED), file=sys.stderr)


# =========================
# Running & recording
# =========================

def run_limited(cmd: list[str], timeout: float, *,
                stdout_path: Path | None = None,
                cwd: Path | None = None) -> tuple[int, int, float, float]:
    """Run `cmd` under a wall-clock limit, killing the whole process group.

    Returns (exitval, signal, start_epoch, wall_seconds).

    Killing the process *group* is why this is safer than `parallel --timeout`
    for the large-proof stage, where the timed command is `make -j` and the
    work happens in grandchildren that a plain SIGTERM to the child misses.
    """
    out = open(stdout_path, "wb") if stdout_path else subprocess.DEVNULL
    start = time.time()
    try:
        try:
            proc = subprocess.Popen(
                cmd, stdout=out, stderr=subprocess.DEVNULL,
                cwd=str(cwd) if cwd else None, start_new_session=True,
            )
        except OSError as e:
            # Missing binary or unreadable cwd: record it like any other
            # failure rather than tearing down the graph.  127 is the shell's
            # "command not found", which classify() already treats as an error.
            print(f"cannot exec {cmd[0]!r}: {e}", file=sys.stderr)
            return 127, 0, start, 0.0
        try:
            rc = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            _kill_group(proc)
            return -1, 15, start, time.time() - start
    finally:
        if stdout_path:
            out.close()

    wall = time.time() - start
    return (rc, 0, start, wall) if rc >= 0 else (-1, -rc, start, wall)


def _kill_group(proc: subprocess.Popen) -> None:
    try:
        pgid = os.getpgid(proc.pid)
    except ProcessLookupError:
        return
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(pgid, sig)
        except ProcessLookupError:
            return
        try:
            proc.wait(timeout=5)
            return
        except subprocess.TimeoutExpired:
            continue


def classify(exitval: int, sig: int) -> str:
    """Same mapping collects.py applies to parallel joblogs."""
    if sig == 15:
        return "timeout"
    return "success" if (sig == 0 and exitval == 0) else "error"


def status_path(stage: str, stem: str) -> Path:
    return STATUS / stage / f"{stem}.json"


def retry_gate(group: str, record_stage: str, stem: str):
    """doit `uptodate` check.  When RETRY_FAILED names this task's stage, a
    task whose last record is not a success is out of date and runs again.
    Otherwise it has no opinion, and doit's usual file checks decide."""
    def last_run_succeeded() -> bool:
        if group not in RETRY_FAILED:
            return True
        try:
            return json.loads(status_path(record_stage, stem).read_text())["status"] == "success"
        except (OSError, ValueError, KeyError):
            return False
    return last_run_succeeded


def record(stage: str, stem: str, cmd: Iterable[str], exitval: int, sig: int,
           start: float, wall: float, **extra) -> None:
    """Write the one authoritative record for (stage, stem)."""
    p = status_path(stage, stem)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps({
        "stem": stem,
        "stage": stage,
        "status": classify(exitval, sig),
        "exitval": exitval,
        "signal": sig,
        "starttime": round(start, 3),
        "runtime_seconds": round(wall, 3),
        "command": " ".join(shlex.quote(c) for c in cmd),
        **extra,
    }, indent=2) + "\n")


def problem_for(stem: str) -> Path:
    """The original SMT-LIB problem — the second input that makes this a DAG
    rather than a pipe."""
    return BENCH_DIR / f"{stem}.smt2"


def split_status_line(path: Path) -> str:
    """Remove carcara's leading status word from a proof file, returning it."""
    if not path.exists() or path.stat().st_size == 0:
        return ""
    with path.open("rb") as fh:
        first = fh.readline()
        rest = fh.read()
    word = first.decode(errors="ignore").strip()
    if not word or word.startswith("("):
        return ""  # no status line; leave the file alone
    path.write_bytes(rest)
    return word


def discard_unless_ok(path: Path, exitval: int, sig: int) -> str:
    """Delete `path` unless the tool that wrote it exited cleanly.

    A tool killed by the timeout has usually already streamed part of its
    output -- carcara elaborate prints its status line and starts on the
    proof before it is killed -- so a non-empty file proves nothing.  Keeping
    it passes a truncated artifact downstream, where the next stage fails on
    it too and the benchmark is counted as a failure twice.

    Returns the reason for discarding, or "" if the artifact was kept.
    """
    if (exitval, sig) == (0, 0):
        return ""
    if path.exists():
        path.unlink()
    return "incomplete" if sig else f"exit:{exitval}"


def drop_if_empty(path: Path) -> bool:
    """jobs.py's remove_empty_entries(), applied at the point of production."""
    if path.exists() and path.stat().st_size == 0:
        path.unlink()
        return True
    return False


# =========================
# Stage 0 — cvc5
# =========================

def do_gen_proof(stem: str) -> bool:
    out = PROOFS / f"{stem}.proof"
    out.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "cvc5", "--produce-proofs", "--dump-proofs",
        "--proof-format-mode=alethe", f"--proof-granularity={PROOF_GRANULARITY}",
        "--proof-alethe-res-pivots", "--proof-elim-subtypes",
        "--print-arith-lit-token", str(problem_for(stem)),
    ]
    ev, sg, start, wall = run_limited(cmd, CVC5_TIMEOUT, stdout_path=out)

    # Only an answer of `unsat` followed by a proof body is a proof.  Anything
    # else must be dropped here or stage 1 picks it up and records it as an
    # elaboration *error*: cvc5 prints `sat`/`unknown` with exit status 0, so
    # the exit code alone does not tell them apart.
    dropped = discard_unless_ok(out, ev, sg)
    text = out.read_text(errors="ignore") if out.exists() else ""
    answer, _, body = text.lstrip().partition("\n")
    answer = answer.strip()
    if dropped:
        pass
    elif not text.strip():
        dropped = "empty"
    elif answer != "unsat":
        dropped = f"answer:{answer[:32]}"   # sat, unknown, an error message...
    elif not body.strip():
        dropped = "unsat-only"              # unsat, but no proof was dumped
    if dropped and out.exists():
        out.unlink()

    record("cvc5", stem, cmd, ev, sg, start, wall, dropped=dropped)
    return True  # never fail the task; the record carries the outcome


def task_gen_proof():
    """cvc5: benchs/<stem>.smt2 -> proofs/<stem>.proof"""
    for src in sorted(_iter_benchmarks()):
        stem = str(src.relative_to(BENCH_DIR).with_suffix(""))
        yield {
            "name": stem,
            "actions": [(do_gen_proof, [stem])],
            "file_dep": [str(src)],
            "targets": [str(status_path("cvc5", stem))],
            "uptodate": [retry_gate("gen_proof", "cvc5", stem)],
            "clean": True,
        }


def _iter_benchmarks() -> Iterator[Path]:
    for pattern in BENCH_GLOBS:
        yield from BENCH_DIR.rglob(pattern)


# =========================
# Stage 1 — carcara elaborate
# =========================

def do_elaborate(stem: str) -> bool:
    out = ALETHE / f"{stem}.elab"
    out.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "carcara", "elaborate", "--no-print-with-sharing",
        *PARSE_FLAGS, "-i", "--log", "off",
        str(PROOFS / f"{stem}.proof"), str(problem_for(stem)),
    ]
    ev, sg, start, wall = run_limited(cmd, ELAB_TIMEOUT, stdout_path=out)
    # carcara 1.1 prefixes the elaborated proof with a status word ("holey"
    # when -i turned unknown rules into holes).  `translate` cannot parse it,
    # so strip it here and keep it as data: it says whether the proof still
    # contains holes, which is worth reporting rather than discarding.
    dropped = discard_unless_ok(out, ev, sg)
    proof_status = "" if dropped else split_status_line(out)
    drop_if_empty(out)
    record("elaborate", stem, cmd, ev, sg, start, wall,
           proof_status=proof_status, dropped=dropped)
    return True


@create_after(executed="gen_proof", target_regex=r".*/status/elaborate/.*\.json")
def task_elaborate():
    """carcara elaborate: (proof, problem) -> run/alethe/<stem>.elab"""
    for proof in sorted(PROOFS.rglob("*.proof")):
        stem = str(proof.relative_to(PROOFS).with_suffix(""))
        problem = problem_for(stem)
        if not problem.exists():
            continue
        yield {
            "name": stem,
            "actions": [(do_elaborate, [stem])],
            "file_dep": [str(proof), str(problem)],
            "targets": [str(status_path("elaborate", stem))],
            "uptodate": [retry_gate("elaborate", "elaborate", stem)],
            "clean": True,
        }


# =========================
# Stage 2 — carcara translate (the dynamic split)
# =========================

def do_translate_small(stem: str) -> bool:
    out = SMALL / f"{stem}.lp"
    out.parent.mkdir(parents=True, exist_ok=True)
    cmd = ["carcara", "translate", "--admit-unsupported", *PARSE_FLAGS, TRANSLATE_TARGET,
           str(ALETHE / f"{stem}.elab"), str(problem_for(stem))]
    ev, sg, start, wall = run_limited(cmd, TRANSLATE_TIMEOUT, stdout_path=out)
    dropped = discard_unless_ok(out, ev, sg)
    drop_if_empty(out)
    record("translate_small", stem, cmd, ev, sg, start, wall, dropped=dropped)
    return True


def do_translate_large(stem: str) -> bool:
    # carcara 1.1 dropped `-n <segment>` / `-o <dir>`, so a large proof is no
    # longer split into a directory of segments with a generated Makefile.  It
    # produces one .lp like any other and is checked directly instead of with
    # `make -j`.  The small/large split is kept only because the reporting
    # (and collects.py) separates the two.
    out = LARGE / f"{stem}.lp"
    out.parent.mkdir(parents=True, exist_ok=True)
    cmd = ["carcara", "translate", "--admit-unsupported", *PARSE_FLAGS, TRANSLATE_TARGET,
           str(ALETHE / f"{stem}.elab"), str(problem_for(stem))]
    ev, sg, start, wall = run_limited(cmd, TRANSLATE_TIMEOUT, stdout_path=out)
    dropped = discard_unless_ok(out, ev, sg)
    drop_if_empty(out)
    record("translate_large", stem, cmd, ev, sg, start, wall, dropped=dropped)
    return True


@create_after(executed="elaborate", target_regex=r".*/status/translate_.*\.json")
def task_translate():
    """carcara translate -> convert/{small,large}/<stem>.lp

    The routing depends on the size of a file produced by the *previous* stage.
    That is the piece a static Makefile cannot express without re-invoking make.
    """
    skipped = 0
    for elab in sorted(ALETHE.rglob("*.elab")):
        stem = str(elab.relative_to(ALETHE).with_suffix(""))
        problem = problem_for(stem)
        if not problem.exists():
            continue
        # fd's -1M/+1M both match a file of exactly the limit, so today such a
        # file is translated twice.  '<=' / '>' here makes the split a partition.
        small = elab.stat().st_size <= SPLIT_BYTES
        if not small and SKIP_LARGE:
            skipped += 1
            continue
        stage = "translate_small" if small else "translate_large"
        action = do_translate_small if small else do_translate_large
        yield {
            "name": stem,
            "actions": [(action, [stem])],
            "file_dep": [str(elab), str(problem)],
            "targets": [str(status_path(stage, stem))],
            "uptodate": [retry_gate("translate", stage, stem)],
            "clean": True,
        }
    _report_skipped("translating", skipped)


# =========================
# Stage 3 — lambdapi check, timed with hyperfine
# =========================

@contextlib.contextmanager
def one_check_at_a_time():
    """Serialise the timed checks, whatever `-n` the run was started with.

    The check timings are the numbers that get reported, and a timing taken
    while other checks compete for the same cores measures the load, not
    lambdapi.  Stages 0-2 are not timed, so they stay fully parallel; this
    lock is what lets a single `doit -n 8` run the whole pipeline correctly
    instead of needing a separate `doit -n 1 check`.

    An flock on a file, not a threading.Lock, so it also holds with
    `--parallel-type process`.  It is taken *before* the clock starts, so
    time spent queueing does not count against LAMBDAPI_CHECK_TIMEOUT.
    """
    with open(JOB_DIR / ".check.lock", "w") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(fh, fcntl.LOCK_UN)


def _hyperfine(stem: str, stage: str, inner: str, cwd: Path,
               warmup: str, max_runs: str) -> bool:
    export = RESULTS / f"{stem}.json"
    export.parent.mkdir(parents=True, exist_ok=True)
    cmd = ["hyperfine", "--warmup", warmup, "--max-runs", max_runs,
           "--time-unit", "second", "--export-json", str(export), inner]
    with one_check_at_a_time():
        ev, sg, start, wall = run_limited(cmd, CHECK_TIMEOUT, cwd=cwd)
    record(stage, stem, cmd, ev, sg, start, wall, export=str(export))
    return True


def do_check_small(stem: str) -> bool:
    return _hyperfine(stem, "lambdapi_small_check",
                      f"lambdapi check -w -v 0 {shlex.quote(stem + '.lp')}",
                      cwd=SMALL, warmup="3", max_runs=MAX_RUNS_SMALL)


def do_check_large(stem: str) -> bool:
    return _hyperfine(stem, "lambdapi_large_check",
                      f"lambdapi check -w -v 0 {shlex.quote(stem + '.lp')}",
                      cwd=LARGE, warmup="0", max_runs=MAX_RUNS_LARGE)


def ensure_lambdapi_pkg(d: Path) -> None:
    """`lambdapi check` refuses a file that is not under a package root:
    "cannot be mapped under the library root".  check-lp.sh cds into the
    convert dirs but never puts a package file there, so drop the repo's
    lambdapi.pkg in alongside the generated proofs."""
    pkg = d / "lambdapi.pkg"
    if pkg.exists():
        return
    d.mkdir(parents=True, exist_ok=True)
    src = SCRIPT_DIR / "lambdapi.pkg"
    pkg.write_text(src.read_text() if src.exists()
                   else "package_name = bench\nroot_path = bench\n")


@create_after(executed="translate", target_regex=r".*/status/lambdapi_.*\.json")
def task_check():
    """hyperfine around `lambdapi check`, for small and large proofs alike."""
    for d in (SMALL, LARGE):
        ensure_lambdapi_pkg(d)

    for lp in sorted(SMALL.rglob("*.lp")):
        stem = str(lp.relative_to(SMALL).with_suffix(""))
        yield {
            "name": f"small/{stem}",
            "actions": [(do_check_small, [stem])],
            "file_dep": [str(lp)],
            "targets": [str(status_path("lambdapi_small_check", stem))],
            "uptodate": [retry_gate("check", "lambdapi_small_check", stem)],
            "clean": True,
        }

    large = sorted(LARGE.rglob("*.lp"))
    if SKIP_LARGE:
        _report_skipped("checking", len(large))
        large = []
    for lp in large:
        stem = str(lp.relative_to(LARGE).with_suffix(""))
        yield {
            "name": f"large/{stem}",
            "actions": [(do_check_large, [stem])],
            "file_dep": [str(lp)],
            "targets": [str(status_path("lambdapi_large_check", stem))],
            "uptodate": [retry_gate("check", "lambdapi_large_check", stem)],
            "clean": True,
        }


def _report_skipped(what: str, n: int) -> None:
    """Say it out loud: skipped proofs are simply absent from the later
    stages' records, so a silent skip would read as failures in the report."""
    if n:
        print(f"SKIP_LARGE: not {what} {n} proof(s) over "
              f"PROOF_SPLIT_LIMIT={SPLIT_LIMIT}", file=sys.stderr)


def _leaf_dirs(root: Path) -> Iterator[Path]:
    """Directories with no sub-directories — check-lp.sh's nested `fd -td`."""
    for d in root.rglob("*"):
        if d.is_dir() and not any(c.is_dir() for c in d.iterdir()):
            yield d


# =========================
# Reporting — emit GNU-parallel-shaped joblogs so collects.py works unchanged
# =========================

JOBLOG_NAMES = {
    "cvc5": "cvc5.txt",
    "elaborate": "elab_logs.txt",
    "translate_small": "translate_small_logs.txt",
    "translate_large": "translate_large_logs.txt",
    "lambdapi_small_check": "lambdapi_small_checks.txt",
    "lambdapi_large_check": "lambdapi_large_checks.txt",
}
JOBLOG_HEADER = ("Seq", "Host", "Starttime", "JobRuntime",
                 "Send", "Receive", "Exitval", "Signal", "Command")


def do_joblogs() -> bool:
    """Fold the per-task records into the TSVs collects.py already parses.

    This exists so a doit run can be diffed against an existing job dir with the
    current tooling.  The records under status/ are the real output; once
    collects.py reads those directly, this task can go away.
    """
    (JOB_DIR / "job_id.txt").write_text(
        f"job_id: {uuid.uuid5(uuid.NAMESPACE_URL, str(JOB_DIR))}\n"
        f"benchmark_dir: {BENCH_DIR}\n"
    )
    host = socket.gethostname()

    for stage, filename in JOBLOG_NAMES.items():
        stage_dir = STATUS / stage
        records = []
        if stage_dir.exists():
            for f in sorted(stage_dir.rglob("*.json")):
                try:
                    records.append(json.loads(f.read_text()))
                except json.JSONDecodeError:
                    print(f"skipping malformed record: {f}", file=sys.stderr)
        if not records:
            continue

        records.sort(key=lambda r: r["starttime"])
        with (LOGS / filename).open("w", encoding="utf-8") as fh:
            fh.write("\t".join(JOBLOG_HEADER) + "\n")
            for seq, r in enumerate(records, start=1):
                fh.write("\t".join(str(x) for x in (
                    seq, host, r["starttime"], r["runtime_seconds"],
                    0, 0, r["exitval"], r["signal"], r["command"],
                )) + "\n")
        print(f"  {filename}: {len(records)} records")
    return True


@create_after(executed="check")
def task_joblogs():
    """Aggregate status/**/*.json -> logs/*.txt (GNU parallel joblog format)."""
    yield {
        "name": "aggregate",
        "actions": [do_joblogs],
        "uptodate": [False],  # cheap; always refresh
        "verbosity": 2,
    }


# NOTE on measurement: hyperfine here runs under whatever concurrency `doit -n`
# was given, so timings are wall-clock-under-load, same as today.  To fix that
# without changing anything else, replace run_limited() with a call to
# BenchExec's `runexec --timelimit N --memlimit M --cores <pinned>`, which
# measures CPU time and peak RSS per run and pins cores.  Linux only.
