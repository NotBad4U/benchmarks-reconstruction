#!/usr/bin/env python3
"""
Aggregate benchmark job directories:
- Parse text logs (cvc5, elaboration, translate_*) with runtimes in seconds.
- Parse Lambdapi JSON results (run/results/*.json) and aggregate timings in milliseconds:
  * Global weighted mean across files using per-file mean weighted by len(times) (fallback weight=1).
  * Global Q1/Q3 computed on the concatenation of all raw 'times' across files
    (fallback to using per-file means as samples if no raw times exist).
- Print per-job summaries; optionally write CSV with per-job metrics.

CLI:
  collects.py [ROOT=. ] [--csv OUT.csv] [--skip-empty]
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import statistics
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, MutableMapping, Sequence, Tuple

# =========================
# Configuration & Constants
# =========================

TYPES = {"QF_LIA", "QF_UF", "LIA", "UF", "UFLIA", "TLAPS"}

LOG_MAP: Mapping[str, str] = {
    "cvc5.txt": "cvc5",
    "elab_logs.txt": "elaboration",
    "translate_small_logs.txt": "translate_small",
    "translate_large_logs.txt": "translate_large",
    "lambdapi_small_checks.txt": "lambdapi_small_check",
    "lambdapi_large_checks.txt": "lambdapi_large_check",
}

JSON_LOG_KIND = "lambdapi"  # kind label for Lambdapi JSON results

# If 'times'/'mean' inside results JSON are already in milliseconds set True; if in seconds set False.
JSON_TIMES_ARE_MS = True

HEADERS_EXPECTED = ("Seq", "Host", "Starttime", "JobRuntime", "Send", "Receive", "Exitval", "Signal", "Command")


# ============
# Data Models
# ============

@dataclass(frozen=True)
class MetaCommon:
    job_id: str
    benchmark_type: str
    benchmark_name: str
    job_dir: Path


@dataclass
class Row:
    """Normalized row from either a text log (seconds) or a JSON result (ms)."""
    job_id: str
    benchmark_type: str
    benchmark_name: str
    seq: str
    jobruntime_seconds: float      # for logs: seconds; for Lambdapi JSON: holds ms (historical name kept)
    exitval: str
    signal: str
    status: str                     # "success" | "timeout" | "error"
    command: str
    log_kind: str                   # one of LOG_MAP values or JSON_LOG_KIND
    job_dir: str
    # Optional (JSON aggregation helpers)
    mean_ms: float | None = None
    times_count: int | None = None
    times_ms: List[float] | None = None


# ===============
# Helper Functions
# ===============

def infer_type_and_name(benchmark_dir: str) -> Tuple[str, str]:
    """Infer (logic_type, benchmark_name) from a benchmark_dir path."""
    parts = [p for p in Path(benchmark_dir).parts if p and p != os.sep]
    for i, p in enumerate(parts):
        if p in TYPES:
            name = parts[i + 1] if i + 1 < len(parts) else ""
            return p, name
    return "", ""


def parse_job_id_txt(job_id_path: Path) -> Tuple[str, str]:
    """Parse job_id.txt for job_id and benchmark_dir."""
    job_id = ""
    benchmark_dir = ""
    try:
        with job_id_path.open(encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line.startswith("job_id:"):
                    job_id = line.split("job_id:", 1)[1].strip()
                elif line.startswith("benchmark_dir:"):
                    benchmark_dir = line.split("benchmark_dir:", 1)[1].strip()
    except Exception:
        pass
    return job_id, benchmark_dir


def classify(exitval_str: str, signal_str: str) -> str:
    """Map exit code & signal to status."""
    try:
        exitval = int(exitval_str)
    except Exception:
        exitval = None
    try:
        signal = int(signal_str)
    except Exception:
        signal = None

    if signal == 15:
        return "timeout"
    if signal == 0 and exitval is not None and exitval != 0:
        return "error"
    if exitval == 0:
        return "success"
    return "error"


def parse_log_file(log_path: Path, meta: MetaCommon, rows_out: List[Row], log_kind: str | None = None) -> None:
    """Parse a text log TSV and append normalized rows (seconds) to rows_out."""
    try:
        with log_path.open(encoding="utf-8") as f:
            header = f.readline().rstrip("\n").split("\t")
            idx = {col: header.index(col) for col in HEADERS_EXPECTED if col in header}
            for needed in ("Seq", "JobRuntime", "Exitval", "Signal", "Command"):
                if needed not in idx:
                    return

            for raw in f:
                line = raw.rstrip("\n")
                if not line:
                    continue
                parts = line.split("\t")
                if len(parts) < len(header):
                    continue

                seq = parts[idx["Seq"]]
                jobruntime = parts[idx["JobRuntime"]]
                exitval = parts[idx["Exitval"]]
                signal = parts[idx["Signal"]]
                command = parts[idx["Command"]]
                status = classify(exitval, signal)

                rows_out.append(Row(
                    job_id=meta.job_id,
                    benchmark_type=meta.benchmark_type,
                    benchmark_name=meta.benchmark_name,
                    seq=str(seq),
                    jobruntime_seconds=round(float(jobruntime), 3),  # seconds
                    exitval=str(exitval),
                    signal=str(signal),
                    status=status,
                    command=command,
                    log_kind=log_kind or LOG_MAP[log_path.name],
                    job_dir=str(meta.job_dir),
                ))
    except FileNotFoundError:
        pass


# -----------------------------
# JSON (Lambdapi) file handling
# -----------------------------

def analyze_json_results(json_file: Path) -> Tuple[bool, float, int, List[float]]:
    """
    Analyze one JSON file under run/results.
    Returns:
        success: bool
        mean_ms: float (ms)
        n_samples: int
        times_ms: list[float] (ms)
    Expected format:
      {"results":[{"mean": <float>, "times": [<float>, ...], "exit_codes":[int,...]}]}
    """
    factor = 1.0 if JSON_TIMES_ARE_MS else 1000.0
    try:
        with json_file.open() as f:
            data = json.load(f)
        results = (data.get("results") or [])
        if not results:
            return False, 0.0, 0, []
        r0: Dict[str, Any] = results[0]

        mean_ms = float(r0.get("mean", 0.0)) * factor
        times_raw = r0.get("times", []) or []
        times_ms = [float(t) * factor for t in times_raw]
        n = len(times_ms)
        success = all(int(code) == 0 for code in (r0.get("exit_codes") or []))
        return success, mean_ms, n, times_ms
    except Exception as e:
        print(f"Error processing {json_file}: {e}")
        return False, 0.0, 0, []


def collect_results(root: Path, meta: MetaCommon, rows_out: List[Row]) -> None:
    """Collect JSON Lambdapi results from root/run/results and append rows (ms) to rows_out."""
    results_dir = root / "run" / "results"
    if not results_dir.exists():
        return

    for json_file in results_dir.rglob("*.json"):
        success, mean_ms, n_samples, times_ms = analyze_json_results(json_file)
        status = "success" if success else "error"
        rows_out.append(Row(
            job_id=meta.job_id,
            benchmark_type=meta.benchmark_type,
            benchmark_name=meta.benchmark_name,
            seq=json_file.stem,
            jobruntime_seconds=float(mean_ms),
            exitval="0" if success else "1",
            signal="0",
            status=status,
            command=f"lambdapi check {json_file.name}",
            log_kind=JSON_LOG_KIND,
            job_dir=str(meta.job_dir),
            mean_ms=float(mean_ms),
            times_count=int(n_samples),
            times_ms=times_ms,
        ))


def collect_job_stats(job_dir: Path, rows: List[Row]):
    """
    Aggregate per-job stats.

    Text logs (seconds): counts and runtime summaries.
    Lambdapi JSON (ms):
      - Global weighted mean across files (weights = len(times_i), fallback 1).
      - Q1/Q3 computed on per-file mean_ms values ONLY (ignoring raw 'times').
      - Min/Max from per-file mean values only.
    """
    counts: Dict[Tuple[str, str], int] = {}
    runtimes: Dict[str, List[float]] = {}

    # Lambdapi accumulators
    # total = success = failure = 0
    weighted_numer = 0.0
    weighted_denom = 0.0
    mean_list_ms: List[float] = []  # used for Q1/Q3 and min/max    # CHANGED

    btype = rows[0].benchmark_type if rows else "unknown"
    bname = rows[0].benchmark_name if rows else "unknown"

    for r in rows:
        kind_status = (r.log_kind, r.status)
        counts[kind_status] = counts.get(kind_status, 0) + 1

        # ---------- LOGS: build per-kind runtimes, but EXCLUDE timeouts ----------
        # (This is where cvc5/elaboration/translate_* get their stats from.)
        if r.log_kind in LOG_MAP.values() and r.status != "timeout":
            # text logs store seconds in jobruntime_seconds
            runtimes.setdefault(r.log_kind, []).append(float(r.jobruntime_seconds))

        # ---------- Lambdapi JSON aggregation ----------
        if r.log_kind == JSON_LOG_KIND:
            # Per-file mean (ms)
            mean_ms = float(r.mean_ms if r.mean_ms is not None else r.jobruntime_seconds)
            mean_list_ms.append(mean_ms)

            # Weighted mean pieces (weight by number of samples; fallback 1)
            weight = r.times_count if r.times_count is not None and r.times_count > 0 else 1
            weighted_numer += mean_ms * weight
            weighted_denom += weight

    # Weighted mean across files
    weighted_mean_ms = (weighted_numer / weighted_denom) if weighted_denom > 0 else 0.0

    # Q1/Median/Q3 from per-file means only
    samples_sorted = sorted(mean_list_ms)
    if samples_sorted:
        try:
            qs = statistics.quantiles(samples_sorted, n=4)
            q1_lp, median_lp, q3_lp = qs[0], qs[1], qs[2]
        except statistics.StatisticsError:
            # Fallback if too few data points
            q1_lp, median_lp, q3_lp = weighted_mean_ms
    else:
        q1_lp = median_lp = q3_lp = 0.0

    # Min/Max strictly from per-file means (unchanged logically)
    if mean_list_ms:
        min_ms = min(mean_list_ms)
        max_ms = max(mean_list_ms)
    else:
        min_ms = max_ms = 0.0

    stats: Dict[str, Any] = {
        "job_id": job_dir.name,
        "benchmark_type": btype,
        "benchmark_name": bname,
        "weighted_mean_time": round(weighted_mean_ms * 1000, 0),
        "min_lp": round(min_ms * 1000, 0),
        "q1_lp": round(q1_lp * 1000, 0),
        "median_lp": round(median_lp * 1000, 0),
        "q3_lp": round(q3_lp * 1000, 0),
        "max_lp": round(max_ms * 1000, 0),
    }

     # Per-stage (text logs) in seconds
    for kind in LOG_MAP.values():
        stats.update({
            f"{kind}_success": counts.get((kind, "success"), 0),
            f"{kind}_timeout": counts.get((kind, "timeout"), 0),
            f"{kind}_error": counts.get((kind, "error"), 0),
        })
        rt = [x for x in runtimes.get(kind, []) if isinstance(x, (int, float))]

        try:
            qs = statistics.quantiles(rt, n=4)
            q1, median, q3 = qs[0], qs[1], qs[2]
        except statistics.StatisticsError:
            q1 = min(rt)
            q3 = max(rt)
            median = rt[0] if len(rt) == 1 else 0.0

        n = counts.get((kind, "success"), 0) + counts.get((kind, "timeout"), 0) + counts.get((kind, "error"), 0)

        stats.update({
            f"{kind}_count": n,
            f"{kind}_mean": round(sum(rt) / n, 3),
            f"{kind}_min": round(min(rt), 3),
            f"{kind}_q1": round(q1, 3),
            f"{kind}_median": round(median, 3),
            f"{kind}_q3": round(q3, 3),
            f"{kind}_max": round(max(rt), 3),
        })

    return stats, counts

# =============
# Pretty Output
# =============

def print_job_report(job_dir: Path,
                     rows: List[Row],
                     stats: Dict[str, Any],
                     counts: Mapping[Tuple[str, str], int],
                    ) -> None:
    """Pretty-print per-job summary. Lambdapi in ms; text logs in seconds."""
    btype = rows[0].benchmark_type if rows else "unknown"
    bname = rows[0].benchmark_name if rows else "unknown"

    print(f"\n=== Job Directory: {job_dir.name} ===")
    print(f"Benchmark: {btype}/{bname}")

    for kind in list(LOG_MAP.values()):
        if kind == JSON_LOG_KIND:
            continue
        print(f"\n  {kind}:")
        print(f"    Count: {stats[f"{kind}_count"]}")
        print(f"    Success: {stats[f"{kind}_success"]}")
        print(f"    Error: {stats[f"{kind}_error"]}")
        print(f"    Timeout: {stats[f"{kind}_timeout"]}")

        print(f"    Runtime stats:")
        print(f"      Mean:   {stats[f"{kind}_mean"]:.3f}s")
        print(f"      Min:    {stats[f"{kind}_min"]:.3f}s")
        print(f"      Q1:     {stats[f"{kind}_q1"]:.3f}s")
        print(f"      Median: {stats[f"{kind}_median"]:.3f}s")
        print(f"      Q3:     {stats[f"{kind}_q3"]:.3f}s")
        print(f"      Max:    {stats[f"{kind}_max"]:.3f}s")
            

    if stats["lambdapi_small_check_count"] > 0 or stats["lambdapi_large_check_count"] > 0 :
        print(f"\n  Lambdapi Checks Timing stats (ms):")
        print(f"      Weighted mean: {stats['weighted_mean_time']:.0f} ms")
        print(f"      Min:           {stats['min_lp']:.0f} ms")
        print(f"      Q1:            {stats['q1_lp']:.0f} ms")
        print(f"      Median:        {stats['median_lp']:.0f} ms")
        print(f"      Q3:            {stats['q3_lp']:.0f} ms")
        print(f"      Max:           {stats['max_lp']:.0f} ms")

# =====
# Main
# =====

def _csv_fieldnames() -> List[str]:
    stage_fields: List[str] = []
    for kind in LOG_MAP.values():
        stage_fields.extend([
            f"{kind}_count",
            f"{kind}_success",
            f"{kind}_error",
            f"{kind}_timeout",
            f"{kind}_mean",
            f"{kind}_min",
            f"{kind}_q1",
            f"{kind}_median",
            f"{kind}_q3",
            f"{kind}_max",
        ])
    return [
        "job_id",
        "benchmark_type",
        "benchmark_name",
        *stage_fields,
        "weighted_mean_time",
        "min_lp",
        "q1_lp",
        "median_lp",
        "q3_lp",
        "max_lp",
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description="Aggregate benchmark jobs and Lambdapi timings.")
    parser.add_argument("root", nargs="?", default=".", help="Root directory to scan (default: .)")
    parser.add_argument("--csv", type=str, help="Optional: write per-job CSV to this file")
    parser.add_argument("--skip-empty", action="store_true",
                        help="Skip jobs with no Lambdapi checks in CSV output and printing")
    args = parser.parse_args()

    root = Path(args.root).resolve()

    jobs: Dict[Path, List[Row]] = {}

    # Prepare CSV if requested
    csv_file = None
    csv_writer = None
    if args.csv:
        csv_file = open(args.csv, "w", newline="")
        csv_writer = csv.DictWriter(csv_file, fieldnames=_csv_fieldnames())
        csv_writer.writeheader()

    try:
        # Discover job directories
        for dirpath, _, _ in os.walk(root):
            dpath = Path(dirpath)
            job_id_file = dpath / "job_id.txt"
            logs_dir = dpath / "logs"
            if not job_id_file.exists() or not logs_dir.is_dir():
                continue

            job_id, benchmark_dir = parse_job_id_txt(job_id_file)
            btype, bname = infer_type_and_name(benchmark_dir)
            meta = MetaCommon(job_id=job_id, benchmark_type=btype, benchmark_name=bname, job_dir=dpath)

            rows: List[Row] = []

            # Parse text logs (seconds)
            for filename, kind in LOG_MAP.items():
                log_path = logs_dir / filename
                if log_path.exists():
                    parse_log_file(log_path, meta, rows)

            # Parse JSON (ms)
            collect_results(dpath, meta, rows)

            if rows:
                jobs[dpath] = rows

        # Stable order: by logic then benchmark name
        sorted_jobs = sorted(
            jobs.items(),
            key=lambda kv: (kv[1][0].benchmark_type, kv[1][0].benchmark_name)
        )

        # Output
        for job_dir, job_rows in sorted_jobs:
            stats, counts = collect_job_stats(job_dir, job_rows)

            if args.skip_empty and (stats["lambdapi_small_check_count"] > 0 or stats["lambdapi_small_check_count"] > 0):
                continue
            print_job_report(job_dir, job_rows, stats, counts)

            if csv_writer is not None:
                csv_writer.writerow(stats)

    finally:
        if csv_file is not None:
            csv_file.close()


if __name__ == "__main__":
    main()
