# SMT Alethe proof-reconstruction benchmark

Generates SMT proofs with cvc5, elaborates and translates them to Lambdapi with
carcara, checks them with Lambdapi, and records timings and outcomes.

```
benchs/<LOGIC>/<BENCH>/x.smt2
   │
   ├─► cvc5 ─────────────► proofs/x.proof
   │                          │
   ├─► carcara elaborate ◄────┘ ──► run/alethe/x.elab
   │                                   │
   └─► carcara translate ◄─────────────┘ ──► run/convert/{small,large}/x.lp
                                                │
                              hyperfine → lambdapi check ──► run/results/x.json
```

The problem file feeds stages 1 and 2 as well as stage 0, which is why this is a
task graph and not a shell pipe.

## Files

| file | role |
|---|---|
| `dodo.py` | the pipeline, as a [doit](https://pydoit.org) task graph |
| `config.env` | timeouts, split threshold, hyperfine run counts |
| `collects.py` | aggregates a job directory into per-stage stats and CSV |
| `download_benchs.sh` | fetches SMT-LIB sets (QF_UF and UF by default), drops sat/unknown |
| `lambdapi.pkg` | package file placed next to generated proofs so lambdapi accepts them |
| `slurm/` | jobs for the ITU HPC cluster — see [`slurm/README.md`](slurm/README.md) |

## Run locally

```bash
python3 -m venv .venv
```

```bash
./.venv/bin/pip install -r requirements.txt
```

You also need `cvc5`, `carcara` (`NotBad4U/carcara`, branch
`lambdapi-refactor`) and `hyperfine` on `PATH`, plus `lambdapi` with two
libraries installed, in this order:

1. `Stdlib` — `make install` in `NotBad4U/lambdapi-stdlib`
2. `alethe` — `make install` in carcara's `alethe-lp/`

**Load opam's environment first** (`eval "$(opam env)"`), both for the
installs and for every run. lambdapi finds its library root through
`OPAM_SWITCH_PREFIX`; without it, it looks in `/usr/local/lib/lambdapi/lib_root`
and every check fails with `alethe/core.lp … not found`.

```bash
./download_benchs.sh
```

```bash
BENCH_DIR=benchs/QF_UF JOB_DIR=output/run PROOF_GRANULARITY=theory-rewrite ./.venv/bin/doit -n 8 --parallel-type thread
```

`JOB_DIR` must stay the same between invocations: that is what lets a rerun
resume instead of starting over.

To iterate quickly, skip the large proofs, which dominate the run time:

```bash
SKIP_LARGE=1 ./.venv/bin/doit -n 8 --parallel-type thread
```

Proofs over `PROOF_SPLIT_LIMIT` (1 MB) are then neither translated nor checked,
and the run prints how many it skipped. Cvc5 and elaboration still run on
everything, since a proof's size is only known after elaboration. Rerun the
same `JOB_DIR` without the flag to do the large ones later: the small ones are
already up to date.

### Viewing the results in a browser

```bash
./.venv/bin/doit report
```

```bash
open output/run/report/results.table.html
```

That is BenchExec's table-generator: one row per benchmark, one column group
per stage, sortable and filterable, with quantile ("cactus") and scatter plots.
Statuses read `done`, `TIMEOUT`, or `ERROR (<exit code>)` — a carcara panic
shows as `ERROR (101)`. For the check stage, the time shown is hyperfine's
mean per run, not the whole warmup-and-repeat sequence. The page is a single
self-contained file, so you can copy it anywhere. `doit report` only reads the
status records, so it is safe to run while you iterate.

### Rerunning after fixing something

doit decides what to rerun from **files only**. Installing a Lambdapi
library, fixing a tool flag or changing a timeout touches no file it tracks,
and a failed tool still writes a valid record — so a plain rerun does nothing,
and the failures stay failures. Name the stages to retry instead:

```bash
RETRY_FAILED=translate,check ./.venv/bin/doit -n 8 --parallel-type thread
```

Tasks in those stages whose last record is not a success run again; everything
that succeeded is skipped. Stages are `gen_proof`, `elaborate`, `translate`,
`check`, or `all`. Retrying `gen_proof` or `elaborate` only helps if you changed
something, such as a timeout — otherwise the same failures come back.

That one command runs every stage. Stages 0–2 use all `-n` workers; the timed
`lambdapi check`s always run one at a time, serialised by a lock inside
`dodo.py`, so `-n` never puts the reported timings under load.

```bash
./.venv/bin/python collects.py output/run --csv summary.csv
```

## Output

Every task writes `status/<stage>/<stem>.json` — exit code, signal, runtime and,
for elaboration, whether the proof still contains holes. That record is the
doit target, so a tool that fails (timeout, no proof) records the failure
instead of aborting the run. `logs/*.txt` repeats the records in GNU parallel
joblog format, which is what `collects.py` reads.

## Known issues

- **`PROOF_GRANULARITY=dsl-rewrite`** (the `config.env` default) makes cvc5
  emit `rare_rewrite` steps that carcara can only check given a RARE database
  via `--rare-file`, which is not shipped. Every elaboration then fails. Use
  `theory-rewrite` until that is resolved.
- **Every elaborated proof is `holey`.** `-i` turns unknown rules into holes and
  `translate --admit-unsupported` turns unsupported ones into `admit`, so a
  passing `lambdapi check` does not by itself mean the proof is complete.
- **carcara 1.1 no longer segments large proofs** (`-n`/`-o` are gone). Large
  proofs are one `.lp` checked directly; the small/large split is now only a
  reporting distinction.
- `*.smt` files (TLAPS/Allocator) are not picked up; only `*.smt2` is globbed.
