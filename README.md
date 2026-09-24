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

`doit` is the only Python dependency. You also need `cvc5`, `carcara`
(`NotBad4U/carcara`, branch `lambdapi-refactor`), `lambdapi` with
`NotBad4U/lambdapi-stdlib` installed, and `hyperfine` on `PATH`.

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

To keep stage-3 timings clean, run the work in parallel and the measurement
serially:

```bash
BENCH_DIR=benchs/QF_UF JOB_DIR=output/run ./.venv/bin/doit -n 8 --parallel-type thread translate
```

```bash
BENCH_DIR=benchs/QF_UF JOB_DIR=output/run ./.venv/bin/doit -n 1 check
```

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
