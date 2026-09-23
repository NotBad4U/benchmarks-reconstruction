# Running the benchmark on the ITU HPC cluster

Two jobs: `setup.job` builds the toolchain and downloads the benchmarks (run it
once), `benchmark.job` runs the pipeline and copies the results into `$HOME`.

> **These scripts have never been executed.** They were written against the ITU
> documentation, not against the cluster. Expect to fix at least the module
> names. Run the smoke test below before the real thing.

## 0. Get the repository onto the cluster

You need to be on eduroam, ITU++ or the ITU VPN.

```bash
ssh alecol@hpc.itu.dk
```

Then, on the cluster:

```bash
git clone git@github.com:NotBad4U/benchmarks-reconstruction.git && cd benchmarks-reconstruction
```

Create the tmp directory the ITU docs ask for, once:

```bash
mkdir -p ~/tmp
```

## 1. Build the toolchain (once, ~1 hour)

```bash
sbatch slurm/setup.job
```

This runs on `scavenge` (low priority, all nodes) because it is a build, not a
measurement, and because the ITU docs warn that running this kind of work on
the login node can get your account restricted.

It installs into `$HOME/bench-toolchain`:

| component | how | why |
|---|---|---|
| cvc5 1.4.0 | upstream static Linux binary | **not on conda-forge** — I checked, the package does not exist. No cvc5 module either. The static build needs no compiler and no shared libraries. |
| carcara | `cargo install --git … --branch lambdapi-refactor` | needs a private rustup: `Cargo.toml` declares `edition 2024` / `rust-version 1.93`, newer than most site Rust modules |
| OCaml 5.2 + lambdapi | private opam switch, `opam pin` on `deducteam/lambdapi` master | opam is not installed on the cluster, so the job fetches the opam binary itself |
| lambdapi-stdlib | `make install` from `NotBad4U/lambdapi-stdlib` | provides `alethe.core` — without it every `lambdapi check` fails |
| QF_UF + UF | `download_benchs.sh` | now the default set (it used to fetch all five) |

`opam init` is run with **`--disable-sandboxing`**. opam's sandbox uses
bubblewrap and user namespaces, which are restricted on most HPC nodes; without
that flag every package build fails.

## 2. Smoke test before committing 2 days of wall time

```bash
sbatch --time=00:30:00 --cpus-per-task=8 --partition=scavenge slurm/benchmark.job QF_UF/eq_diamond
```

That is 100 benchmarks and takes about a minute of compute once it starts. If
it produces `~/benchmark-results/<jobid>/summary.txt`, the pipeline works.

## 3. The real run

```bash
sbatch slurm/benchmark.job
```

Defaults: `--partition=cores,cores_any`, 32 cores, 64 GB, 2 days, QF_UF + UF.
One logic only:

```bash
sbatch slurm/benchmark.job QF_UF
```

The ITU docs say explicitly that a CPU-only job should request **both** `cores`
and `cores_any` — `cores_any` is spare cores on the GPU nodes, so asking for
both roughly doubles the set of nodes that can start you.

Stages 0–2 run on all cores; **stage 3 runs serially on purpose**, because
hyperfine times it and a timing taken while 31 sibling checks fight for the
same cores is not worth reporting.

## 4. Watch it

```bash
squeue -u $USER
```

```bash
tail -f proof-bench-<jobid>.out
```

`squeue --start -u $USER` estimates when a pending job will start, and
`sacct -j <jobid> --format=JobID,State,Elapsed,MaxRSS,ReqMem` shows what it
actually used — worth checking `MaxRSS` before asking for more memory.

## 5. Results

Written to `$HOME/benchmark-results/<jobid>/`, plus a `.tar.gz` beside it:

```
status/       one JSON record per (stage, benchmark)
logs/         GNU-parallel-format joblogs, for collects.py
run/results/  hyperfine JSON per checked proof
summary.txt   collects.py output
summary.csv   same, machine readable
run-info.txt  node, partition, tool versions, granularity
```

The bulk — `proofs/`, `run/alethe/`, `run/convert/` — stays on node-local
scratch and is deleted. It is tens of GB and fully reproducible. The job works
on scratch rather than `$HOME` because the ITU docs note the home filesystem
has no infiniband link, and this pipeline writes tens of thousands of small
files.

## Can we get a bigger machine?

From the ITU docs:

| partition | nodes | wall time |
|---|---|---|
| `cores` | cn[8,14-15] | 3 days (students) / **7 days (researchers)** |
| `cores_any` | cn[3-4,6-7,12,16-18] | 3 / 7 days |
| `acltr` | cn[3-7,12-13,18] | 3 / 7 days — GPU nodes, irrelevant here |
| `scavenge` | all nodes | 1 day, low priority |
| `dgpu` | desktop[1-9] | 10 days |

**The docs do not publish per-node core counts or RAM**, so I could not size the
job from them. Check on the cluster:

```bash
sinfo -o "%20P %8D %6c %10m %N"
```

`%c` is cores per node and `%m` is memory in MB. Raise `--cpus-per-task` and
`--mem` in `benchmark.job` to match the largest node you can actually get; this
pipeline is embarrassingly parallel, so cores translate almost linearly into
throughput for stages 0–2.

Other levers, in order of effort:

- **You are a researcher, so you get 7 days**, not 3. `--time=7-00:00:00` on
  `cores`/`cores_any` if the full run does not fit in 2 days.
- Students have per-queue CPU-minute caps; researchers should not, but if a job
  sits pending forever, that is the first thing to check. Email `hpc@itu.dk`
  cc'ing your supervisor to have limits raised.
- You can request a **temporary dedicated partition** for a deadline.
- There is no limit on the number of simultaneous jobs, so splitting QF_UF and
  UF into two submissions will usually finish sooner than one big job.
- ITU has access to **external HPC resources** for workloads that need more than
  the internal cluster — `hpc-frontoffice@itu.dk`.

## Things most likely to break

1. **`module load Python/3.12.3-GCCcore-13.3.0`** — taken from your scraper job.
   If it fails, `module spider Python`.
2. **`/scratch` may not exist**, or not be writable. The job falls back to
   `$TMPDIR` then `/tmp/$USER`, and prints which it picked.
3. **`opam switch create 5.2.0`** builds OCaml from source, ~15 minutes. If
   lambdapi master requires a different compiler, set `OCAML_VERSION`.
4. **`make install` in lambdapi-stdlib** must land inside the opam switch's
   `lib_root`. If `lambdapi check` still reports `alethe/core.lp not found`,
   that step put the files somewhere else.
5. **`PROOF_GRANULARITY`** is forced to `theory-rewrite`. With cvc5's
   `dsl-rewrite` (the `config.env` default) carcara needs a RARE database via
   `--rare-file`, which is not shipped — every elaboration fails. If you get a
   RARE file, set `PROOF_GRANULARITY=dsl-rewrite` and pass it through.
