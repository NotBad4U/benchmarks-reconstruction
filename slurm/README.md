# Running the benchmark on the ITU HPC cluster

Two jobs: `setup.job` builds the toolchain and downloads the benchmarks (run it
once), `benchmark.job` runs the pipeline and copies the results into `$HOME`.

> **Partially executed.** Job 130513 got through cvc5 and rustup and then died
> building carcara's GMP dependency for want of `m4`. Everything from the opam
> switch onwards is still unverified. Run the smoke test below before the real
> thing, and `slurm/check-deps.sh` before either.

## 0. Get the repository onto the cluster

You need to be on eduroam, ITU++ or the ITU VPN.

```bash
ssh alecol@hpc.itu.dk
```

Then, on the cluster:

```bash
git clone -b v2 https://github.com/NotBad4U/benchmarks-reconstruction.git && cd benchmarks-reconstruction
```

Two details that matter:

- **`-b v2`**: without it you get `main`, which has none of this pipeline.
- **HTTPS, not `git@github.com:`**: your GitHub SSH key lives on your laptop,
  not on the cluster, so an SSH clone fails there. The repo is public, so
  HTTPS needs no credentials.

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
| cvc5 1.4.0 | upstream static Linux binary | **not on conda-forge** (the package does not exist), and confirmed on the cluster: `module spider cvc5` finds nothing and it is not on `PATH`. The static build needs no compiler and no shared libraries. |
| carcara | cloned at `lambdapi-refactor`, `cargo install --path` | needs a private rustup: `Cargo.toml` declares `edition 2024` / `rust-version 1.93`, newer than most site Rust modules |
| OCaml 5.2 + lambdapi | private opam switch, `opam pin` on `deducteam/lambdapi` master | opam is not installed on the cluster, so the job fetches the opam binary itself |
| lambdapi-stdlib | `make install` from `NotBad4U/lambdapi-stdlib` | provides `Stdlib`, which `alethe-lp` requires |
| Alethe library | `make install` in carcara's `alethe-lp/` | provides `alethe.core` etc. — without it every `lambdapi check` fails. The job then checks that `alethe.core` resolves and stops if not |
| hyperfine | `cargo install hyperfine` | times stage 3; not on the cluster, and cargo is already there for carcara |
| QF_UF + UF | `download_benchs.sh` | now the default set (it used to fetch all five) |

### What the host has to provide

`setup.job` compiles carcara, OCaml and lambdapi from source, so it needs more
of the host than the ITU docs list. `slurm/check-deps.sh` reports what a given
host actually has — binaries, a real compile-and-link test per dev library, and
the modules that could supply anything missing:

```bash
srun -p scavenge --time=00:05:00 --mem=2G bash -lc 'bash slurm/check-deps.sh'
```

Run it **on a compute node**, not on the login node. They are not the same host,
and that difference is what killed the first run: `m4` sits at `/usr/bin/m4` on
`slurmhead`, yet GMP's configure could not find one on the node it landed on.
`bash -lc` is needed for the `module` function to exist.

| need | pulled in by | where it comes from |
|---|---|---|
| cc, c++, make, ar, ranlib | everything built from source | on the nodes |
| `m4` | carcara → rug → gmp-mpfr-sys, which builds GMP | `module load M4`, else built into `$PREFIX` |
| libgmp + headers | lambdapi → why3 → zarith | built into `$PREFIX`; no header on the nodes |
| libev + headers | lambdapi → dream → conf-libev | built into `$PREFIX`; **no libev module exists** — the cluster's `libevent` is a different library and conf-libev links `-lev` and accepts nothing else |
| OpenSSL headers | lambdapi → dream → ssl/lwt_ssl | present on the host (`OpenSSL/3` module too) |
| zlib | camlzip, if the chain pulls it | present |
| unzip, tar, xz, bzip2, patch, rsync, pkg-config | cvc5 release, opam | present |

GMP and libev go into `$PREFIX`, not a module, because `$PREFIX` is under `$HOME`
and every node mounts it: `benchmark.job` runs on `cores`/`cores_any` while
`setup.job` builds on `scavenge`, and a module loaded during the build would not
follow. `env.sh` therefore exports `C_INCLUDE_PATH`, `LIBRARY_PATH`,
`LD_LIBRARY_PATH` and `PKG_CONFIG_PATH` pointing there — the first two are
literally what conf-libev's `discover.ml` probes.

`fd` and GNU parallel are **not** needed, despite comments all over the pipeline
naming them: `dodo.py` reimplements both, and `download_benchs.sh` falls back to
`find`.

`opam init` is run with **`--disable-sandboxing`**. opam's sandbox uses
bubblewrap and user namespaces, which are restricted on most HPC nodes; without
that flag every package build fails.

## 2. Smoke test before committing 2 days of wall time

```bash
sbatch --time=00:30:00 --cpus-per-task=8 --mem=16G --partition=scavenge slurm/benchmark.job QF_UF/eq_diamond
```

`--mem=16G` is not optional here: the script defaults to 64 GB, but the
smallest `scavenge` nodes have only ~30 GB, so without the override the job
would sit pending forever waiting for a node that can satisfy it.

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

Small proofs only, skipping everything over `PROOF_SPLIT_LIMIT` at the
translate and check stages:

```bash
sbatch --export=ALL,SKIP_LARGE=1 slurm/benchmark.job
```

`--export=ALL,` keeps the rest of your environment; `--export=SKIP_LARGE=1`
alone would pass *only* that variable. The setting is recorded in the run's
`run-info.txt`.

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

Measured on the cluster with `sinfo` (the published docs are out of date — they
list `cores` as cn[8,14-15], but it is actually six nodes):

| partition | nodes | cores | memory | node list |
|---|---|---|---|---|
| `cores` | 6 | **40+** | 120 GB+ | cn[8,14-18] |
| `cores_any` | 9 | 32+ | **190 GB+** | cn[3-7,12,16-18] |
| `acltr` | 10 | 32+ | 128 GB+ | cn[3-7,12-13,16-18] |
| `scavenge` | 23 | 8+ | 30 GB+ | cn[3-19], desktop[1,6-8,12,15] |
| `dgx1` / `asus1` | 1 each | 20 | 115 GB | — |

`+` is a minimum: the partition contains nodes with at least that much.

**The job asks for 32 cores and 64 GB on purpose.** 32 is the largest request
that still fits every node in *both* `cores` and `cores_any`; asking for 40
would fit `cores` but exclude the nine `cores_any` nodes, so you would wait
longer for 25% more cores. On a two-day job that is a bad trade. If the queue
is empty and you want the bigger nodes:

```bash
sbatch --cpus-per-task=40 --partition=cores slurm/benchmark.job
```

Memory is not the constraint — every node in both partitions has 120 GB+, and
64 GB across 32 concurrent tasks is 2 GB each, well beyond what cvc5 and
carcara need on these benchmarks. Raise it only if a run reports OOM.

To see individual nodes rather than partition minima:

```bash
sinfo -N -o "%N %c %m" | sort -u
```

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

1. ~~`module load Python/3.12.3-GCCcore-13.3.0`~~ — confirmed present on the
   cluster. (3.13.1 is also available if you want it.)
2. **`/scratch` may not exist**, or not be writable. The job falls back to
   `$TMPDIR` then `/tmp/$USER`, and prints which it picked.
3. **`opam switch create 5.2.0`** builds OCaml from source, ~15 minutes. If
   lambdapi master requires a different compiler, set `OCAML_VERSION`.
4. **The Lambdapi libraries must land where lambdapi looks.** It finds its
   library root through `OPAM_SWITCH_PREFIX`; without that it falls back to
   `/usr/local/lib/lambdapi/lib_root` and finds nothing, not even `Stdlib`.
   `setup.job` now fails loudly if `alethe.core` does not resolve.
5. ~~**`m4` is absent on the compute nodes**~~ — hit for real: carcara depends
   on `rug` -> `gmp-mpfr-sys`, which builds GMP from source, and GMP's
   `configure` dies with `No usable m4 in $PATH`. `setup.job` now loads an `M4`
   module if the cluster has one and otherwise builds m4 1.4.19 into
   `$PREFIX` before touching cargo.
6. **`why3` and `dream` are the unverified part.** lambdapi master depends on
   both, which is where libgmp and libev come from; nothing past the opam
   switch has run on the cluster yet. If `conf-libev` still fails, its error
   names the two variables it wants — check `env.sh` exported them.
7. **`PROOF_GRANULARITY`** is forced to `theory-rewrite`. With cvc5's
   `dsl-rewrite` (the `config.env` default) carcara needs a RARE database via
   `--rare-file`, which is not shipped — every elaboration fails. If you get a
   RARE file, set `PROOF_GRANULARITY=dsl-rewrite` and pass it through.
