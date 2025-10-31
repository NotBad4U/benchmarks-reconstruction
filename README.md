# SMT Alethe proof-reconstruction benchmark — README

Overview
--------
This repository implements a multi-stage pipeline to generate, clean, elaborate and translate SMT proofs, then run Lambdapi checks / benchmarks and collect results.

Pipeline stages
- gen-proof.sh   : run cvc5 on SMT benchmarks and produce `.proof` files
- clean-proof.sh : remove empty proof files i.e. return `unsant` but do not provide the proof 
- elaborate.sh   : run `carcara check` + `carcara elaborate` to produce `.elab` (Alethe) files
- translate.sh   : translate `.elab` → `.lp` (Lambdapi); split outputs in `convert/small` and `convert/large` by size
- check-lp.sh    : run lambdapi checks / benchmarks (produces `run/results` and logs)
- jobs.py        : orchestrator that creates a job directory (UUID) under `output/` (by default), runs the above scripts and manages env injection
- utils / parsers: scripts to parse logs and aggregate results (results.py, parselogs.py, jobres.py)

The pipeline is modular: each stage (proof generation, cleaning, elaboration, translation, and Lambdapi checks) can be run independently, end to end, or in any subset you need. However, jobs.py serves as the orchestrator that ties these steps together—creating the job workspace, wiring environment variables, and invoking the shell scripts in order. It’s implemented in Python to make configuration straightforward (e.g., via config.env and command-line flags like --max-stage), so you can adjust timeouts, thresholds, and stopping points without touching the underlying scripts.

Stage map (for `--max-stage`)
- `0` → generate proofs only
- `1` → + elaborate
- `2` → + translate
- `3` → + Lambdapi check (full pipeline; default if `--max-stage` is omitted)

Required tools
- cvc5
- carcara
- lambdapi
- GNU parallel
- fd (fd-find)
- rg (ripgrep)
- hyperfine (used for benchnmark)
- Python 3 (for orchestrator and parsing utilities)
Notes:
- On some Linux distributions `fd` is packaged as `fd-find` and the binary is `fdfind`. Either install `fd` or create an `fd` wrapper/alias.
- All scripts assume the required binaries are on PATH. Use `check-setup.sh` to validate dependencies.

Installation (macOS / Homebrew example)
```bash
brew install cvc5 carcara lambdapi parallel fd ripgrep hyperfine
# if fd is fdfind on your system:
# ln -s "$(which fdfind)" /usr/local/bin/fd
```

Configuration
-------------
Edit `config.env` to tune timeouts and split thresholds. Example recommended content (exported so scripts can source it directly):
```bash
export CVC5_TIMEOUT=600
export CARCARA_CHECK_ELAB_TIMEOUT=60
export CARCARA_TRANSLATE_TIMEOUT=60
export LAMBDAPI_CHECK_TIMEOUT=60
export PROOF_SPLIT_LIMIT=1M   # fd size threshold (e.g. 1M, 500K)
export SEGMENT_SIZE=2000
```
How the env is consumed
- jobs.py contains a loader that reads `config.env` and injects values into `os.environ` so subprocesses inherit them.
- Shell scripts can `source` the same `config.env`. If `config.env` uses plain assignments, call:
  ```bash
  set -a
  source /path/to/config.env
  set +a
  ```
  to auto-export the variables.

Running the pipeline
--------------------
Recommended (orchestrated) — creates a job dir under `./output/<UUID>` and runs all stages:
```bash
# Full pipeline (default: --max-stage 3)
python3 run_benchmark.py --benchmark-dir /path/to/benchs --output-dir ./output

# Stop after proof generation
python3 run_benchmark.py --benchmark-dir /path/to/benchs --output-dir ./output --max-stage 0

# Stop after elaboration
python3 run_benchmark.py --benchmark-dir /path/to/benchs --output-dir ./output --max-stage 1

# Stop after translation
python3 run_benchmark.py --benchmark-dir /path/to/benchs --output-dir ./output --max-stage 2
```
Manual step-by-step
1. Create job dir and subdirs:
```bash
JOB_DIR=./output/$(uuidgen)
mkdir -p "$JOB_DIR"/{proofs,logs,run/alethe,run/convert/small,run/convert/large,run/results}
```
2. Generate proofs:
```bash
./gen-proof.sh /path/to/benchs "$JOB_DIR"
```
3. Clean proofs:
```bash
./clean-proof.sh "$JOB_DIR/proofs"
```
4. Elaborate:
```bash
./elaborate.sh "$JOB_DIR" /path/to/benchs
```
5. Translate:
```bash
./translate.sh "$JOB_DIR" /path/to/benchs
```
6. Run lambdapi checks / benchmarks:
```bash
./check-lp.sh "$JOB_DIR"
```
7. Parse results:
```bash
python3 results.py
python3 parselogs.py
```

Behavior notes and tips
- PROOF_SPLIT_LIMIT is passed to `fd --size` (e.g. `--size -1M` for files smaller than 1 MiB). Set PROOF_SPLIT_LIMIT in `config.env`.
- GNU parallel `--timeout` expects a plain number (seconds) or a percentage, do not append `s`.
- Scripts use `fd` + `parallel` with null-separated output to safely handle whitespace in filenames.
- jobs.py will load `config.env` into the Python environment so scripts launched via jobs.py inherit the variables.
- Logs are written to `<job_dir>/logs` (cvc5, elaborate, translate, lambdapi checks).
- Outputs:
  - proofs → `<job_dir>/proofs`
  - alethe elab → `<job_dir>/run/alethe`
  - converted lambdapi → `<job_dir>/run/convert/{small,large}`
  - results → `<job_dir>/run/results`

Troubleshooting
---------------
- Missing tools: run `./check-setup.sh` or install missing packages.
- If `fd` is named `fdfind` on your system: create a shim `ln -s "$(which fdfind)" /usr/local/bin/fd` or modify scripts to call `fdfind`.
- If parallel complains about `--timeout`, provide an integer (e.g. `--timeout 60`).

License & contact
-----------------
See repository root for license. For issues or questions, open an issue in the repo.

```# filepath: /Users/alessiocoltellacci/Projects/benchmarks/README.md
# SMT Alethe proof-reconstruction benchmark — README

Overview
--------
This repository implements a multi-stage pipeline to generate, clean, elaborate and translate SMT proofs, then run Lambdapi checks / benchmarks and collect results.

Pipeline stages
- gen-proof.sh   : run cvc5 on SMT benchmarks and produce `.proof` files
- clean-proof.sh : remove empty / trivial proof files
- elaborate.sh   : run `carcara check` + `carcara elaborate` to produce `.elab` (Alethe) files
- translate.sh   : translate `.elab` → `.lp` (Lambdapi); split outputs in `convert/small` and `convert/large` by size
- check-lp.sh    : run lambdapi checks / benchmarks (produces `run/results` and logs)
- jobs.py        : orchestrator that creates a job directory (UUID) under `output/`, runs the above scripts and manages env injection
- utils / parsers: scripts to parse logs and aggregate results (results.py, parselogs.py, jobres.py)

Required tools
- cvc5
- carcara
- lambdapi
- GNU parallel
- fd (fd-find)
- rg (ripgrep)
- hyperfine (optional — used for timing Lambdapi)
- Python 3 (for orchestrator and parsing utilities)
Notes:
- On some Linux distributions `fd` is packaged as `fd-find` and the binary is `fdfind`. Either install `fd` or create an `fd` wrapper/alias.
- All scripts assume the required binaries are on PATH. Use `check-setup.sh` to validate dependencies.

Installation (macOS / Homebrew example)
```bash
brew install cvc5 carcara lambdapi parallel fd ripgrep hyperfine
# if fd is fdfind on your system:
# ln -s "$(which fdfind)" /usr/local/bin/fd
```

Configuration
-------------
Edit `config.env` (or `timeout.env`) to tune timeouts and split thresholds. Example recommended content (exported so scripts can source it directly):
```bash
export CVC5_TIMEOUT=600
export CARCARA_CHECK_ELAB_TIMEOUT=60
export CARCARA_TRANSLATE_TIMEOUT=60
export LAMBDAPI_CHECK_TIMEOUT=60
export PROOF_SPLIT_LIMIT=1M   # fd size threshold (e.g. 1M, 500K)
export SEGMENT_SIZE=2000
```
How the env is consumed
- jobs.py contains a loader that reads `config.env` and injects values into `os.environ` so subprocesses inherit them.
- Shell scripts can `source` the same `config.env`. If `config.env` uses plain assignments, call:
  ```bash
  set -a
  source /path/to/config.env
  set +a
  ```
  to auto-export the variables.

Running the pipeline
--------------------
Recommended (orchestrated) — creates a job dir under `./output/<UUID>` and runs all stages:
```bash
python3 jobs.py --benchmark-dir /path/to/benchs --output-dir ./output
```
In the idea, the pipeline is the following:
1. Create job dir and subdirs:
```bash
JOB_DIR=./output/$(uuidgen)
mkdir -p "$JOB_DIR"/{proofs,logs,run/alethe,run/convert/small,run/convert/large,run/results}
```
2. Generate proofs:
```bash
./gen-proof.sh /path/to/benchs "$JOB_DIR"
```
3. Clean proofs:
```bash
./clean-proof.sh "$JOB_DIR/proofs"
```
4. Elaborate:
```bash
./elaborate.sh "$JOB_DIR" /path/to/benchs
```
5. Translate:
```bash
./translate.sh "$JOB_DIR" /path/to/benchs
```
6. Run lambdapi checks / benchmarks:
```bash
./check-lp.sh "$JOB_DIR"
```
7. Parse results:
```bash
python3 results.py
python3 parselogs.py
```

Behavior notes and tips
- PROOF_SPLIT_LIMIT is passed to `fd --size` (e.g. `--size -1M` for files smaller than 1 MiB). Set PROOF_SPLIT_LIMIT in `config.env`.
- GNU parallel `--timeout` expects a plain number (seconds) or a percentage, do not append `s`.
- Scripts use `fd` + `parallel` with null-separated output to safely handle whitespace in filenames.
- jobs.py will load `config.env` into the Python environment so scripts launched via jobs.py inherit the variables.
- Logs are written to `<job_dir>/logs` (cvc5, elaborate, translate, lambdapi checks).
- Outputs:
  - proofs → `<job_dir>/proofs`
  - alethe elab → `<job_dir>/run/alethe`
  - converted lambdapi → `<job_dir>/run/convert/{small,large}`
  - results → `<job_dir>/run/results`

Troubleshooting
---------------
- Missing tools: run `./check-setup.sh` or install missing packages.
- If `fd` is named `fdfind` on your system: create a shim `ln -s "$(which fdfind)" /usr/local/bin/fd` or modify scripts to call `fdfind`.
- If parallel complains about `--timeout`, provide an integer (e.g. `--timeout 60`).
