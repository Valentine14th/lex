# GDPRSocial case study (WhyEnf / EnfFlash)

This folder contains the Django case study used for GDPR enforcement experiments.

## Installation

This case study supports exactly two setup options:

1. Local install
2. Docker

## Option 1: Local install

### 1) Build the enforcer executable first (required)

Use the `enfflash` branch of WhyEnf:

- Repository: https://github.com/runtime-enforcement/whyenf/tree/enfflash

Build it with the repository `Makefile` (builds both OCaml and Rust parts):

```bash
git clone -b enfflash https://github.com/runtime-enforcement/whyenf.git ~/Git/whyenf
cd ~/Git/whyenf
make build
```

After this, the executable should be available at:

```text
~/Git/whyenf/enfguard
```

### 2) Set up GDPRSocial

From this folder:

```bash
cd /home/franz/Git/Lex/evaluation/02_case_studies/GDPRSocial
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
python manage.py migrate
ln -sfn ~/Git/whyenf/enfguard ./enfguard
```

`requirements.txt` includes all Python dependencies used by the app (including `scikit-learn`).

For benchmarking, also install the benchmark-specific requirements:

```bash
pip install -r benchmark/privacy_testsuite/requirements.txt
```

### 3) Run

```bash
make clean
make run
```

App access:

- http://127.0.0.1:8000/
- Login page: http://127.0.0.1:8000/accounts/login/

Optional: replay monitor over current log in another terminal:

```bash
make replay
```

### 4) Run benchmark (local)

From this folder:

```bash
# Enforced benchmark (requires a built enfguard executable):
bash benchmark/privacy_testsuite/run_benchmark.sh gdpr ~/Git/whyenf/enfguard

# Un-instrumented baseline (no enforcer needed):
bash benchmark/privacy_testsuite/run_benchmark.sh baseline
```

This runs:

1. `prepare_databases.py` (snapshot preparation, skipped if already done)
2. `privacy_test.py` (benchmark execution)

Expected runtime is around 5–7 minutes per run.
Results are written under `output/minitwitter_<timestamp>/`.

The baseline measures raw app latency without enforcement overhead. Run
both to compare.

## Option 2: Docker

### 1) Build a separate WhyEnf EnfFlash image

From this folder:

```bash
docker build -f Dockerfile.enfflash -t whyenf-enfflash:latest .
```

### 2) Build this case-study image

From this folder (note the parent `..` build context):

```bash
docker build -f Dockerfile -t gdprsocial:latest ..
```

### 3) Run container

```bash
docker run --rm -it \
	-p 8000:8000 \
	gdprsocial:latest
```

App access:

- http://127.0.0.1:8000/
- Login page: http://127.0.0.1:8000/accounts/login/


## Parallel enforcement

To experiment with enforcing a policy split across multiple sub-formulas, use the
[policy splitting tool](LINK). It takes a monolithic `.mfotl` policy and produces a
folder of sub-formula files, each with a matching `.sig`, following this structure:

```
policies/
└── my_split/
    ├── formula_a.mfotl
    ├── formula_a.sig
    ├── formula_b.mfotl
    ├── formula_b.sig
    └── ...
```

Both recommended options below run via Docker Compose (requires the image to be built first — see Option 2 above).

**Single run** — pass the split folder as `--formula`; all `.mfotl` and `.sig` files are picked up automatically:

```bash
docker compose run --rm benchmark gdpr /opt/whyenf/enfguard \
  --instrlib /app/instrlib \
  --formula /app/policies/my_split/
```

**Sweep over multiple splits** — list the folders in `benchmark/run_all_splits.sh`
under `SPLITS` and run the script:

```bash
SPLITS=(
    my_split
    another_split
)
```

```bash
./benchmark/run_all_splits.sh
# or BUILD_ONCE=1 ./benchmark/run_all_splits.sh  to rebuild the image first
```

Results for each split are written to `output/<split-name>/` on the host.

## Notes

- For Docker, `enfguard` and `enfflash` are copied from the separate `whyenf-enfflash:latest` image.
- The compose file mounts the desired instrlib version onto `/app/instrlib` — benchmark commands always use that path. To switch version, update the mount in `docker-compose.yml`: `- ./instrlib_filter:/app/instrlib`.
- Outputs: measurements in `output/`, per-scenario server logs in `benchmark/privacy_testsuite/logs/multi_runs/`, and the raw event stream sent to the enforcer(s) in `GDPRSocial/log`. All can be parsed further, e.g. for transparency or fine-grained timing analysis.





