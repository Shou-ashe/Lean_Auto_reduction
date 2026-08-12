# ComplexityReduction Hardness Agent

Lean 4 complexity-reduction agent with kernel-checked NP-hardness proofs, typed reduction-gap
authoring, independent replay, endpoint equality checks, and a standard-axiom audit. Python plans,
model output, JSON reports, and benchmark oracles are observational; only checked Lean artifacts
establish hardness.

## Configuration

Copy `.env.example` to `.env` and provide `DEEPSEEK_API_KEY`:

```text
DEEPSEEK_BASE_URL=https://api.deepseek.com
DEEPSEEK_API_KEY=your-key
DEEPSEEK_MODEL=deepseek-v4-flash
DEEPSEEK_TIMEOUT_SECONDS=300
DEEPSEEK_MAX_TOKENS=64000
DEEPSEEK_MAX_RETRIES=0
DEEPSEEK_REASONING_EFFORT=low
```

Formal production precedence is explicit CLI option, then environment/`.env`, then these accepted
defaults. Reports redact the API key.

## Prove one NP-hardness goal

`prove_np_hard.py` handles one existing Lean `PresentedProblem`; it is not a benchmark runner.

```bash
python3 scripts/prove_np_hard.py \
  --problem ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem
```

The command discovers the input module, resolves an existing route or a typed authoring DAG,
checks the exact canonical endpoint, independently replays the artifact, and audits axioms. It
returns a stable public status such as `VERIFIED`, `BLOCKED_NOT_TARGET`,
`BLOCKED_MISSING_PREREQUISITE`, `FAILED_MODEL`, `FAILED_LEAN`, or `INPUT_ERROR`.

## Run benchmarks

The repository has exactly one benchmark runner:

```text
scripts/run_hardness_benchmark.py
```

It directly imports library APIs and never starts another Python runner. The frozen benchmark is
the complete 78-case inventory under `Benchmark/Hardness/Suites`:

- 32 capability cases;
- 2 unscored frontier cases;
- 24 exact-reduction-edge cases;
- 20 Boolean-CSP cases.

Validate and list all cases without Lean or API calls:

```bash
python3 scripts/run_hardness_benchmark.py --list
```

Run and score all 78 cases:

```bash
python3 scripts/run_hardness_benchmark.py \
  --output-root .reduction-agent/benchmark-full \
  --jobs 4
```

Run selected lanes by repeating `--lane`:

```bash
python3 scripts/run_hardness_benchmark.py \
  --lane boolean_csp \
  --output-root .reduction-agent/benchmark-boolean-csp \
  --jobs 4
```

Valid lanes are `capability`, `frontier`, `exact_edge`, and `boolean_csp`. The runner keeps public
suite execution separate from scorer-only oracle access; each oracle is opened only after its
selected production cases finish.

See [Benchmark/Hardness/README.md](Benchmark/Hardness/README.md) for the registry, selection flags,
output layout, and scoring contract.

## Repository layout

- `Lean/Reference/ComplexityReduction`: trusted problem, reduction, certificate, and agent code.
- `Lean/Reference/Benchmark/Hardness/Inputs`: answer-free Lean benchmark inputs.
- `Benchmark/Hardness/Suites`: the public 78-case suites.
- `Evaluation`: isolated scorer/oracle material.
- `agent/hardness`: reusable runner, authoring, verification, and scoring libraries.
- `scripts/run_hardness_benchmark.py`: the only benchmark runner.
- `scripts/prove_np_hard.py`: single-problem proof CLI.

Repository structure is enforced by `tests/test_hardness_single_benchmark_runner.py`; adding a
second `run_*.py`, delegating to a Python script, or drifting from 78 unique suite cases fails CI.
