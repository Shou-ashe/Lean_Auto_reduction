# OneShotLLM comparison arm

This directory is parallel to `compare/Archon` and implements the direct LLM
control for the hardness benchmark.

For every case it uses the same formal model profile as the production agent
and Archon (`deepseek-v4-flash`, temperature `0`, reasoning effort `low`,
64,000 output tokens, 300-second timeout, zero retries). It makes exactly one
chat-completions request and offers no tools, Lean feedback, follow-up turn,
planner, prover loop, or reviewer.

The user request is constructed from the exact `USER_HINTS.md` and sole Lean
objective source rendered for the Archon black-box arm. Thus the task facts are
identical: public statement, formal Lean goal, and proof-kind requirement only.
Library sources, recommended proof bodies, oracles, typed DAGs, routes,
dependency proof bodies, and diagnostics are absent.

Run the frozen 78-case registry through the repository's only benchmark runner:

```bash
python3 scripts/run_hardness_benchmark.py \
  --agent oneshot-llm \
  --jobs 4 \
  --output-root .reduction-agent/benchmark-oneshot-llm \
  --env-file .env
```
