# Gemma4 Model Evaluation

Generated: 2026-04-26T15:26Z

## Status

Gemma4 is available locally through Ollama, but it is not yet a reliable
mathematical-discovery agent.

## Probe

- `ollama list` shows `gemma4:e2b` and `gemma4:latest`.
- `python scripts\gemma4_math_discovery.py probe` returned
  `GEMMA4_SIDEcar_READY`.

## Discovery Runs

| Model | Focus | Assessment | Result |
|---|---|---|---|
| `gemma4:e2b` | B.2 decoder | WEAK_OUTPUT | Too generic; did not follow required headings |
| `gemma4:latest` | B.2 decoder | PARTIAL / WEAK_OUTPUT | Produced plausible candidate ideas with falsification tests, but omitted required final sections |

## Current Recommendation

- Use `gemma4:latest` for mathematical-discovery passes despite slower runtime.
- Keep `gemma4:e2b` for cheap probes/status only.
- Treat every output as HEURISTIC_ONLY.
- Build a small training/evaluation dataset before any fine-tuning attempt.

## Next Engineering Step

Create `registry/gemma4_training_examples.jsonl` with accepted, rejected, and
invalid examples from Gemma outputs. Use those examples to improve prompts first;
only consider adapter training after Cowork audits the dataset schema.
