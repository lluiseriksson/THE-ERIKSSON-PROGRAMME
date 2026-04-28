# GEMMA4_MATH_DISCOVERY.md

## Purpose

Gemma4/Ollama is a local sidecar for mathematical discovery support. It is not
a proof authority, not an auditor, and not a source of unconditional claims.

Its job is to generate candidate definitions, proof decompositions, obstruction
maps, counterexample searches, and Codex-ready task proposals for the
Yang-Mills programme.

## Current status

- Runtime: local Ollama
- Preferred model: `gemma4:e2b`
- Canonical runner: `scripts/gemma4_math_discovery.py`
- Latest output: `dashboard/gemma4_math_discovery_latest.md`
- Run log: `registry/gemma4_discovery_runs.jsonl`
- State: `registry/gemma4_state.json`

## Honesty rules

Gemma output must always be treated as one of:

- HEURISTIC: an idea or strategy with no formal standing
- FORMALIZATION_TARGET: a theorem/definition/task that Codex may attempt
- COUNTEREXAMPLE_SEARCH: an explicit attempt to break an idea
- AUDIT_PROMPT: a request for Cowork to inspect a claim
- INVALID: an idea that conflicts with known project evidence

Gemma must never:

- claim the Clay problem is solved;
- upgrade a ledger row;
- move a percentage;
- introduce a hidden axiom;
- treat a plausible proof sketch as formal evidence.

## Discovery loop

1. Read the current ledger, planner, and frontier documents.
2. Identify the smallest live mathematical blocker.
3. Generate 3-5 candidate ideas.
4. For every idea, require:
   - exact target statement;
   - dependency on existing project identifiers;
   - falsification test;
   - Lean formalization route;
   - Cowork audit question.
5. Codex converts only the best candidate into a task.
6. Cowork audits before any status movement.

## Training plan

No weight training has been performed yet. The first stage is data collection:
Gemma runs are logged with prompts, context manifests, and outputs. After enough
audited runs exist, Codex may build a supervised dataset of:

- useful hypothesis -> accepted task;
- weak hypothesis -> rejection reason;
- invalid hypothesis -> counterexample/audit failure;
- formal target -> Lean outcome.

The initial evaluation/training dataset lives at:

- `registry/gemma4_training_examples.jsonl`

Each JSONL row is a labelled example with:

- `classification`: `useful`, `weak`, or `invalid`;
- `authority`: always `HEURISTIC_ONLY`;
- `overclaim_risk`: `low`, `medium`, or `high`;
- `missing_falsification_tests`: boolean;
- `codex_ready_task_quality`: `none`, `partial`, `high`, or `invalid`;
- `proof_authority`: always `none`;
- `ledger_status_change_allowed`: always `false`;
- `percentage_change_allowed`: always `false`.

Current use is prompt/evaluation training only:

1. Use `weak` examples to tighten required headings and reject generic output.
2. Use `invalid` examples as hard guardrails against proof-authority or
   percentage/ledger overclaim.
3. Use `useful` examples as target shape for future heuristic discovery runs.

Fine-tuning or adapter training may only be considered after:

1. the dataset has substantially more audited examples;
2. Cowork audits the schema and labels;
3. Codex records an explicit training plan that keeps Gemma outputs
   `HEURISTIC_ONLY`;
4. the plan states that model weights do not create proof authority, ledger
   authority, or percentage authority.

No model-weight training has been performed or claimed.
