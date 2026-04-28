# Continuous Improvement Playbook

Purpose: keep Codex and Cowork improving the system every run while preserving mathematical honesty.

## Daily lanes

- `formal_math`: Lean/formal theorem work that reduces a named mathematical blocker.
- `creative_research`: Cowork/strategy work inventing non-circular mathematical routes.
- `audit_honesty`: Ledger, horizon, progress, and claim-safety auditing.
- `automation_infra`: Watcher, dispatcher, registry, and queue reliability work.
- `planning_metrics`: Roadmap, metrics, milestones, dependencies, and time planning.

## Role rotation

- `Codex-Implementer` (Codex): Land Lean interfaces/proofs or infrastructure patches with validation.
- `Cowork-CreativeResearch` (Cowork): Invent candidate invariants, theorem statements, and non-circular proof routes.
- `Cowork-Auditor` (Cowork): Attack claims, check ledgers, and block fake percentage/status movement.
- `Codex-Infrastructure` (Codex): Improve watcher, dispatcher, validation, and registry automation.
- `Planner` (Codex/Cowork): Turn blockers into dated, lane-balanced tasks.

## Guardrails

- Never move `F3-COUNT` above `CONDITIONAL_BRIDGE` without complete Lean evidence and Cowork audit.
- Never convert creative research into a proof claim without a no-sorry Lean artifact.
- Every overnight run should have at least 3 concrete READY Codex tasks and one READY Cowork task.
- Every week should include at least one formalization task, one creative research task, one audit task, one automation task, and one planning/metrics task.

## Ready-floor routine

- Treat fewer than 3 Codex READY tasks as a warning even when lane coverage is otherwise green.
- Use `recommended_seed_tasks` from `dashboard/continuous_improvement_status.json` as the deterministic seed list.
- Refresh `SEED_TASK_TEMPLATES` whenever preflight can name fewer than three unused Codex seed suggestions.
- Seed tasks only through an explicit registry update/META task, never as a hidden preflight mutation.
- Keep Cowork polling gates intact; fill Cowork idle time with non-polling creative research or landed-substrate audits.
