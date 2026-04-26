# UNCONDITIONALITY_LEDGER.md

This ledger tracks every assumption, bridge, axiom, placeholder, conditional
theorem, experimental result, and unresolved blocker.

## Global Clay status

Status:
- NOT_ESTABLISHED

Reason:
- The repository does not yet contain a complete unconditional formal proof of
  the Clay Yang-Mills Mass Gap problem.

## Status labels

- FORMAL_KERNEL: verified by Lean without project-specific assumptions
- MATHLIB_FOUNDATIONAL: depends only on accepted Lean/Mathlib foundations
- CONDITIONAL_BRIDGE: depends on an explicitly stated unproved mathematical bridge
- EXPERIMENTAL: exploratory and not part of the proof chain
- HEURISTIC: motivational or strategic only
- BLOCKED: cannot progress without a theorem, definition, or decision
- INVALID: must not be used

## Ledger

| ID | Claim | Status | Dependency | Evidence | Next action |
|---|---|---|---|---|---|
| CLAY-GOAL | Full Clay-level Yang-Mills existence and mass gap | BLOCKED | Complete formal chain | FORMALIZATION_ROADMAP_CLAY.md | Decompose into milestones |
| AGENTIC-INFRA | Codex/Cowork coordination system | CONDITIONAL_BRIDGE | Bootstrap files and audit | AGENT_BUS.md | Codex creates, Cowork audits |
| AUTOCONTINUE | 24/7 task dispatch system | CONDITIONAL_BRIDGE | codex_autocontinue.py | registry/agent_tasks.yaml | Replace generic message with structured task dispatch |
