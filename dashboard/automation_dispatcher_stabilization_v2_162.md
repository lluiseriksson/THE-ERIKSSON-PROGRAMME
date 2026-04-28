# Automation Dispatcher Stabilization v2.162

Date: 2026-04-27

## Scope

This is an infrastructure-only intervention after repeated automation churn:
unconfirmed Codex sends, repeated Cowork polling audits, and META/AUDIT tasks
running without a new mathematical trigger.

## Changes

- `C:\Users\lluis\Downloads\codex_autocontinue.py`
  - Cowork default sidecar interval increased from 30s to 300s.
  - Cowork is now treated as a triggered sidecar for polling-style tasks.
  - Polling Cowork tasks are skipped for 900s when `AXIOM_FRONTIER.md`,
    `UNCONDITIONALITY_LEDGER.md`, `YangMills/ClayCore/LatticeAnimalCount.lean`,
    `CLAY_HORIZON.md`, and `F3_COUNT_DEPENDENCY_MAP.md` have not changed since
    the last Cowork sidecar dispatch.
  - Unconfirmed sends now get one delayed retry; after that the app is paused
    for 600s instead of looping.
  - Failed-delivery retry delay increased from 20s to 90s.
  - Session cooldown is recorded on every send attempt, not only confirmed
    deliveries, to reduce duplicate long-prompt injection under flaky visual
    confirmation.

- `scripts/agent_next_instruction.py`
  - Same-agent recent dispatch suppression increased from 60s to 300s.
  - Cowork FUTURE polling tasks without explicit fired triggers are no longer
    auto-promoted by the canonical dispatcher.

## Cowork Policy

Cowork should be useful when there is a real trigger:

- a new Codex frontier/interface/proof artifact,
- a ledger or percentage movement needing audit,
- a human-requested review,
- a concrete consistency/index refresh after changed deliverables.

Cowork should not spend cycles re-validating unchanged periodic freshness,
deliverables, PR-draft, or META task-generation surfaces on a polling interval.

## Validation

- `python -m py_compile C:\Users\lluis\Downloads\codex_autocontinue.py scripts\agent_next_instruction.py`
- `python C:\Users\lluis\Downloads\codex_autocontinue.py --preflight-only`

Both passed. Dispatcher peeks remain:

- Codex: `CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-IMAGE-INDEPENDENCE-SCOPE-001`
- Cowork: `COWORK-AUDIT-MATHLIB-PR-DRAFT-STATUS-001`

The watcher will now skip that Cowork periodic audit immediately unless a
tracked mathematical/ledger trigger changes after watcher startup.

## Unconditionality Impact

No Lean theorem, ledger row, F3 status, README/planner percentage, or Clay-level
claim moved. F3-COUNT remains `CONDITIONAL_BRIDGE`.
