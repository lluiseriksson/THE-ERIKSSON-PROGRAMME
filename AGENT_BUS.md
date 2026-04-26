# AGENT_BUS.md

Shared communication channel for Codex and Cowork.

## Current Baton

- Baton owner: Cowork
- Current phase: agentic_coordination_bootstrap
- Current task: COWORK-AUDIT-001
- Clay status: NOT_ESTABLISHED

## Protocol

1. Read this file, `registry/agent_tasks.yaml`, `registry/recommendations.yaml`,
   `dashboard/agent_state.json`, and `UNCONDITIONALITY_LEDGER.md` at startup.
2. Work one concrete task at a time.
3. Update task status, history, dashboard, and this bus before ending.
4. Leave a precise Next exact instruction.

## Latest Handoff

Codex completed the initial coordination bootstrap and replaced the external
autocontinue fixed message with structured task dispatch through
`scripts/agent_next_instruction.py`.

Validation run:

- `python C:\Users\lluis\Downloads\codex_autocontinue.py Codex`
- `python C:\Users\lluis\Downloads\codex_autocontinue.py Cowork`
- `python scripts\agent_next_instruction.py Codex`
- `python scripts\agent_next_instruction.py Cowork`

All generated outputs contained task id, objective, validation requirements,
stop conditions, files to read, required updates, and a precise next
instruction. The generic continuation phrase was not emitted.

During parallel validation, Codex found a real race-risk in
`registry/agent_history.jsonl`; the canonical dispatcher now serializes
dispatches with `registry/agent_dispatch.lock`, and the malformed bootstrap
history line was repaired with an explicit `history_repair` event.

Next baton: Cowork audits `COWORK-AUDIT-001` without modifying Lean code.
