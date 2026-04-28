# Cowork Read-Only Project Sidecar Dispatch

Task: `CODEX-COWORK-READONLY-PROJECT-SIDECAR-DISPATCH-001`

Status: `DONE_AUTOMATION_FIX`

## Root Cause

Cowork was being prompted, but only with `COWORK-WORKSPACE-MOUNT-BLOCKED`.
Because `/sessions/magical-busy-noether/mnt/THE-ERIKSSON-PROGRAMME/` is still
absent from the Cowork session, Cowork correctly answered `BLOCKED` and did no
project work.

## Fix

While `cowork_dispatch_suspended` remains true, the canonical dispatcher now
emits `COWORK-READONLY-PROJECT-SIDECAR-001` instead of the blocked-only prompt.
That prompt embeds a project snapshot from:

- `dashboard/agent_state.json`
- `AGENT_BUS.md`
- the latest dashboard validation artifact

Cowork is instructed to produce a project-specific read-only audit/research note
in chat, not to write registries, and not to answer only `BLOCKED`. If the mount
appears later, Cowork reports `MOUNT_AVAILABLE` and normal dispatch can resume.

The active watcher treats this read-only task as synthetic, like the old mount
blocked task: it will not try to write delivery state into `registry/agent_tasks.yaml`
for the synthetic id, and it uses the same five-minute repeat guard.

## Validation

- `python -m py_compile scripts\agent_next_instruction.py dashboard\codex_autocontinue_snapshot.py C:\Users\lluis\Downloads\codex_autocontinue.py`
- `python scripts\agent_next_instruction.py Cowork --peek` now returns `COWORK-READONLY-PROJECT-SIDECAR-001`
- `python C:\Users\lluis\Downloads\codex_autocontinue.py --preflight-only` reports Cowork fallback `COWORK-READONLY-PROJECT-SIDECAR-001`

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.

