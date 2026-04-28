# Cowork Workspace Mount Dispatch Suspension

**Task**: `CODEX-COWORK-WORKSPACE-MOUNT-DISPATCH-SUSPENSION-001`
**Status**: `DONE_COWORK_DISPATCH_SUSPENDED_UNTIL_MOUNT_AVAILABLE`
**Timestamp**: `2026-04-28T08:05:00Z`

## Problem

Cowork repeatedly halted `META-GENERATE-TASKS-001` because its session path:

```text
/sessions/magical-busy-noether/mnt/
```

contained only empty `outputs/`, `uploads/`, and `.claude/` directories. The
shared repository was not mounted at:

```text
/sessions/magical-busy-noether/mnt/THE-ERIKSSON-PROGRAMME/
```

That made the META task's required registry/dashboard writes impossible. The
failure mode was environmental, not an audit disagreement.

## Patch

Codex patched the canonical dispatcher and watcher path so Cowork is no longer
given registry-writing or META maintenance work while the mount is absent.

Changed files:

- `scripts/agent_next_instruction.py`
- `dashboard/codex_autocontinue_snapshot.py`
- `C:/Users/lluis/Downloads/codex_autocontinue.py`
- `dashboard/agent_state.json`

The state flag is:

```json
"cowork_dispatch_suspended": true
```

While this flag is set, `scripts/agent_next_instruction.py Cowork --peek`
returns a blocked pseudo-dispatch:

```text
Task id: COWORK-WORKSPACE-MOUNT-BLOCKED
Task status at dispatch: BLOCKED
```

The running autocontinue watcher also checks the same state file before loading
Cowork and again during the loop, so Cowork sidecar dispatch is disabled without
stopping Codex.

## Resume Condition

Resume Cowork only after the repository is mounted read/write at:

```text
/sessions/magical-busy-noether/mnt/THE-ERIKSSON-PROGRAMME/
```

Then clear `cowork_dispatch_suspended` in `dashboard/agent_state.json`. After
that, Cowork can return to artifact-backed audit work.

## Validation

- `python -m py_compile scripts/agent_next_instruction.py dashboard/codex_autocontinue_snapshot.py C:/Users/lluis/Downloads/codex_autocontinue.py`
- `python scripts/agent_next_instruction.py Cowork --peek` returns `COWORK-WORKSPACE-MOUNT-BLOCKED`
- `python scripts/agent_next_instruction.py Codex --peek` still selects `CODEX-F3-SCOPE-STRUCTURAL-RESIDUAL-VALUE-CODE-SEPARATION-SOURCE-001`
- YAML/JSON/JSONL validation passed

## Mathematical Impact

None. F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README
metric, planner metric, ledger row, proof closure claim, or Clay-level claim
moved.
