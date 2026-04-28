# Cowork Autocontinue Blocked Prompt Injection Fix

Date: 2026-04-28

## Scope

Operational fix for the 24/7 watcher path that should keep Codex and Cowork
receiving prompts. This is not a mathematical F3 task and does not move
F3-COUNT, any README metric, any planner metric, any ledger status, or any
percentage.

## Root Cause

`dashboard/agent_state.json` correctly marks Cowork dispatch as suspended while
the Cowork session lacks the repository mount:

```text
/sessions/magical-busy-noether/mnt/THE-ERIKSSON-PROGRAMME/
```

The canonical dispatcher still emits the safe synthetic prompt:

```text
COWORK-WORKSPACE-MOUNT-BLOCKED
```

However, `codex_autocontinue.py` treated `cowork_dispatch_suspended` as a
reason to disable Cowork in the visual watcher before any prompt could be
pasted. That converted an honest mount blocker into total prompt starvation on
the Cowork side.

## Fix

Patched both the active watcher and the versioned snapshot:

- `C:/Users/lluis/Downloads/codex_autocontinue.py`
- `dashboard/codex_autocontinue_snapshot.py`

Behavior after the patch:

- Codex remains the primary implementing agent.
- Cowork is still watched when calibrated, even while dispatch is suspended.
- While suspended, Cowork receives only the safe
  `COWORK-WORKSPACE-MOUNT-BLOCKED` prompt.
- The blocked prompt has a five-minute repeat guard to avoid flooding the chat.
- The watcher does not try to record delivery state for the synthetic blocked
  task id, because it is not a real registry task.
- Normal registry-writing Cowork tasks remain blocked until the folder is
  actually mounted and `cowork_dispatch_suspended` is cleared.

## Validation

Commands run:

```powershell
python -m py_compile C:\Users\lluis\Downloads\codex_autocontinue.py dashboard\codex_autocontinue_snapshot.py
python C:\Users\lluis\Downloads\codex_autocontinue.py --preflight-only
```

Preflight confirmed:

- YAML/JSON/JSONL parse.
- No duplicate task ids.
- `Cowork --peek` returns `COWORK-WORKSPACE-MOUNT-BLOCKED`.
- Guardrail diagnostic reports `Cowork suspended prompt remains sendable=True`.

## Remaining Blocker

This patch restores Cowork prompt injection, but it cannot make Cowork write the
repository while the Cowork session lacks the mounted folder. To resume real
Cowork audit/write tasks, mount the repository at:

```text
/sessions/magical-busy-noether/mnt/THE-ERIKSSON-PROGRAMME/
```

Then clear `cowork_dispatch_suspended` in `dashboard/agent_state.json`.

## Follow-up: Codex Stale-Busy False Confirmation

After the first fix, the watcher did inject Cowork's blocked prompt, but Codex
hit a separate stale-busy path:

```text
[Codex] método codex-enter no mostró cambio visual suficiente (d=56.6, Δ=0.0)
[Codex] método codex-ctrl-enter no mostró cambio visual suficiente (d=56.6, Δ=0.0)
[Codex] ocupado confirmado (d=56.6), rearmado.
```

The last line was wrong: unchanged detector distance must not confirm delivery
when the rescue path started from an already-busy detector state.

Additional patch:

- Stale-busy Codex submit now tries Enter, Ctrl+Enter, calibrated button, and
  double calibrated button.
- The rearm loop now uses the same stale-busy confirmation rule as the submit
  loop: confirmation requires a real ready-state transition or a large detector
  jump, not merely `not ready`.
- Startup stale-busy is now treated as untrusted immediately when Codex has not
  yet had a confirmed delivery in the watcher session. If the dispatcher has a
  concrete non-META task, the watcher sends instead of waiting 18 seconds while
  printing `ocupado` for a stale detector.
- The affected task
  `CODEX-F3-BASE-ZONE-ORIGIN-CERTIFICATE-CODE-INJECTION-DATA-CANDIDATE-INVENTORY-001`
  was requeued to `READY` because the user reported the prompt did not arrive.

## Follow-up: Cowork Decoupled From Codex Pending Retries

Another live run showed Cowork stuck behind Codex's unconfirmed pending prompt:

```text
[SKIP] Cowork: Codex tiene un envío pendiente no confirmado; evito interferir hasta reintento.
```

This guard has been removed. Codex and Cowork each focus their own calibrated
prompt box before paste/submit, so Cowork can continue under its own repeat
guard and sidecar interval even while Codex is retrying an unconfirmed delivery.

Preflight now also auto-abandons stale unconfirmed `IN_PROGRESS` tasks after 30
minutes via `ABANDONED_UNCONFIRMED`, which requeues them without claiming
completion. This repaired the stale Codex inventory task left by earlier
delivery failures.

## Follow-up: Codex Multipoint Paste/Submit

Codex delivery still failed after detector fixes because a single prompt-box
coordinate could be stale or fail to focus the input. The Codex send path now:

- repastes the full dispatcher prompt at several focus points around the
  calibrated prompt box and toward the send button;
- tries Enter, Ctrl+Enter, calibrated button, and double calibrated button at
  each focus point;
- preserves the active focus point during submit retries instead of jumping back
  to the original stale coordinate;
- abandons/requeues stale unconfirmed dispatches after 2 minutes on preflight.

The user-confirmed undelivered F3 inventory dispatch was marked
`ABANDONED_UNCONFIRMED` and is `READY` again.
