# Negcoords runtime history spot-check

Task: `CODEX-NEGCOORDS-RUNTIME-HISTORY-SPOTCHECK-001`

Status: `DONE_SPOTCHECK_EVIDENCE_READY_FOR_COWORK_AUDIT`

## Objective

Address the open recommendation:

```text
REC-NEGCOORDS-RUNTIME-CONFIRMATION-001
```

by inspecting runtime history after the source-level negcoords fix in
`dashboard/codex_autocontinue_snapshot.py`.

## Source-level guard checked

The snapshot still contains the negative-coordinate-safe movement helper:

```text
dashboard/codex_autocontinue_snapshot.py
```

Relevant behavior: `safe_move_to` only avoids the primary `(0, 0)` fail-safe
corner and does not normalize negative monitor coordinates.  The submit paths
call `safe_move_to(...)` before focusing the prompt box or fallback send
button.

This task did not edit dispatcher behavior, autocontinue behavior, or Cowork
polling-spam gates.

## Runtime evidence

Using the recommendation's source-level verification timestamp as the cutoff:

```text
2026-04-26T08:00:00Z
```

`registry/agent_history.jsonl` contains:

```text
134 dispatch_delivery_state events with delivery_state = CONFIRMED_BUSY
0 JSON parse errors
0 relevant GHOST_PAUSE runtime events
```

The latest twelve confirmed post-fix deliveries include:

```text
2026-04-28T00:13:27Z Codex CODEX-AXIOM-FRONTIER-F3-V2.188-V2.216-RECONCILE-001 calibrated-button distance=29.0
2026-04-28T00:18:49Z Codex CODEX-LEDGER-F3-COUNT-EVIDENCE-COLUMN-EXTEND-V2.183-V2.216-001 calibrated-button distance=31.5
2026-04-28T00:25:24Z Codex META-GENERATE-TASKS-001 codex-enter distance=32.5
2026-04-28T00:30:19Z Codex CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-INJECTION-INTERFACE-RECOVERY-001 codex-ctrl-enter distance=32.5
2026-04-28T00:39:43Z Codex CODEX-F3-PROVE-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-INJECTION-001 codex-enter distance=32.5
2026-04-28T00:45:06Z Codex CODEX-F3-BASE-ZONE-COORDINATE-CANDIDATE-LEMMA-INVENTORY-001 codex-enter distance=32.5
2026-04-28T00:49:12Z Codex CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-SCOPE-001 codex-ctrl-enter distance=31.7
2026-04-28T00:52:42Z Codex CODEX-F3-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-INTERFACE-001 calibrated-button distance=32.5
2026-04-28T01:00:24Z Codex CODEX-F3-PROVE-SELECTOR-ADMISSIBLE-BASE-ZONE-COORDINATE-SOURCE-001 double-calibrated-button distance=32.5
2026-04-28T01:01:36Z Codex CODEX-AXIOM-FRONTIER-F3-V2.217-V2.219-RECONCILE-SCOPE-001 codex-enter distance=32.5
2026-04-28T01:07:43Z Codex CODEX-AXIOM-FRONTIER-F3-V2.217-V2.219-RECONCILE-001 codex-enter distance=32.5
2026-04-28T01:10:47Z Codex CODEX-NEGCOORDS-RUNTIME-HISTORY-SPOTCHECK-001 double-calibrated-button distance=31.7
```

The history contains entries whose task names include the word `GHOST`, but
those are diagnostic task names and recommendation text, not runtime
`GHOST_PAUSE` events.

## Recommendation status

`registry/recommendations.yaml` was not changed.  The recommendation remains
`OPEN` because Cowork owns audit authority for closing it.

This Codex spot-check supplies the runtime evidence Cowork requested: at least
five successful post-fix dispatch/delivery events and no relevant
`GHOST_PAUSE` signal.

## Validation

- Dashboard note records successful runtime evidence.
- `registry/recommendations.yaml` remains coherent and was not closed by Codex.
- YAML/JSON/JSONL validation passed.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
  planner metric, ledger row, proof claim, or Clay-level claim moved.

## Next task

```text
COWORK-NEGCOORDS-RUNTIME-CONFIRMATION-AUDIT-001
```

Cowork should audit this evidence and decide whether to resolve
`REC-NEGCOORDS-RUNTIME-CONFIRMATION-001`.
