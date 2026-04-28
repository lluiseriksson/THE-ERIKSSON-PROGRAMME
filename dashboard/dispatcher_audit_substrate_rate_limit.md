# Dispatcher audit-substrate rate limit

Task: `CODEX-DISPATCHER-AUDIT-SUBSTRATE-RATE-LIMIT-001`

Status: `DONE_AUDIT_SUBSTRATE_GATE_ADDED_NO_POLLING_WEAKENING`

Implemented a canonical dispatcher guard in
`scripts/agent_next_instruction.py` for Cowork audit slots whose id begins
`COWORK-AUDIT-CODEX-` and whose text names concrete `CODEX-*` substrate task
ids.

If at least one named substrate is already complete, the audit remains
dispatchable. If the named substrate is known to the registry/history but has
not landed yet, the audit is skipped so Cowork can take another READY task
instead of repeatedly auditing absent work. If the named substrate is unknown,
the audit is allowed so Cowork can diagnose the mismatch.

The existing Cowork polling-spam gates are unchanged. The guard does not mark
audit tasks DONE, does not reset Codex tasks, and does not touch F3-COUNT status
or percentages.

Validation:

- `python -m py_compile scripts/agent_next_instruction.py C:/Users/lluis/Downloads/codex_autocontinue.py` passed.
- `python C:/Users/lluis/Downloads/codex_autocontinue.py --preflight-only` passed.
- YAML/JSON/JSONL validation passed.
- Cowork peek selected `COWORK-LEDGER-FRESHNESS-AUDIT-019`, not the pending
  `COWORK-AUDIT-CODEX-DISPATCHER-AUDIT-SUBSTRATE-RATE-LIMIT-001` audit, while
  its Codex substrate was still incomplete.
