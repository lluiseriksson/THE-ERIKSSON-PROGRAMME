# Dispatcher YAML Robustness Recheck

Timestamp: 2026-04-26T18:40:00Z

Task: `CODEX-DISPATCHER-YAML-ROBUSTNESS-RECHECK-001`

## Result

`scripts/agent_next_instruction.py` already has a correct emergency path for malformed shared YAML:

- `load_yaml` wraps `yaml.safe_load` and raises `YAMLRegistryError`.
- `main` catches `YAMLRegistryError`, records `dashboard/last_yaml_error.json`, appends a `yaml_registry_parse_error` event to `registry/agent_history.jsonl`, and emits `META-YAML-REPAIR-001`.
- The repair dispatch explicitly tells the next agent to repair only YAML syntax, preserve all tasks, and run `--peek` validation for Codex and Cowork.

No dispatcher semantic change was made in this recheck. Trigger-gated `FUTURE` discipline remains intact: `future_trigger_state` treats unknown explicit auto-promote language as not fired and logs `trigger_not_fired`.

## Recent Failure Pattern

`dashboard/last_yaml_error.json` records the concrete malformed-YAML class seen in this run: a list item beginning with a backtick was emitted as a plain YAML scalar, which PyYAML rejected. The preventive rule for future manual task edits is:

> Quote every validation/note/objective list item that begins with punctuation, a backtick, a bracket, or contains a colon that is not intended as a mapping key.

When adding long task prose manually, prefer a single quoted scalar or a block scalar over implicit multi-line plain scalars.

## Validation Commands

Run from the repository root:

```powershell
@'
import json, pathlib, yaml
root = pathlib.Path('.')
for p in ['registry/agent_tasks.yaml','registry/recommendations.yaml']:
    yaml.safe_load((root / p).read_text(encoding='utf-8'))
    print(f'YAML OK: {p}')
json.loads((root / 'dashboard/agent_state.json').read_text(encoding='utf-8'))
print('JSON OK: dashboard/agent_state.json')
for i, line in enumerate((root / 'registry/agent_history.jsonl').read_text(encoding='utf-8').splitlines(), 1):
    if line.strip():
        json.loads(line)
print('JSONL OK: registry/agent_history.jsonl')
'@ | python -

python scripts\agent_next_instruction.py --peek Codex
python scripts\agent_next_instruction.py --peek Cowork
```

## Current Validation Evidence

- `registry/agent_tasks.yaml`: PyYAML parse OK.
- `registry/recommendations.yaml`: PyYAML parse OK.
- `registry/agent_history.jsonl`: JSONL parse OK.
- `python scripts\agent_next_instruction.py --peek Codex`: returns `CODEX-F3-RESIDUAL-SELECTOR-COUNTEREXAMPLE-SEARCH-001`, a non-META Codex task.
- `python scripts\agent_next_instruction.py --peek Cowork`: returns `COWORK-F3-MAYER-B6-SCOPE-001`, a coherent Cowork task.

## Handoff

The next Codex task should proceed to the F3 residual-selector counterexample search selected by dispatcher priority. This recheck did not move any mathematical status, ledger row, or project percentage.
