# Execution harness

This directory describes how to use the v5 pack as an agent workbench.

## Typical run

```bash
python scripts/mission_board.py --ranked
python scripts/compile_mission_prompt.py OC_001_eq231_source_subset_gapCarrier
python scripts/generate_patch_intake.py OC_001_eq231_source_subset_gapCarrier > patch_intake/oc001.json
# agent edits repo or records blocker
python scripts/score_patch_intake.py patch_intake/oc001.json
python scripts/render_hypothesis_burndown.py
```

## Outputs expected from agents

- a patch or explicit no-patch blocker;
- a filled patch intake;
- source-lock worksheet if any citation status changes;
- build/oracle note if any Lean theorem is claimed as theorem-fed.
