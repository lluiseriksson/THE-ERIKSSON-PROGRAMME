# Sprint 14 — Mission contract runner

Goal: Run exactly one mission contract from `mission_contracts/` and produce a
reviewable patch plan.

1. Select `OC_001_eq231_source_subset_gapCarrier` unless a newer proof card is explicitly assigned.
2. Generate the prompt with `scripts/compile_mission_prompt.py`.
3. Fill `patch_intake/INTAKE_TEMPLATE.json` after the patch.
4. Run `scripts/check_patch_contract.py --contract mission_contracts/OC_001_eq231_source_subset_gapCarrier.json --intake patch_intake/INTAKE_TEMPLATE.json`.

Success: either one source-package field is discharged, or the exact primary-source lemma is narrowed.
