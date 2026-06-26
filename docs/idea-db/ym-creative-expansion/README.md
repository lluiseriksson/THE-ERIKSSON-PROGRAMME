# YM Creative Expansion Pack v5

**Execution harness / closed-loop patch edition.**

This pack is for agents working on `lluiseriksson/THE-ERIKSSON-PROGRAMME` after
Batch 002/003 source-db integration.  It assumes the idea database already lives
under `docs/idea-db/ym-creative-expansion/` and that agents should now produce
small patches that remove explicit fields, promote source records, or shrink a
specific proof obligation.

## Main use

```bash
python scripts/mission_board.py
python scripts/compile_mission_prompt.py OC_001_eq231_source_subset_gapCarrier
python scripts/generate_patch_intake.py OC_001_eq231_source_subset_gapCarrier > patch_intake/my_patch.json
python scripts/score_patch_intake.py patch_intake/my_patch.json
python scripts/check_patch_contract.py \
  --contract mission_contracts/OC_001_eq231_source_subset_gapCarrier.json \
  --intake patch_intake/my_patch.json
```

## v5 additions

- closed-loop patch intake and scoring;
- source-lock worksheets before any source-status promotion;
- theorem-skeleton queue for the highest-value proof cards;
- router synchronization tables so a citation key maps to exactly one mission;
- anti-OCR, anti-tautology and no-new-consumer guardrails;
- hypothesis-burndown rendering from the v4/v5 debt vector.

## Highest priority

The first target is still the CMP116 Eq. (2.31) P-family route, but v5 narrows
it to one field when possible:

```text
CMP116Eq231BalabanPFamilySourcePackage.source_subset_gapCarrier
```

A patch that merely adds another downstream constructor without removing a
field, source-pending blocker or exact source-status obligation should be
rejected.

## Hard boundary

This pack is not a mathematical source, not a Lean theorem, not evidence for
`hRpoly`, and not a route into `YangMillsCore`.  It is an execution harness for
agents.
