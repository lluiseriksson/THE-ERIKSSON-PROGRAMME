# Agent Mission Control — v4

v4 turns the creative expansion pack into a bounded execution system for agents.
The repository now already contains the idea DB and Batch 003 proof-obligation
cards, so the useful next layer is a **mission contract**: one proof card, one
source-key set, one exact hypothesis/field, one acceptance rule.

## Default execution loop

```text
1. Choose one `mission_contracts/OC_*.json`.
2. Generate/read its prompt in `mission_prompts/`.
3. Run repo source-db commands for only the allowed source keys.
4. Produce either:
   a. a real source extraction + theorem-shaped Lean target, or
   b. a narrowed blocker that removes ambiguity for the next agent.
5. Score the candidate patch with `scripts/check_patch_contract.py`.
6. Reject the patch if it adds consumers while removing no source field.
```

## Immediate recommendation

Start with `OC_001_eq231_source_subset_gapCarrier`.  It is smaller than the full
Eq. (2.31) membership iff and aligns with the Lean reducer already present in
`BalabanCMP116Eq231.lean`.

## What counts as real progress

- A field of `CMP116Eq231BalabanPFamilySourcePackage` is discharged.
- A source-pending entry becomes source-extracted with exact formula, constants,
  quantifiers and dictionary.
- A caller premise disappears from a theorem because a source theorem now supplies it.
- A proof card changes status only after the Lean consumer is theorem-fed.

## What does not count

- A new theorem with the same old source hypotheses.
- A record constructor that only repackages existing fields.
- A broader prompt asking agents to inspect more papers.
- Treating the creative pack or operational crosswalk as primary evidence.
