# YM Creative Expansion Pack v3 — post-integration hypothesis-removal edition

This ZIP is the v3 continuation of the Yang-Mills creative-expansion workflow.
It assumes v2 has already been staged in `THE-ERIKSSON-PROGRAMME` under
`docs/idea-db/ym-creative-expansion/` and that the repository now has Batch 002
operational crosswalks plus Batch 003 proof-obligation cards.

## What changed in v3

v1/v2 generated creative derived formulas. v3 converts that idea database into a
strict source-hypothesis removal discipline.

```text
one proof card -> one source field -> one commit
```

## Current best target

Attack CMP116 Eq. (2.31), specifically the source package field:

```lean
CMP116Eq231BalabanPFamilySourcePackage.source_subset_gapCarrier
```

Use the reducer already present in the repo:

```lean
cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes
```

Target source-shaped theorem:

```text
sourceAdmissible Z D P -> forall b in P, b.1 in gapCubes Z D
```

This is narrower and more realistic than proving the full P-family membership iff
in one jump.

## New material

- `post_integration/REPO_UPDATE_BRIEF.md`
- `data/repo_update_scan.v3.json`
- `data/batch003_hypothesis_removal_queue.v3.json`
- `proof_obligation_cards/PO_*.md`
- D31-D45 formula/proof-routing cards
- new Lean templates for Eq. (2.31), Eq. (2.29), pointwise residuals and R-operation bridge
- `builders/CONSTRUCTOR_PLAYBOOK_v3.es.md`
- `rankings/BUILDER_PRIORITY_v3.md`
- `falsification/NO_NEW_CONSUMERS_CHECK.md`
- `prompts/constructor_v3_prompt.es.md`

## Hard boundary

This pack is not a proof of Yang-Mills, not a proof of `hRpoly`, and not source
evidence. It must not be imported into `YangMillsCore`. It is an agent handoff
for creating source-backed theorem patches.

Run:

```bash
python scripts/validate_pack.py
python scripts/query_expansion_db.py --search D32
```
