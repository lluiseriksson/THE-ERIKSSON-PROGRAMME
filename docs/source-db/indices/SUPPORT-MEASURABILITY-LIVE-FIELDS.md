# Support/Measurability Live Fields

Purpose: make the CMP116 support-containment and measurability fields directly searchable without treating locality, decay, or rendered H(Z) displays as support or measurability proofs.

## Source Anchors

Open these first:

```powershell
python scripts\source_db.py show proof.activity.support-measurability.v2
python scripts\source_db.py show proof.local-activity.construction.v2
python scripts\source_db.py show proof.activity.termwise.live-fields.v2
python scripts\source_db.py show cmp116.localized-activity.2.7-2.10
python scripts\source_db.py lean YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_omega
python scripts\source_db.py lean YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_skeleton
python scripts\source_db.py lean YangMills.RG.PhysicalGaugeCMP116Dictionary.physicalBondsOfCells
python scripts\source_db.py lean YangMills.RG.PhysicalGaugeCMP116Dictionary.image_bondToCube_subset_iff_physicalBondsOfCells
```

Focused blocker lookups:

```powershell
python scripts\source_db.py blockers source_to_lean_support_dictionary
python scripts\source_db.py blockers support_measurability_support_dictionary_open
python scripts\source_db.py blockers source_to_lean_measurability_dictionary
python scripts\source_db.py blockers support_measurability_activity_measurability_dictionary_open
```

Each blocker lookup above should route back to
`proof.activity.support-measurability.v2`; use them to find the exact open
support or measurability field before feeding the Lean targets below.

The support/measurability fields are downstream of local activity construction but are not discharged by construction, localization, or exponential decay alone.

The `physicalActiveSupport`, `physicalBondsOfCells`, and
`image_bondToCube_subset_iff_physicalBondsOfCells` routes are repository
operational support conventions, not primary-source support theorems.
`proof.activity.support-measurability.v2` remains dictionary-open until the
source localized-domain to `physicalActiveSupport` enlargement, the
`physicalBondsOfCells`/skeleton `HF X.val` dictionary, and the adapted-field
measurability plus finite-index/measurable-summand data are supplied.

## Live Fields

| Field | Source target | Lean target | Status |
|---|---|---|---|
| spectator support | source locality domain for spectator variables | `YangMills.RG.BalabanCMP116SourceAssumptions.spectator_support_subset` | dictionary_open |
| fluctuation support | source locality domain for fluctuation variables | `YangMills.RG.BalabanCMP116SourceAssumptions.fluctuation_support_subset` | dictionary_open |
| physical active support | source localized domains to repository `physicalActiveSupport` enlargement | `YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_omega`; `YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_skeleton` | dictionary_open |
| skeleton convention | source active sets to `PhysicalGaugeCMP116Dictionary` physicalBondsOfCells / skeleton convention | `YangMills.RG.PhysicalGaugeCMP116Dictionary.physicalBondsOfCells`; `YangMills.RG.PhysicalGaugeCMP116Dictionary.image_bondToCube_subset_iff_physicalBondsOfCells` | dictionary_open |
| measurability | adapted physical local activity as a measurable function of fluctuation fields | `YangMills.RG.BalabanCMP116SourceAssumptions.activity_stronglyMeasurable` | dictionary_open |

## Non-Claims

- Do not infer support containment from exponential decay.
- Do not infer measurability from the existence of a finite H(Z) summation display.
- Do not infer `raw_pointwise_decay` from support containment.
- Do not treat repository `physicalActiveSupport` conventions as a primary-source dictionary.

The useful next source step is to extract the exact source localized-domain/enlargement convention and the adapted-field measurability statement separately.
