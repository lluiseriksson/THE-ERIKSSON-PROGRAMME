# Gaussian/root/Hessian live fields — Batch 006

**Purpose.** This index turns the raw-source M3 frontier into an ordered checklist for LLMs. It is not a primary-source extraction. It tells agents which exact field they are trying to discharge and which source keys to open first.

## Current field order

```text
covariance_root_certificate
→ root_localization
→ gaussian_pushforward
→ wilson_hessian_identification
→ local_physical_activity_construction
→ spectator/fluctuation support + measurability
→ raw_pointwise_decay / termwise estimate
→ Appendix-F / rooted H# identity
→ flow and IR
```

The Lean record `BalabanCMP116SourceAssumptions` keeps these fields separate. Do not merge them into a monolithic source claim.

## Current Lean narrowing

`PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization` separates
the CMP116 Eq. (2.5)--(2.6) normalization route into a source coordinate map,
a source physical Gaussian, equality with the dictionary/root map, equality
with the consumer Gaussian law, and the normalized pushforward identity.
The scale-family raw-source constructors
`rawSource_of_lemma3ActivityEstimate_gaussianNormalization`,
`rawSource_of_weightedPostPBoundaries_gaussianNormalization`, and
`rawSource_of_eq231_weightedPostPBoundaries_gaussianNormalization`, and
`rawSource_of_eq231_sourcePIndexMemIff_gaussianNormalization` consume that
structured record instead of a raw per-scale `gaussian_pushforward` equality.

`CMP116GaussianPushforwardNormalization.of_sourceNormalizedChange` is the
current Lean endpoint for CMP116 Eq. (2.5)--(2.6).  It packages three named
source/dictionary facts into the structured record: Balaban's source map
`X -> B' = (C^(k))^(1/2) X` equals `D.gaussianRootMap root`, the source
correlated `B'` law equals the downstream `physicalGaussian`, and the
determinant/Jacobian-normalized pushforward of `balabanCMP116Dmu0` by the
source map is exactly the source Gaussian law.
Those facts now have independent Lean source records:
`CMP116GaussianCoordinateMapSource`, `CMP116GaussianPhysicalLawSource`, and
`CMP116GaussianNormalizedPushforwardSource`.  The constructor
`CMP116GaussianPushforwardNormalization.of_sourceRecords` assembles the
structured normalization record from those three records.
The localized and raw source packages also expose direct source-record
constructors,
`PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.of_sourceRecords`
and
`PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_sourceRecords`,
so callers can feed the three CMP116 Gaussian records without manually
preassembling the intermediate normalization record.
The same boundary is now available at scale-family level through
`cmp116GaussianPushforwardNormalizationScaleFamily_of_sourceRecords`,
`rawSource_of_lemma3ActivityEstimate_sourceRecords`,
`rawSource_of_weightedPostPBoundaries_sourceRecords`,
`rawSource_of_eq231_weightedPostPBoundaries_sourceRecords`, and
`rawSource_of_eq231_sourcePIndexMemIff_sourceRecords`.  Those constructors do
not prove any Gaussian record; they remove the caller-side intermediate
normalization package from the existing raw-source routes.

This is still a source-pending analytic field.  The determinant/Jacobian
normalization and source-to-Lean coordinate dictionary for CMP116 (2.5)--(2.6)
remain to be extracted before the record can be populated from primary source.

## First source keys to open

```powershell
python scripts/source_citations.py show cmp116.gaussian-pushforward.2.5-2.6
python scripts/source_citations.py show cmp116.localized-activity.2.7-2.10
python scripts/source_db.py show dimockii.fluctuation-covariance.271-276
python scripts/source_db.py show cmp99.background-field-propagator-source-target
python scripts/source_db.py show cmp102.variational-hessian-expansion-source-target
python scripts/source_db.py show proof.wilson.hessian.identification.v2
python scripts/source_db.py show proof.activity.support-measurability.v2
python scripts/source_db.py show proof.activity.termwise.live-fields.v2
python scripts/source_db.py show proof.dimock.appendixf.hsharp-feed
python scripts/source_db.py show proof.rooted-hsharp-remainder.identity.v2
python scripts/source_db.py show dimockii.appendix-f.second-ursell.645-646
python scripts/source_db.py show proof.rawsource.m3.live-fields.v2
```

## Live fields

| Field | Source target | Lean target | Danger |
|---|---|---|---|
| covariance/root certificate | CMP116 covariance/root definitions + Dimock-style architecture as guide | `PhysicalLocalizedCovarianceRootCertificate` | Product Gaussian display alone is not a root certificate. |
| gaussian pushforward | CMP116 (2.5)-(2.6) + coordinate/Jacobian dictionary | `gaussian_pushforward` | Do not ignore determinant/normalization. |
| root localization | CMP116 (2.7)-(2.10), covariance-root localization | `root_localization` | H(Z) display is not exact finite root reconstruction. |
| Wilson Hessian | CMP102 Eq. (142), CMP102 `H`, CMP99 `G(U)`, and the remaining coordinate/sign/normalization dictionary | `YangMills.RG.physicalGaugeWilsonHessianIdentification`; `YangMills.RG.BalabanCMP116SourceAssumptions.wilson_hessian_identification` | Located Hessian/propagator pages are not yet the Lean dictionary theorem. |
| physical precision defect budget | source identification of `physicalPrecisionDefect` plus positive residual margin `schurCatalanBudget M epsilon < min 1 a / CP` | `YangMills.RG.physicalPrecisionDefect_hdefect_of_smallBackgroundPerturbation`; `YangMills.RG.physicalPrecisionCatalanDefectCoercivityConstant_pos`; `YangMills.RG.covarianceOfPhysicalPrecisionCatalanDefect_comp_precision`; `YangMills.RG.precision_comp_covarianceOfPhysicalPrecisionCatalanDefect`; `YangMills.RG.norm_covarianceOfPhysicalPrecisionCatalanDefect_le`; `YangMills.RG.covarianceOfPhysicalPrecisionCatalanDefect_psd` | The Catalan defect bound and residual coercivity budget are separate hypotheses. |
| local activity | CMP116 localized H(Z) construction | `local_physical_activity_construction` | Construction and decay are separate. |
| support/measurable | localized domains to physical support; see `proof.activity.support-measurability.v2` | `spectator_support_subset`, `fluctuation_support_subset`, `activity_stronglyMeasurable` | Support is not implied by exponential decay. |
| termwise/raw decay | Eq. (2.29), Eq. (2.31), Eq. (2.37), activity identity; see `proof.activity.termwise.live-fields.v2` | `raw_pointwise_decay`, `termwise_estimate` | Finite-sum norm bridge is not source termwise estimate. |
| rooted H# | Appendix F + physical raw-source scale family; see `proof.dimock.appendixf.hsharp-feed` and `proof.rooted-hsharp-remainder.identity.v2` | `YangMills.RG.BalabanCMP116SourceAssumptions.rooted_hsharp_remainder_identity` | H# is downstream, not proof of upstream Gaussian/root/Hessian fields. |

## Batch 006 rule

A useful next commit should remove one row above or sharpen one primary citation target for one row. New wrappers that merely pass the same hypotheses around are cosmetic.
