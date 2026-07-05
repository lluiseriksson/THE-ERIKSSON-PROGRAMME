# Hypothesis Removal Queue — Batch 003

Ordered by payoff and risk. A commit should remove one live hypothesis or promote one source-pending item to a real theorem-feedable interface.

| Rank | Key | Main live hypothesis/blocker | Source keys | Lean payoff |
|---:|---|---|---|---|
| 1 | `proof.eq231.membership-iff.source-package` | hPIndex | `cmp116.eq231.p-family-carrier-source-target`, `cmp109.bond-convention.positive-oriented`, `crosswalk.eq231.p-family-source-dictionary-route` | `cmp116Eq231_balabanPFamily_sourcePIndexMemIff`, `cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff` |
| 2 | `proof.eq231.carrier-count.four-positive-directions` | bondCarrier_card_le inside CMP116Eq231PBondBoundary | `cmp116.eq231.p-family-carrier-source-target`, `cmp109.bond-convention.positive-oriented` | `CMP116Eq231PBondBoundary.of_sourceBondSets`, `CMP116Eq231PBondBoundary.of_sourceFilteredBondSets` |
| 3 | `proof.eq231.pointwise-p-residual-majorization` | hpointwise | `cmp116.eq231.p-bond-sum`, `cmp116.eq231.p-family-carrier-source-target` | `cmp116PStageSourceBound_of_eq231_pointwise`, `CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise` |
| 4 | `proof.eq229.cammarota-dstage-summability` | CMP116Lemma3Eq229ScaleBoundary | `cmp116.eq229.d-stage-summability`, `cmp109.ref26.cammarota-infinite-range-cluster`, `cammarota.cmp85.polymer-mayer-source-target` | `YangMills.RG.CMP116Lemma3Eq229ScaleBoundary`, `YangMills.RG.CMP116Eq229Summability` |
| 5 | `proof.eq237.fixed-z0prime-source-estimate` | fixed-Z0' Eq. (2.37) premise | `cmp116.eq237.post-p-resummation`, `cmp116.constants.c3-alpha5`, `crosswalk.eq237.combined-postp-route` | `YangMills.RG.cmp116PostPResidualSourceBound_of_eq237`, `YangMills.RG.CMP116Eq237MajorizationBoundary` |
| 6 | `proof.activity.termwise-identification` | CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification | `cmp116.localized-activity.2.7-2.10`, `cmp116.lemma3.window.2.14-2.38`, `crosswalk.gaussian-root-activity-route` | `CMP116Lemma3ActivityTermwiseScaleBoundary`, `cmp116Lemma3ActivityEstimateScaleFamily_of_resummation` |
| 7 | `proof.gaussian.root.localization-certificate` | gaussian_pushforward | `cmp116.gaussian-pushforward.2.5-2.6`, `cmp116.localized-activity.2.7-2.10`, `cmp95.covariance-green.bounds-source-target` | `PhysicalLocalizedCovarianceRootCertificate`, `PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward` |
| 8 | `proof.dimock.appendixf.hsharp-feed` | activity bound |H(X)| <= H0 exp(-kappa d_M) | `crosswalk.dimock.appendixf-hole-cluster-route`, `dimockii.appendix-f.cluster-with-holes`, `dimockii.appendix-f.second-ursell.645-646` | `omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`, `balabanCMP116AppendixFHsharpOfIntegratedKsharp` |
| 9 | `proof.cmp122.r-operation-polymer-local-bound` | RawYMActivityDecay plus post-R action/local-activity dictionary | `cmp119.density-expansion-form.2.18`, `cmp119.t-operation-action-factorization.2.19-2.23`, `cmp119.e-term-local-regularity.2.24-2.29`, `cmp119.r-term-bound.2.31`, `cmp119.b-term-local-regularity-bound.2.34-2.42`, `cmp119.rt-improved-new-expressions.before-theorem1`, `cmp119.theorem1.rt-inductive-assumptions`, `cmp122ii.theorem1.coupling-interval-induction`, `cmp122i.large-field-c-bound.1.70`, `cmp122ii.rprime-bound.1.98-1.100`, `cmp122ii.post-r-action-split.1.101` | `RawYMActivityDecay`, `CMP116RawSourceM3Frontier` |
| 10 | `proof.flow.ir.bridge` | coupling flow assumptions | `crosswalk.flow-ir-asymptotic-freedom-route` | `CouplingFlow.logistic_geometric_decay`, `remainder_geometric_of_logistic` |
| 11 | `proof.source-status-promotion.gates` | source_pending entries | `docs.SOURCE-CITATIONS`, `docs.source-db.README` | `source_db.verify`, `source_db.build` |
| 12 | `proof.final-frontier.pipeline` | Eq. (2.29) | `crosswalk.final-frontier-pipeline`, `cmp116.lemma3.final-2.38`, `cmp116.effective-action.2.39-2.41` | `CMP116RawSourceM3Frontier`, `BalabanCMP116SourceTheorem` |

## Commit rule

Do not add new downstream wrappers in this queue. Either extract/prove a source theorem, or record the exact missing lemma with enough precision that the next agent can attack it directly.
