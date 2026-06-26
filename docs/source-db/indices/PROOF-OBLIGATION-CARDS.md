# Proof Obligation Cards — Batch 003

Purpose: give LLM agents theorem-shaped targets instead of making them rediscover the route from source citations to Lean declarations.

These cards are operational metadata, not primary sources. Every card points back to primary citation keys or source-pending targets.

## 1. `proof.eq231.membership-iff.source-package`

**Topic:** CMP116 Eq. (2.31) P-family source dictionary
**Status:** `blocked_on_source`

**Target shape:**

```text
P in BalabanPFamily(Z,D) <-> P subset gapCubes(Z,D) x Fin 4 and admissible(Z,D,P) = true
```

**Inspect source keys first:**
  - cmp116.eq231.p-family-carrier-source-target
  - cmp109.bond-convention.positive-oriented
  - crosswalk.eq231.p-family-source-dictionary-route

**Live hypotheses / blockers:**
  - hPIndex
  - hPcarrier on non-filtered sourceBondSets route

**Removes:**
  - caller-supplied PIndex = cmp116Eq231SourcePIndex gapCubes admissible
  - manual carrier containment for source P

**Lean targets:**
  - cmp116Eq231_balabanPFamily_sourcePIndexMemIff
  - cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff
  - CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets
  - CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_filteredBondSets

**Dependencies/open questions:**
  - positive-oriented bond ownership
  - complete source admissibility definition
  - source-to-Lean encoding of Balaban finite bond sets

**Do not:**
  - Do not define admissible as decide(P in PIndex).
  - Do not use the source lower bound |P| >= 1/2 M^-4 |Z0\Y0| as a carrier upper bound.

**Next action:** Open CMP116 page 12 and pages 18-19 only; extract the eligible bond universe and exact iff.

## 2. `proof.eq231.carrier-count.four-positive-directions`

**Topic:** CMP116 Eq. (2.31) eligible carrier cardinality
**Status:** `blocked_on_source`

**Target shape:**

```text
|EligibleCarrier(Z0,Y0)| <= 4 * |Z0 \ Y0|, equivalently <= 4*M^4*gapMass
```

**Inspect source keys first:**
  - cmp116.eq231.p-family-carrier-source-target
  - cmp109.bond-convention.positive-oriented

**Live hypotheses / blockers:**
  - bondCarrier_card_le inside CMP116Eq231PBondBoundary
  - positive-tail ownership of eligible bonds

**Removes:**
  - abstract carrier-count field for concrete source route

**Lean targets:**
  - CMP116Eq231PBondBoundary.of_sourceBondSets
  - CMP116Eq231PBondBoundary.of_sourceFilteredBondSets
  - CMP116Eq231BalabanPFamilySourcePackage.of_bond_fst_mem_gapCubes
  - cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes
  - cmp116Eq231GapCarrier_card_le_four_scale4_gapMass

**Dependencies/open questions:**
  - eligible bond has a unique positive-direction encoding
  - tail/base cube lies in Z0\Y0 or another source-owned injection into gapCubes x Fin 4

**Do not:**
  - Do not infer factor 4 from unoriented incidence; that can be 8.
  - Do not cite CMP109 alone as the CMP116 carrier theorem.

**Next action:** Search only for CMP116-specific carrier ownership; CMP109 supplies ambient orientation, not the count.

## 3. `proof.eq231.pointwise-p-residual-majorization`

**Topic:** CMP116 Eq. (2.31) pointwise P-residual majorization
**Status:** `analytic_blocker`

**Target shape:**

```text
pResidualWeight(Z,D,P) <= 2*(M+2)^4*epsilon2*pGeometryWeight(Z,D,P), then pGeometryWeight <= Eq231 PWeight
```

**Inspect source keys first:**
  - cmp116.eq231.p-bond-sum
  - cmp116.eq231.p-family-carrier-source-target

**Live hypotheses / blockers:**
  - hpointwise
  - hgeometry or source identification of pGeometryWeight

**Removes:**
  - manual pointwise P residual bound feeding P-stage summability

**Lean targets:**
  - cmp116PStageSourceBound_of_eq231_pointwise
  - CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
  - CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries

**Dependencies/open questions:**
  - identify actual P residual term
  - rate rho = gamma2*epsilon1^2/(20*gk^2)
  - source bracket rho - 4*M^4*exp(-2*rho)

**Do not:**
  - Do not claim Eq. (2.31) closure from finite entropy alone; the residual term must be matched.

**Next action:** After P dictionary, inspect the factors surrounding Eq. (2.31) to identify pResidualWeight and pGeometryWeight.

## 4. `proof.eq229.cammarota-dstage-summability`

**Topic:** CMP116 Eq. (2.29) D-stage product summability via Cammarota CMP85
**Status:** `blocked_on_external_source`

**Target shape:**

```text
sum_D prod_{Y in D} alpha6*exp(-delta*kappa*d_k(Y)) <= 1
```

**Inspect source keys first:**
  - cmp116.eq229.d-stage-summability
  - cmp109.ref26.cammarota-infinite-range-cluster
  - cammarota.cmp85.polymer-mayer-source-target
  - crosswalk.eq229.cammarota-dstage-route

**Live hypotheses / blockers:**
  - CMP116Lemma3Eq229ScaleBoundary
  - CMP116Eq229Summability
  - DIndex/DParts dictionary

**Removes:**
  - manual Eq. (2.29) D-stage summability
  - qualitative sufficiently-large/small source gap

**Lean targets:**
  - CMP116Lemma3Eq229ScaleBoundary
  - CMP116Eq229Summability
  - cmp116H_postD_sum_le_of_eq229
  - cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound

**Dependencies/open questions:**
  - Cammarota theorem statement
  - smallness threshold dependencies
  - Balaban D-family dictionary
  - metric d_k convention

**Do not:**
  - Do not cite Cammarota bibliographic entry as theorem extraction.
  - Do not turn 'K sufficiently large and alpha6 sufficiently small' into constants without proof.

**Next action:** Obtain clean Cammarota CMP85 theorem text or PDF page; extract theorem, assumptions, constants, and route to Balaban Eq. (2.29).

## 5. `proof.eq237.fixed-z0prime-source-estimate`

**Topic:** CMP116 Eq. (2.37) fixed-Z0' source estimate
**Status:** `analytic_blocker`

**Target shape:**

```text
fixed Z0' bound from Eq. (2.37) plus final Z0' summation gives combined post-P source bound
```

**Inspect source keys first:**
  - cmp116.eq237.post-p-resummation
  - cmp116.constants.c3-alpha5
  - crosswalk.eq237.combined-postp-route

**Live hypotheses / blockers:**
  - fixed-Z0' Eq. (2.37) premise
  - post-(2.37) final summation
  - Z0/Z0' source dictionary

**Removes:**
  - caller-supplied combined CMP116PostPResidualSourceBound inputs

**Lean targets:**
  - cmp116PostPResidualSourceBound_of_eq237
  - CMP116Eq237MajorizationBoundary
  - cmp116Eq237FixedZ0PrimeWeight
  - cmp116Eq237Amplitude

**Dependencies/open questions:**
  - D/P/Z0/Z0' dictionaries
  - component product over Zi'
  - alpha5/C3 constant majorants
  - post Eq. (2.37) half-exponent reserve

**Do not:**
  - Do not split into standalone Z0 and Z0' estimates unless the source supports the split.
  - Do not collapse O(1) constants without a common-majorant theorem.

**Next action:** Extract exact fixed-Z0' theorem shape and final summation as two named source premises.

## 6. `proof.activity.termwise-identification`

**Topic:** CMP116 H(Z) activity identification and termwise estimate
**Status:** `source_to_lean_dictionary_blocker`

**Target shape:**

```text
physicalActivity(Z).globalEval psi phi = balabanCMP116H R Z psi phi and each summand norm <= termWeight
```

**Inspect source keys first:**
  - cmp116.localized-activity.2.7-2.10
  - cmp116.lemma3.window.2.14-2.38
  - crosswalk.gaussian-root-activity-route

**Live hypotheses / blockers:**
  - CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification
  - CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate

**Removes:**
  - manual hglobal activity identification
  - manual hterm termwise norm estimate

**Lean targets:**
  - CMP116Lemma3ActivityTermwiseScaleBoundary
  - cmp116Lemma3ActivityEstimateScaleFamily_of_resummation
  - PhysicalGaugeLocalActivity.globalEval

**Dependencies/open questions:**
  - source H(Z,Z0)/H(Z) localization
  - finite resummation dictionary
  - complex norm termwise estimate

**Do not:**
  - Do not use final Lemma 3 bound to backfill termwise estimates.

**Next action:** Extract H(Z) finite-sum dictionary around CMP116 (2.7)-(2.14), then feed termwise estimates around (2.14)-(2.38).

## 7. `proof.gaussian.root.localization-certificate`

**Topic:** Gaussian pushforward and covariance-root localization certificate
**Status:** `source_to_lean_dictionary_blocker`

**Target shape:**

```text
map(dmu0, gaussianRootMap(root)) = physicalGaussian and localized root/covariance bounds hold
```

**Inspect source keys first:**
  - cmp116.gaussian-pushforward.2.5-2.6
  - cmp116.localized-activity.2.7-2.10
  - cmp95.covariance-green.bounds-source-target
  - cmp96.one-step-covariance-law-source-target

**Live hypotheses / blockers:**
  - gaussian_pushforward
  - root_localization
  - PhysicalLocalizedCovarianceRootCertificate

**Removes:**
  - manual Gaussian/root/source package fields

**Lean targets:**
  - PhysicalLocalizedCovarianceRootCertificate
  - PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward
  - balabanCMP116Dmu0

**Dependencies/open questions:**
  - coordinate dictionary
  - Jacobian/normalization
  - CMP95/CMP96 covariance bounds
  - resolvent/root localization

**Do not:**
  - Do not treat CMP116 (2.5)-(2.6) as determinant normalization or coordinate dictionary by itself.

**Next action:** Create CMP95/CMP96 structured catalogs, then link root localization to CMP116 activity construction.

## 8. `proof.dimock.appendixf.hsharp-feed`

**Topic:** Dimock Appendix F H# route into hole-cluster machinery
**Status:** `partially_source_extracted`

**Target shape:**

```text
|H#(Y)| <= O(1)*H0*exp(-(kappa-3*kappa0-3)*d_M(Y, mod Omega^c))
```

**Inspect source keys first:**
  - crosswalk.dimock.appendixf-hole-cluster-route
  - dimockii.appendix-f.cluster-with-holes
  - dimockii.appendix-f.second-ursell.642-646

**Live hypotheses / blockers:**
  - activity bound |H(X)| <= H0 exp(-kappa d_M)
  - H0 <= c0
  - kappa >= 3*kappa0+3
  - modified metric summability

**Removes:**
  - manual cluster-with-holes package once activity estimate is supplied

**Lean targets:**
  - omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound
  - balabanCMP116AppendixFHsharpOfIntegratedKsharp
  - appendixFHoleExpWeight

**Dependencies/open questions:**
  - activity/locality estimate
  - Omega-connectivity relation
  - skeleton metric dictionary

**Do not:**
  - Do not replace Omega-connectivity by ordinary polymer overlap.

**Next action:** Use Batch 001 Dimock extraction as stable; focus on feeding the activity bound from CMP116/Balaban.

## 9. `proof.cmp122.r-operation-polymer-local-bound`

**Topic:** CMP122-I/II and CMP119 localized R-operation bounds
**Status:** `located_not_fully_extracted`

**Target shape:**

```text
|R'^(k)(X,(U,J))| <= exp(-p0(g_k))*exp(-kappa*d_k(X)); |R^(j)(X)| <= g_j^kappa0*exp(-kappa*d_j(X))
```

**Inspect source keys first:**
  - cmp119.r-term-bound.2.31
  - cmp122i.large-field-c-bound.1.70
  - cmp122ii.rprime-bound.1.98-1.100
  - crosswalk.r-operation-polymer-local-route

**Live hypotheses / blockers:**
  - RawYMActivityDecay
  - polymer-local R/B/C source bounds
  - large-field dictionary

**Removes:**
  - surrogate scalar R_k <= M r^k when replaced by faithful polymer-local bound plus flow bridge

**Lean targets:**
  - RawYMActivityDecay
  - future_R_operation_bound
  - CMP116RawSourceM3Frontier

**Dependencies/open questions:**
  - CMP122-I/II theorem extraction
  - source-to-Lean polymer metric
  - large-field operation dictionary

**Do not:**
  - Do not call the polymer-local bound a global scalar mass-gap estimate.

**Next action:** Extract CMP122-I Eq. (1.70) and CMP122-II Eqs. (1.98)-(1.100) into source_extracted entries.

## 10. `proof.flow.ir.bridge`

**Topic:** Flow and IR bridge separating marginal logarithmic flow from irrelevant geometric contraction
**Status:** `conceptual_bridge_blocker`

**Target shape:**

```text
marginal g_k decays logarithmically; geometric r^k belongs to irrelevant remainders/operators, not the gauge coupling itself
```

**Inspect source keys first:**
  - crosswalk.flow-ir-asymptotic-freedom-route

**Live hypotheses / blockers:**
  - coupling flow assumptions
  - ir_bound
  - geometric contraction of irrelevant operators

**Removes:**
  - misuse of g_k <= C*r^k for 4D marginal gauge coupling

**Lean targets:**
  - CouplingFlow.logistic_geometric_decay
  - remainder_geometric_of_logistic
  - BalabanCMP116SourceAssumptions.coupling_recursion
  - BalabanCMP116SourceAssumptions.ir_bound

**Dependencies/open questions:**
  - CMP109/CMP119 beta-function source
  - irrelevant operator scaling theorem
  - IR covariance decay

**Do not:**
  - Do not assume g_k <= C*r^k for 4D marginal Yang-Mills coupling.

**Next action:** Catalog exact beta-flow formulas and separate them from the already-formal irrelevant logistic surrogate.

## 11. `proof.source-status-promotion.gates`

**Topic:** Quality gates for promoting a citation to source_extracted/theorem_checked
**Status:** `process_guardrail`

**Target shape:**

```text
source_extracted requires exact formula, assumptions, quantifiers, constants, dictionary and do_not_use checks; theorem_checked requires compiled Lean/oracle check for the named consumer
```

**Inspect source keys first:**
  - docs.SOURCE-CITATIONS
  - docs.source-db.README

**Live hypotheses / blockers:**
  - source_pending entries
  - ocr_corrupted entries
  - visual_confirmed but not theorem-feedable entries

**Removes:**
  - false progress from plausible OCR or theorem-looking wrappers

**Lean targets:**
  - source_db.verify
  - source_db.build
  - oracle_check.lean

**Dependencies/open questions:**
  - artifact hash
  - visual page confirmation
  - local_text/render locator
  - Lean target link

**Do not:**
  - Do not promote visual_confirmed to source_extracted just because the formula shape is useful.

**Next action:** Use the promotion checklist before every source-db commit.

## 12. `proof.final-frontier.pipeline`

**Topic:** End-to-end source frontier pipeline from CMP116 Lemma 3 to raw-source M3 frontier
**Status:** `aggregate_route`

**Target shape:**

```text
source-fed Eq229 + Eq231 + Eq237 + termwise/activity + Gaussian/root/Hessian/H# + flow/IR -> raw-source M3 frontier
```

**Inspect source keys first:**
  - crosswalk.final-frontier-pipeline
  - cmp116.lemma3.final-2.38
  - cmp116.effective-action.2.39-2.41

**Live hypotheses / blockers:**
  - Eq. (2.29)
  - Eq. (2.31)
  - Eq. (2.37)
  - activity/termwise
  - Gaussian/root/Hessian/H#
  - flow and IR

**Removes:**
  - manual CMP116RawSourceM3Frontier fields only after all upstream cards close

**Lean targets:**
  - CMP116RawSourceM3Frontier
  - BalabanCMP116SourceTheorem
  - CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237

**Dependencies/open questions:**
  - all higher-priority proof cards

**Do not:**
  - Do not claim Clay or full source closure from an aggregate route; close named hypotheses one by one.

**Next action:** Use this only as a dashboard; implement the smallest upstream source theorem first.
