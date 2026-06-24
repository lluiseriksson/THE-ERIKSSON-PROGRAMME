# Dimock-Balaban Source-Claim Audit for the P3/P4 Frontier

**Repository:** `lluiseriksson/THE-ERIKSSON-PROGRAMME`  
**Document status:** adversarial documentation only; not a Lean theorem and
not source evidence by itself  
**Audit date:** 2026-06-20  
**Last updated:** 2026-06-24
**Live code reference:** `337025aadd8f80810cdf676f2612ca0944281c9a`
**Primary frontier:** `hRpoly`, the concrete single-scale Yang-Mills
activity-decay estimate for the actual gauge RG operator

## Purpose

This file is a source-claim ledger for the P3/P4 constructive-QFT frontier.
It exists to prevent three failure modes:

1. attributing a theorem to the wrong paper or model;
2. turning a source-level analytic obligation into a hollow Lean interface;
3. importing scalar-model constants, support conventions, or covariance
   assumptions into four-dimensional Yang-Mills without proof.

This document does **not** claim construction of continuum Yang-Mills, an
Osterwalder-Schrader or Wightman reconstruction, a continuum spectral gap,
completion of `hRpoly`, or permission to use a `source-pending` statement as a
Lean theorem hypothesis under a new name.  The verified core remains governed
by the compiler, the consistency checker, and `#print axioms`.

## Place In The Repository

This audit complements, rather than replaces:

| File | Responsibility |
|---|---|
| [`CURRENT-STATE.md`](../CURRENT-STATE.md) | What Lean currently proves |
| [`HYPOTHESIS_FRONTIER.md`](../HYPOTHESIS_FRONTIER.md) | What remains a theorem hypothesis |
| [`docs/BALABAN-SOURCE-BOUNDS.md`](BALABAN-SOURCE-BOUNDS.md) | Positive source transcriptions and quantitative anchors |
| `docs/SOURCE-CLAIM-AUDIT.md` | Contradicted claims, pending claims, provenance, and extraction requirements |
| [`docs/VERIFICATION-LEDGER.md`](VERIFICATION-LEDGER.md) | Build/oracle-certified theorem additions |

No import should be added to `YangMillsCore.lean` for this document, and no
entry belongs in `oracle_check.lean`.

## Live P3/P4 Mapping

At the live code reference above, the finite Appendix-F layer is stronger than
older drafts of this audit assumed.

### P3 Already Theorem-Fed

The following finite, source-shaped components are present:

* exact finite raw Mayer expansion;
* canonical `Omega`-connected components;
* target-cover families and their inverse;
* source-faithful two-support handling:
  * active skeletons determine `Omega`-connectedness;
  * full polymer unions determine the target `Y`;
* exact finite target-family/Fubini reindexing;
* exact finite hard-core partition identity for the first activity;
* a finite norm majorant for the first connected activity:

  ```text
  ||K(Y)|| <=
    sum over connected C with union target Y of
      (2H0)^|C| * exp(-kappa * sum_X metric X)
  ```

* finite with-holes metric stitching for the repository's discrete modified
  metric:

  ```text
  d_M(Y, mod holes) + 1 <= sum_X (d_M(X, mod holes) + 1).
  ```

Relevant modules include:

```text
YangMills/RG/AppendixFFiniteCover.lean
YangMills/RG/AppendixFHoleTarget.lean
YangMills/RG/AppendixFHoleTargetFamily.lean
YangMills/RG/AppendixFQuantitative.lean
```

Headline finite metric-stitching theorems include:

```text
YangMills.RG.discreteModifiedMetric_add_one_le_card_of_spanning_set
YangMills.RG.appendixFHoleCoverUnion_discreteModifiedMetric_add_one_le_sum
YangMills.RG.appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum
```

### P3 Still Open

The source audit must now support these precise obligations:

1. the connected-cover entropy/summation argument producing Dimock II
   Appendix F equation (642):

   ```text
   |K(Y)| <= C_K H0 * exp(-(kappa - kappa0 - 2) d_M(Y, mod Omega^c)).
   ```

2. type-local and measurable construction of `K(Y, psi, phi)`;
3. ultralocal integration:

   ```text
   K#(Y, psi) = integral K(Y, psi, phi) dmu_Lambda(phi);
   ```

4. the second Ursell expansion defining `H#(Y)`;
5. the final Dimock loss:

   ```text
   |H#(Y)| <= C_F H0
     * exp(-(kappa - 3*kappa0 - 3) d_M(Y, mod Omega^c)).
   ```

The finite geometric content corresponding to the shape of equation (641) is
now theorem-fed in the repository.  The source packet around (641)--(642) is
still needed for constants, quantifier order, smallness restrictions, and the
transition from the finite target-fiber sum to a closed activity bound.

### P4 Still Open

No source audit may conceal the model-specific obligations:

* the actual Balaban block RG operator;
* the background minimizer and gauge slice;
* the gauge-fixed Hessian and its coercivity;
* the true fluctuation covariance and its localization;
* exact support locality of the resulting gauge activity;
* the small-/large-field decomposition;
* the `R`-operation and coupling-power gain;
* the raw Yang-Mills activity bound;
* the exact identity relating the activity sum to the concrete `Rsc`.

## Status Taxonomy

### Original-Claim Status

| Value | Meaning |
|---|---|
| `contradicted` | The cited primary source says something materially different |
| `unsupported` | No inspected primary passage supports the claim |
| `pending` | Plausible target, but the exact primary passage has not been extracted |

### Replacement/Extraction Status

| Value | Meaning |
|---|---|
| `primary-verified` | The corrected mathematical statement was checked against the primary text |
| `source-extracted` | A bounded excerpt, hypotheses, and equation data have been transcribed |
| `source-pending` | The row is only an extraction target; it is not available for proof use |

### Source Scope

| Value | Meaning |
|---|---|
| `exact theorem` | A specific theorem/equation has been checked |
| `paper-level extraction target` | The paper is relevant, but the formalizable statement remains to be extracted |
| `methodological analogue` | The source suggests a proof pattern but is not a theorem for this repository model |

### Local Archive Status

Mathematical verification and local archival provenance are separate fields.
Allowed local-archive values:

```text
archived_sha256
pending_local_ingest
external_primary_only
```

## Provenance Schema

Every source-extracted row should eventually record:

| Field | Required content |
|---|---|
| `local_pdf_sha256` | SHA-256 of the exact local primary PDF |
| `pdf_page` | Page number in the PDF viewer |
| `printed_page` | Printed journal/page number where applicable |
| `transcribed_range` | Exact theorem/equation range and surrounding hypotheses |
| `constants_uniformity` | Dependence on dimension, block scale, coupling, volume, RG scale, regions, and background |
| `support_scope` | Full support, active support, fluctuation support, or a fixed enlargement |
| `model_scope` | Scalar `phi^4_3`, pure lattice gauge theory, QED, or another model |
| `Lean_consumer` | Concrete theorem/module that will consume the extracted statement |

External URLs are bibliographic pointers, not proof evidence.

## Verified Dimock Corrections

### D1 - Dimock I, Appendix B, Theorem 27

| Field | Value |
|---|---|
| Original claim | Theorem 27 is a fermionic/Dirac loop expansion |
| Original status | `contradicted` |
| Verified replacement | Standard ultralocal cluster expansion with the chain `H -> K -> K# -> H#`; equations (296)--(333) culminate in the `H#` estimate |
| Replacement status | `primary-verified` |
| Source scope | `exact theorem` |
| Primary source | J. Dimock, *The Renormalization Group According to Balaban I. Small Fields* |
| Exact range | Appendix B, Theorem 27, equations (296)--(333) |
| Local archive | `pending_local_ingest` |
| Model/constants | scalar `phi^4_3`; constants are not Yang-Mills constants |
| Lean consumer | `appendixFConnectedActivity_norm_le`, future `appendixFEffectiveActivity_norm_le`, future `dimockF1_clusterExpansionWithHoles` |

### D2 - Dimock I, Lemma 6

| Field | Value |
|---|---|
| Original claim | Lemma 6 is a Dirac/fermionic random-walk expansion |
| Original status | `contradicted` |
| Verified replacement | Random-walk expansion for the scalar/bosonic Green operator `G_k = (-Delta + mu_bar_k + a_k Q_k^T Q_k)^-1` |
| Replacement status | `primary-verified` |
| Source scope | `exact theorem` |
| Primary source | J. Dimock, *The Renormalization Group According to Balaban I. Small Fields* |
| Exact range | Lemma 6, equations (83)--(100) |
| Local archive | `pending_local_ingest` |
| Model/constants | scalar operator only |
| Lean consumer | `scalar_green_function_rw`; methodological guide for a future gauge parametrix |

### D3 - Dimock I, Appendix D

| Field | Value |
|---|---|
| Original claim | Appendix D computes Dirac norms with gauge fixing |
| Original status | `contradicted` |
| Verified replacement | Coercivity and Green-function estimates for a scalar operator containing `Q^T Q` |
| Replacement status | `primary-verified` |
| Source scope | `exact theorem` |
| Primary source | J. Dimock, *The Renormalization Group According to Balaban I. Small Fields* |
| Exact range | Appendix D; extract Lemmas 29--30 and equations (342)--(349) |
| Local archive | `pending_local_ingest` |
| Model/constants | scalar pedagogical analogue; no direct 4D gauge constants |
| Lean consumer | `scalar_coercivity_Q_T_Q`; methodological guide for future gauge coercivity |

### D4 - Dimock II, Appendix E, Lemma E.3

| Field | Value |
|---|---|
| Original claim | Lemma E.3 bounds a global/local propagator difference |
| Original status | `contradicted` |
| Verified replacement | Modified-metric polymer summability `sum_{X superset square} exp(-kappa0 d_M(X, mod Omega^c)) <= K0` |
| Replacement status | `primary-verified` |
| Source scope | `exact theorem` |
| Primary source | J. Dimock, *The Renormalization Group According to Balaban II. Large Fields* |
| Exact range | Appendix E, Lemma E.3, equations (627)--(632) |
| Local archive | `pending_local_ingest` |
| Model/constants | scalar hole geometry; compare carefully with the repository's discrete modified metric |
| Lean consumer | existing modified-metric summability; future rooted incompatibility/window bounds |

### D5 - Dimock II, Appendix F

| Field | Value |
|---|---|
| Original claim | Appendix F defines gauge "DEC interfaces" |
| Original status | `contradicted` |
| Verified replacement | Ultralocal cluster expansion with holes: raw `H`, `Omega`-connected covers, `K(Y)`, integrated `K#(Y)`, second Ursell expansion `H#(Y)`, and final decay loss |
| Replacement status | `primary-verified` |
| Source scope | `exact theorem` |
| Primary source | J. Dimock, *The Renormalization Group According to Balaban II. Large Fields* |
| Exact range | Appendix F, equations (633)--(646), Theorem F.1 |
| Local archive | `pending_local_ingest` |
| Model/constants | abstract finite cluster theorem embedded in scalar `phi^4_3`; only the abstract theorem transfers |
| Lean consumer | current Appendix-F compiler; future `K#`, `H#`, metric-loss and F.1 theorems |

Verified semantics:

* connectivity is `X1 ~_Omega X2` iff `X1 cap X2 cap Omega` is nonempty;
* `Omega`-disjoint does not imply full disjointness;
* the target `Y` is the full union of the raw polymers;
* fluctuation factorization uses `Y cap Lambda`;
* the stated final loss is `kappa -> kappa - 3*kappa0 - 3`.

### D6 - Dimock II, Section 3.14

| Field | Value |
|---|---|
| Original claim | Section 3.14 defines a gauge DEC boundary transition |
| Original status | `contradicted` |
| Verified replacement | Scalar/bosonic application after fluctuation localization |
| Replacement status | `primary-verified` |
| Source scope | `exact theorem` |
| Primary source | J. Dimock, *The Renormalization Group According to Balaban II. Large Fields* |
| Exact range | Lemma 3.18, equations (497)--(506) |
| Local archive | `pending_local_ingest` |
| Model/constants | scalar `phi^4_3`; architecture only |
| Lean consumer | model for future localized-fluctuation-to-raw-activity APIs, not a YM theorem |

## Balaban Extraction Queue

Every row in this section is `source-pending` and has source scope
`paper-level extraction target`.  No verified mathematical wording should be
inferred beyond the extraction goal.

### B1 - CMP 95: Propagator Estimates

| Field | Value |
|---|---|
| Pending claim | Propagator on a particular gauge slice with uniform exponential decay |
| Extraction goal | Extract the exact operator, spaces, norms, projectors/gauge conditions, boundary conditions, and estimates around (1.89) and (1.114) |
| Primary source | T. Balaban, *Propagators and Renormalization Transformations for Lattice Gauge Theories I* |
| Lean consumer | `propagator_decay_bounds`; future gauge coercivity/covariance modules |
| Provenance | all local metadata `extraction_pending` |

Do not label the estimate "Combes-Thomas" unless the paper's proof and
hypotheses justify that terminology.

### B2 - CMP 98: Nonlinear Averaging

| Field | Value |
|---|---|
| Pending claim | Linear and nonlinear gauge-covariant block averaging |
| Extraction goal | Extract the exact nonlinear averaging map, gauge covariance, linearization, and powers of `L` in all normalizations |
| Primary source | T. Balaban, *Averaging Operations for Lattice Gauge Theories* |
| Exact target | equations (1)--(5), (11), (14)--(15) |
| Lean consumer | `averaging_gauge_covariance`; identification with existing `Q`/`Ubar` infrastructure |
| Provenance | all local metadata `extraction_pending` |

### B3 - CMP 99 / CMP 102: Background Field And Variational Problem

| Field | Value |
|---|---|
| Pending claim | Gauge slice, regularity domain, background minimizer, Hessian, propagator, and locality |
| Extraction goal | Extract theorem statements, uniqueness domain, gauge freedom, Euler-Lagrange equation, Hessian, and locality/enlargement conventions |
| Primary source | T. Balaban, CMP 99 background-propagator paper and CMP 102 variational/background-field paper |
| Lean consumer | `background_minimizer_propagator` |
| Provenance | all local metadata `extraction_pending` |

### B4 - CMP 109: One-Step Fluctuation Integral

| Field | Value |
|---|---|
| Pending claim | Exact small-field one-step RG fluctuation identity |
| Extraction goal | Extract the coordinate map, normalized blocking identity, Jacobian, gauge fixing, Hessian, nonlinear remainder, cutoff domain, and activity norm |
| Primary source | T. Balaban, *Renormalization Group Approach to Lattice Gauge Field Theories I* |
| Exact target | equations (0.5)--(0.12) and the complete defining sections |
| Lean consumer | `fluctuation_integral_step`; future `ymOneStep_fluctuationIdentity` |
| Provenance | all local metadata `extraction_pending` |

Do not attribute the systematic cluster exponentiation to CMP 109 alone; CMP
116 is the dedicated cluster-expansion sequel.

### B5 - CMP 116: Localized Cluster Activity And Lemma 3

| Field | Value |
|---|---|
| Pending claim | Local support and decay of the one-step cluster activity |
| Extraction goal | Extract component support dependence, target enlargements, Lemma 3/(2.38), its hypotheses, and the post-Lemma bridge (2.39)--(2.41) |
| Primary source | T. Balaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions* |
| Exact target | PDF pp. 4--5 and 18--21; equations (2.27), (2.29), (2.30), (2.32), (2.36), (2.38)--(2.41) |
| Lean consumer | `balabanLemma3_rawActivityDecay` |
| Provenance | all local metadata `extraction_pending` |

The current source-facing goal is the localized `H(Z)` bound, not merely a
scale-distance inequality.

### B5a - CMP 116: Product Gaussian Change Of Variables

| Field | Value |
|---|---|
| Extracted claim | In the localized cluster-expansion integral for a fixed domain `Z0`, Balaban conditions the correlated fluctuation Gaussian, then makes the linear change of variables `B' = (C^(k))^(1/2) X`; the resulting integral is written against the ultralocal product standard Gaussian `dmu0(X)` and a new function `G` absorbing the covariance/root-dependent factors |
| Replacement status | `source-extracted` |
| Source scope | `exact theorem/equation range`, not a completed Lean theorem |
| Primary source | T. Balaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, Comm. Math. Phys. 116 (1988), 1--22 |
| Local PDF | `runtime/sources/primary/balaban-rg-II-cmp116-1104161193.pdf` |
| `local_pdf_sha256` | `EE39523A0F7B83AF958513C7BD6F9C7731934B40355EF5D6B0F7A68EE6D022FC` |
| PDF / printed pages | PDF pages 12--13, printed pages 12--13 |
| Exact range | equations (2.5)--(2.6), plus the paragraph beginning "In the integral with respect to B'..." and the paragraph after (2.6) |
| Surrounding hypotheses | The term has first been localized by choosing a subfamily `D`, target union `Y0`, bond set `Y0^c*`, and smallest localization domain `Z0`; the integral is then represented by conditioning on `Z0^c` before the `B'`-change |
| Measure convention | `dmu0` is the product standard Gaussian over the `X(b)` variables, displayed with density `dX(b) exp(-|X(b)|^2/2)/(2*pi)^(dim(g)/2)` in (2.6); the correlated covariance is not an independence statement but is moved into the integrand through `(C^(k))^(1/2)` and `G` |
| Support/locality convention | The expression after (2.6) still depends on whole-lattice external gauge fields through propagators and operators in `G`; Balaban then re-localizes it by parameters `s`, generalized random-walk expansions, and an expansion of `(C^(k))^(1/2)` beginning with (2.7) |
| Constant/uniformity data | This extraction records the exact measure conversion and localization target only; constants and smallness restrictions for the subsequent bound still come from the later estimates around Lemma 3, especially (2.27), (2.29), (2.30), (2.32), (2.36), and (2.38)--(2.41) |
| Model scope | four-dimensional lattice gauge theory in Balaban's CMP 116 notation |
| Lean consumer | `PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward`, `PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange.ofDictionaryRoot`, and the `balabanCMP116Dmu0` product-Gaussian side |
| Remaining unproved bridge | Identify Balaban's `B'`, `X`, `C^(k)`, and `(C^(k))^(1/2)` with the repository's physical cochain coordinates, `CMP116FluctuationField`, `PhysicalGaugeCMP116Dictionary.gaussianRootMap root`, and `physicalGaussian`; account for determinant/Jacobian normalization; and translate the post-(2.6) localization into the existing `LocalActivity.fluctuationSupport`/`activeSupport` interfaces |

This row is enough to justify the source-targeted product-Gaussian interface.
It is **not** enough to discharge Lean's `gaussian_pushforward` field by itself:
that field still needs the coordinate/dictionary identification and the exact
normalization convention for the finite-dimensional physical Gaussian.

### B5b - CMP 116: Post-Gaussian Localization Of The Root Map

| Field | Value |
|---|---|
| Extracted claim | After the product-Gaussian change of variables, the integrand still depends on whole-lattice external gauge fields through propagators and operators in `G`; Balaban then introduces localization parameters `s`, constructs generalized random-walk expansions with a special localization domain containing `Z0`, expands `(C^(k))^(1/2)` through a resolvent/series formula, and obtains localized activities `H(Z,Z0)` and `H(Z)` |
| Replacement status | `source-extracted` |
| Source scope | `exact theorem/equation range`, not a completed Lean theorem |
| Primary source | T. Balaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, Comm. Math. Phys. 116 (1988), 1--22 |
| Local PDF | `runtime/sources/primary/balaban-rg-II-cmp116-1104161193.pdf` |
| `local_pdf_sha256` | `EE39523A0F7B83AF958513C7BD6F9C7731934B40355EF5D6B0F7A68EE6D022FC` |
| PDF / printed pages | PDF pages 13--14, printed pages 13--14 |
| Exact range | paragraph after (2.6), equation (2.7), the paragraph following (2.7), and equations (2.8)--(2.10) |
| Surrounding hypotheses | The domain `Z0` has already been selected by the Mayer/localization decomposition, and the product-Gaussian representation (2.6) has already moved covariance-root dependence into `G(Z0,X,C^(k)(Z0),(C^(k))^(1/2),Delta_k)` |
| Root/localization convention | The expansion of `(C^(k))^(1/2)` is not asserted as finite-range equality.  Balaban uses a resolvent integral/series representation and generalized random-walk expansions; the domains are unions of connected `M1`-cubes, one chosen domain has enlarged support containing `Z0`, and other localization domains are separated from `Z0` before the random-walk expansion is applied |
| Activity-locality convention | Equations (2.8)--(2.9) rewrite the product-Gaussian integral as a sum of localized quantities `H(Z,Z0)` and then `H(Z)`.  The text then states that `H(Z)` is localized in the interior of `Z` with respect to the external gauge fields and records the component factorization (2.10) |
| Lean consumer | `PhysicalRootToCMP116OperatorTransport.gaussianRootMap_activity_globalEval_eq_of_agreeOn_of_localizedRootLinearMapFinsetSum` through its source-side `hrootPieces` hypothesis; later `local_physical_activity_construction`, `fluctuation_support_subset`, and Appendix-F support transport |
| Remaining unproved bridge | Translate Balaban's enlarged domains, `M1`-cube random-walk supports, and "localized in the interior of Z" statement into explicit `LocalActivity.fluctuationSupport` and `activeSupport` subsets; identify the expanded `(C^(k))^(1/2)` root pieces with the repository's finite `localizedRootLinearMapFinsetSum_ofDictionary`; quantify the truncation/error or infinite-series summation needed before Lean can instantiate `hrootPieces` |

This row is the source anchor for the new activity-local root bridge.  It
supports the shape of the `hrootPieces` hypothesis, but it does **not** prove
that hypothesis: the repository still needs an exact domain-translation theorem
and a finite/infinite root-piece reconstruction statement compatible with the
Lean support interfaces.

### B5c - CMP 116: Resummed Activity Estimate Versus Root-Piece Reconstruction

| Field | Value |
|---|---|
| Extracted claim | The estimates after (2.14) bound the resummed localized activity `H(Z)` obtained from the generalized random-walk/localization expansion; they do not state an exact finite root-piece reconstruction of `(C^(k))^(1/2)` |
| Replacement status | `source-extracted` |
| Source scope | `exact theorem/equation range`, not a completed Lean theorem |
| Primary source | T. Balaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, Comm. Math. Phys. 116 (1988), 1--22 |
| Local PDF | `runtime/sources/primary/balaban-rg-II-cmp116-1104161193.pdf` |
| `local_pdf_sha256` | `EE39523A0F7B83AF958513C7BD6F9C7731934B40355EF5D6B0F7A68EE6D022FC` |
| PDF / printed pages | PDF pages 15--20, printed pages 15--20 |
| Exact range | equations (2.14)--(2.38), especially the resummations using (2.27), (2.29)--(2.32), (2.34), (2.36), (2.37), and Lemma 3 / (2.38) |
| Estimate structure | A typical term is written in (2.14), bounded in (2.26), then resummed over `D`, `P`, `Z0`, and `Z0'`.  The proof extracts small factors such as `alpha_6 exp(-delta kappa d_k(Y))`, uses the summability input (2.29), geometric inequalities (2.27), (2.30), (2.32), and the scale-transfer inequality (2.36), and ends with Lemma 3's bound for `H(Z)` |
| Equation (2.29) Lean status | `YangMills.RG.BalabanCMP116Eq229` records the product-summability shape `sum_D prod_{Y in D} alpha_6 exp(-delta*kappa*d_k(Y)) <= 1` from PDF/printed page 18, proves the local D-stage consumer `cmp116_DStage_sum_le_of_eq229`, proves `cmp116H_termWeightSum_le_of_eq229`, which converts a residual post-D `P/Z0/Z0'` bound plus (2.29) into the finite Lemma-3 `hbudget` shape, exposes `cmp116Lemma3ActivityEstimate_of_eq229_postD` as the corresponding theorem-fed activity-estimate consumer, and has a pointwise scale-family lift `cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_postD`; it does not prove Balaban's large-`K`, small-`alpha_6` assertion or the residual post-D estimates |
| Lean-facing verdict | This source range supports the `raw_pointwise_decay` / `local_physical_activity_construction` side of the CMP116 source package more directly than it supports an exact finite `localizedRootLinearMapFinsetSum` reconstruction theorem.  A finite Lean root-piece sum should therefore be treated as a truncation or auxiliary approximation unless an additional source theorem proves exact activity-support equality |
| Remaining unproved bridge | Extract the exact constant hierarchy (`epsilon_2`, `C_3`, smallness of `(L+2)^4 O(1) epsilon_2`, `2 (L+2)^4 O(1) epsilon_2 exp(5 kappa) <= 1`, `(kappa_1 - 1)/2 >= 2 L kappa`, and boundedness assumptions for `(LM)^4 alpha_i`/`gamma_i`) and map Lemma 3's `H(Z)` to the repository's `PhysicalGaugeLocalActivity.globalEval` plus support fields |

This row resolves the immediate reconstruction-design question negatively for
the current source evidence: pages 15--20 prove a localized activity estimate
after resummation, not exact equality of a finite root-piece operator with the
full covariance root on an activity support.

### B5d - CMP 116: Post-Lemma-3 Effective-Action Bound

| Field | Value |
|---|---|
| Extracted claim | Lemma 3's localized activity bound is converted into the effective-action bound by estimating the exponentiated polymer series and then fixing the final `delta,L` and `C_3 epsilon_1` smallness assumptions |
| Replacement status | `source-extracted` |
| Source scope | `exact theorem/equation range`, not a completed Lean theorem |
| Primary source | T. Balaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, Comm. Math. Phys. 116 (1988), 1--22 |
| Local PDF | `runtime/sources/primary/balaban-rg-II-cmp116-1104161193.pdf` |
| `local_pdf_sha256` | `EE39523A0F7B83AF958513C7BD6F9C7731934B40355EF5D6B0F7A68EE6D022FC` |
| PDF / printed page | PDF page 21, printed page 21 |
| Exact range | equations (2.39)--(2.41) and the following paragraphs through the discussion of the extra `[log Z^(k)(U_{k+1}) - log Z^(k)(1)]` term |
| Estimate structure | Starting from products of Lemma 3 factors inside the polymer expansion, (2.39) extracts an exponential from each factor and uses connectedness of the union.  Equation (2.40) invokes the standard polymer-series bounds for large `kappa` and small `epsilon_1`.  Equation (2.41) gives the effective-action estimate `|E^(k+1)(X)| <= O(1) C_3 epsilon_1 exp (-(1 - 10 delta)^(1/2) L kappa d_{k+1}(X))` |
| Final assumptions | The text then fixes `(1 - 10 delta)^(1/2) L = 1`, equivalently `delta = (1/10) * (1 - 2 * L^(-1))`, and assumes `O(1) C_3 epsilon_1 <= (1/2) E_0`; the added normalization term from `[log Z^(k)(U_{k+1}) - log Z^(k)(1)]` is handled by a separate generalized random-walk expansion with `kappa` replaced by `delta_0 M`, choosing `(1/2) E_0` to cover that absolute constant and `M` so that `delta_0 M >= kappa` |
| Lean-facing verdict | This is the source bridge from Lemma 3's `H(Z)` bound to the inductive effective-action bound `(I.1.18)`.  A Lean interface should expose it as a polymer-series/effective-action consumer of the localized `H(Z)` estimate, not as part of the covariance-root reconstruction story |
| Remaining unproved bridge | Formalize the exact polymer-series summability hypotheses behind the reference to [26], track the `O(1)` constants and the split of the `E_0` budget, and identify the added `log Z` normalization terms with the repository's effective-action/activity representation |

This row isolates the post-Lemma-3 consumer needed after a future Lean theorem
constructs the concrete `H(Z)` local activities and proves Lemma 3's bound.

### B6 - CMP 119: Localized `E/R/B` Decomposition

| Field | Value |
|---|---|
| Pending claim | Localized remainder and boundary activities |
| Extraction goal | Extract the `E/R/B` domain decomposition, support dependence, equation (2.31) for `R^(j)`, and equation (2.42) for boundary `B^(j)` |
| Primary source | T. Balaban, *Convergent Renormalization Expansions for Lattice Gauge Theories* |
| Exact target | printed pp. 257--261; equations (2.31), (2.42) |
| Lean consumers | `balabanRActivity_decay`, `balabanBoundaryActivity_decay` |
| Provenance | all local metadata `extraction_pending` |

Do not describe (2.31) or (2.42) as Euclidean covariance statements.

### B7 - CMP 122 I--II: Large-Field `R`-Operation

| Field | Value |
|---|---|
| Pending claim | Localized large-field activities and their final decay |
| Extraction goal | Extract the `R`-operation, `C_k^(n)`, `R'^(k)`, placement entropy, boundary separation, and all hypotheses of (1.70), Theorem 1, and (1.98)--(1.100) |
| Primary source | T. Balaban, *Large Field Renormalization I* and *II* |
| Lean consumers | `balabanRprimeActivity_decay`, `ymLargeFieldPlacementSum_le` |
| Provenance | all local metadata `extraction_pending` |

Do not relabel these local activity estimates as a global scalar mass-gap
estimate.

## Primary-Source Extraction Priorities

Because the finite cover compiler, first norm majorant, pinned localization,
and finite metric stitching are already proved, the next source packet should
be ordered as follows.

### Priority 1 - Complete P3 Entropy And Integration Bookkeeping

Request:

1. Dimock II Appendix F, equations (637)--(646), including all prose around
   (641)--(642).  The finite geometry corresponding to (641) is already
   theorem-fed; the source is now needed for constants, summability, and the
   passage to (642).
2. Dimock I Appendix B, equations (303)--(333), with all smallness
   restrictions.
3. Dimock II Appendix E, Lemma E.3, including constant dependence and hole
   assumptions.

This packet feeds:

```text
appendixFConnectedActivity_norm_le
appendixFIntegratedActivity
appendixFEffectiveActivity
dimockF1_clusterExpansionWithHoles
```

### Priority 2 - Define The Real P4 Source Activity

Request:

1. CMP 116 component locality and Lemma 3.
2. CMP 109 exact one-step fluctuation identity.
3. CMP 119 localized `R/B` terms.
4. CMP 122 large-field terms and entropy.

### Priority 3 - Construct The Actual Gauge Covariance

Request:

1. CMP 95 propagator definitions and estimates.
2. CMP 98 averaging normalization.
3. CMP 99/102 gauge slice, minimizer, Hessian, and background propagator.

## Known Semantic Mismatches

### Scalar `phi^4_3` Versus Four-Dimensional Yang-Mills

Dimock I/II are scalar three-dimensional models.  Their abstract cluster
combinatorics and proof architecture may transfer; their amplitudes, scaling
dimensions, Hessians, counterterms, and constants do not.

Guardrail: every model-specific constant must carry `model_scope`.

### Active Support Versus Full Target Support

Appendix F uses three distinct roles:

```text
active support       = X cap Omega
full target support  = X
fluctuation support  = X cap Lambda
```

Guardrail: never replace the full target `Y = union_i X_i` by the union of
active skeletons.

Current Lean interface note: at `9c2f42c`,
`BalabanCMP116AppendixFSupportHypotheses` asks the source side only for
`F.activeSupport X subset skeleton HF X.val`.  The theorem
`BalabanCMP116AppendixFSupportHypotheses.activeSupport_subset_full` derives
`F.activeSupport X subset X.val` from that skeleton fact and `skeleton_subset`.
Do not list full-target containment as an independent CMP116 source obligation
unless a later consumer requires a stronger enlargement convention.

The same support package now also supplies the one-way hard-core graph
adapter:
`BalabanCMP116AppendixFSupportHypotheses.omegaGraph_adj_imp_skeletonOverlapGraph_adj_of_supportHypotheses`
maps CMP116 `F.omegaGraph` edges into the Appendix-F skeleton-overlap graph
using only active-skeleton support.  This is finite graph bookkeeping, not a
source proof of CMP116 localization.

It also supplies the factorization-facing no-cross-edge form:
`BalabanCMP116AppendixFSupportHypotheses.not_omegaGraph_adj_of_disjoint_skeleton_of_supportHypotheses`.
If the Appendix-F active skeletons are disjoint, the contained CMP116 active
supports cannot overlap inside `F.Omega`, so `F.zeta = 1` and no CMP116
Ω-overlap edge is present.

The current support adapter also accepts the source-facing clipped form
`F.Omega = HF.omegaRegion` and
`F.activeSupport X subset X.val inter F.Omega`, proving the required skeleton
support package by the finite identity
`skeleton HF X.val = X.val inter HF.omegaRegion`.  Under equality, Lean also
identifies the CMP116 hard-core graph with the Appendix-F skeleton-overlap
graph; under inclusion alone, Lean proves only the safe direction from CMP116
Omega-overlap edges to Appendix-F skeleton-overlap edges.  Therefore a source
phrase such as "localized in the interior of Z" must still be translated into
one of these exact support statements before it can discharge the hypothesis.

### `Omega`-Disjoint Versus Fully Disjoint

Two target polymers may overlap inside holes while being `Omega`-disjoint.
Factorization must be justified through disjoint fluctuation supports in
`Lambda subset Omega`, not through full-set disjointness.

### Product Measure Versus Correlated Gaussian

Appendix F's factorization uses an ultralocal product measure.  Exponential
covariance decay does not imply exact independence.  P4 must provide either an
exact ultralocal representation with nonlocality moved into activities, or a
different theorem with an explicit factorization defect.

CMP 116 equations (2.5)--(2.6) provide the source-side route for the first
option: after conditioning the correlated fluctuation Gaussian on a localized
domain, Balaban changes variables by `B' = (C^(k))^(1/2) X`, defines the product
standard Gaussian `dmu0(X)`, and moves the nonlocal covariance/root dependence
into `G`.  Therefore the Lean route should keep `balabanCMP116Dmu0` product-like
and treat the covariance root as part of the coordinate map/integrand, not infer
independence from covariance decay.

### Source Metric Versus Repository Metric

Similarity between two "modified metrics" is insufficient.  Prove equality or
an explicit comparison theorem with tracked exponent loss.

### Bare Support Versus Fixed Enlargements

Balaban's local terms may depend on a component plus a base cube or collar.
Record the exact enlargement in `support_scope`; do not erase it from
`LocalActivity.fluctuationSupport`.

### Local Polymer Bounds Versus Scalar `hRpoly`

Balaban's source bounds are polymer-local.  A scalar estimate requires
summation, source separation, and an exact definition of `Rsc`.

Guardrail: do not state `SingleScaleUVDecay` until the concrete scale
contribution has been identified.

### Constant Uniformity

A bound valid at fixed volume or fixed scale does not feed the desired route.
Record quantifier order and independence from volume, RG scale, `Lambda`,
`Omega`, and background values.

## Status-Update Protocol

A coding or source-extraction agent may change a row from `source-pending`
only after all of the following are supplied:

1. exact primary PDF identity;
2. `local_pdf_sha256` or an explicit `external_primary_only` marker;
3. PDF and printed page numbers;
4. theorem/equation range;
5. surrounding hypotheses;
6. support convention;
7. constant dependencies and uniformity;
8. model scope;
9. a concrete Lean consumer;
10. a statement of what remains unproved after extraction.

A source extraction is not a Lean proof.  The corresponding analytic result
remains open until implemented and oracle-checked.

## CMP116 Residual-Stage Interface

`YangMills.RG.BalabanCMP116Lemma3ResidualStages` is an algebraic interface for
the residual CMP116 Lemma-3 resummation after the equation-(2.29) D-stage has
been isolated.  It names the source-neutral predicates
`CMP116PResidualSummability`, `CMP116Z0ResidualSummability`, and
`CMP116Z0PrimeResidualSummability`, proves
`cmp116H_postD_sum_le_of_residualStages`, and then composes with the existing
Eq. (2.29) consumer through
`cmp116H_termWeightSum_le_of_eq229_of_residualStages`.

This interface does **not** identify those predicates with CMP116 equations
(2.27), (2.30), (2.32), (2.34), (2.36), or (2.37), and it does **not** prove
the source constants or smallness conditions.  A future source extraction must
still supply the normalized `P`, `Z0`, and `Z0'` residual estimates and the
pointwise term-weight factorization from the primary text.

The scale-family theorem
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_residualStages` is the same
composition pointwise in `(t, k)`.  Its named `postDBase` equality is
bookkeeping for the Eq. (2.29) product-weight base, not evidence for any
residual source estimate.

`YangMills.RG.BalabanCMP116Eq229` also exposes the smaller budget-valued
predicate `CMP116PStageSummability` and the helper
`cmp116H_postDSum_le_of_pStage`.  This only proves that an explicit P-stage
budget plus a fixed-P nested `Z0/Z0'` residual estimate recovers the old
post-D `hpostD` bound.  It is not named after Eq. (2.30), and this audit does
not claim that Eq. (2.30) alone proves the predicate.

`YangMills.RG.BalabanCMP116Lemma3ResidualStages` now also exposes the matching
fixed-P residual bridge `cmp116H_postP_sum_le_of_residualStages` and the
composed consumers
`cmp116H_postD_sum_le_of_pStageResidualStages`,
`cmp116H_termWeightSum_le_of_eq229_of_pStageResidualStages`, and
`cmp116Lemma3ActivityEstimate_of_eq229_pStageResidualStages`.  These theorems
split the previous opaque `hpostP` premise into normalized `Z0` and `Z0'`
residual stages after a budget-valued P-stage, matching the order of the
source discussion around CMP116 pages 18--20.  They still do not identify the
P-stage budget, `Z0` stage, or `Z0'` stage with any source theorem or
constant hierarchy.

## Agent Checklist

Before adding a source-facing Lean theorem:

* confirm that the paper and model are correct;
* confirm the equation number in the primary text;
* transcribe all quantifiers and smallness conditions;
* record whether locality uses the bare set, active part, or an enlargement;
* record whether the measure is product, Gaussian correlated, or conditioned;
* track volume/scale/background dependence of every constant;
* name the exact existing theorem that will consume the result;
* check that the proposed hypothesis does not restate the desired conclusion;
* add no project axiom and no `sorry`;
* run the full build/oracle/consistency loop after code changes.

Verification commands:

```bash
lake build YangMillsCore
lake env lean oracle_check.lean
python scripts/check_consistency.py
```

Expected headline oracle:

```text
[propext, Classical.choice, Quot.sound]
```

## Bibliographic Pointers

These identifiers are pointers for locating primary texts.  They are not
substitutes for the provenance fields above.

### Jonathan Dimock

* *The Renormalization Group According to Balaban I. Small Fields*,
  arXiv:1108.1335.
* *The Renormalization Group According to Balaban II. Large Fields*,
  arXiv:1212.5562.

### Tadeusz Balaban

* *Propagators and Renormalization Transformations for Lattice Gauge Theories
  I*, CMP 95 (1984).
* *Averaging Operations for Lattice Gauge Theories*, CMP 98 (1985).
* *Propagators for Lattice Gauge Field Theories in a Background Field*, CMP 99
  (1985).
* *The Variational Problem and Background Fields in the Renormalization Group
  Method for Lattice Gauge Theories II*, CMP 102 (1985).
* *Renormalization Group Approach to Lattice Gauge Field Theories I*, CMP 109
  (1987).
* *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster
  Expansions*, CMP 116 (1988).
* *Convergent Renormalization Expansions for Lattice Gauge Theories*, CMP 119
  (1988).
* *Large Field Renormalization I. The Basic Step of the R Operation*, CMP 122
  (1989).
* *Large Field Renormalization II. Localization, Exponentiation, and Bounds for
  the R Operation*, CMP 122 (1989).

## Immediate Handoff

The next source-driven mathematical target is the quantitative route from the
already exposed cover sum to Dimock's first-activity bound:

```text
raw metric decay
-> theorem-fed finite metric stitching, source shape (641)
-> rooted connected-cover summation
-> K(Y) decay (642)
```

If the source packet for (642), `K#`, and `H#` is incomplete, request the exact
Dimock I Appendix B and Dimock II Appendix E/F passages before inventing a new
API.

The model-specific P4 frontier remains the true Balaban fluctuation activity.
It must not be hidden behind a renamed hypothesis.
