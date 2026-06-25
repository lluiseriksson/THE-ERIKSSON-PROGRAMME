# Dimock-Balaban Source-Claim Audit for the P3/P4 Frontier

**Repository:** `lluiseriksson/THE-ERIKSSON-PROGRAMME`  
**Document status:** adversarial documentation only; not a Lean theorem and
not source evidence by itself  
**Audit date:** 2026-06-20  
**Last updated:** 2026-06-25
**Live code reference:** `96a18f13c3d9c6d49bc00a11ecc8e50f07771c2e`
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
| [`docs/SOURCE-CITATIONS.md`](SOURCE-CITATIONS.md) | Structured citation keys, local artifact hints, and Lean consumers |
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
| Equation (2.29) Lean status | `YangMills.RG.BalabanCMP116Eq229` records the product-summability shape `sum_D prod_{Y in D} alpha_6 exp(-delta*kappa*d_k(Y)) <= 1` from visually confirmed PDF/printed page 18, proves the local D-stage consumer `cmp116_DStage_sum_le_of_eq229`, proves `cmp116H_termWeightSum_le_of_eq229`, which converts a residual post-D `P/Z0/Z0'` bound plus (2.29) into the finite Lemma-3 `hbudget` shape, exposes `cmp116Lemma3ActivityEstimate_of_eq229_postD` as the corresponding theorem-fed activity-estimate consumer, and has a pointwise scale-family lift `cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_postD`; it does not prove Balaban's large-`K`, small-`alpha_6` assertion, threshold uniformity, the source-to-Lean `DIndex/DParts` dictionary, or the residual post-D estimates |
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
(2.27), (2.32), (2.34), (2.36), or (2.37), and it does **not** prove the source
constants or smallness conditions.  Equation (2.30) is only the metric/cardinality
comparison around the P-stage argument; the literal P-family summation is
equation (2.31).  A future source extraction must still supply the normalized
`P`, `Z0`, and `Z0'` residual estimates and the pointwise term-weight
factorization from the primary text.

The local citation key `cmp116.eq229.d-stage-summability` is now visually
confirmed from CMP116 printed page 18.  It records the exact Eq. (2.29)
product-sum display, the adjacent extraction of
`alpha6 * exp(-delta*kappa*d_k(Y))` from the product over `Y in D`, the Eq.
(2.27) and Eq. (2.30) metric comparisons, and the Eq. (2.28) product reduction
under its displayed smallness condition.  This improves source auditability but
does not by itself prove the large-`K`/small-`alpha6` summability assertion
cited in the text.

The P stage now has the source-shaped predicate
`CMP116PStageSourceBound` and adapter
`cmp116PResidualSummability_of_pStageSourceBound`.  The predicate records the
finite `P`-sum bound by
`2 * (blockScale + 2)^4 * pEntropyConstant * epsilon2 * exp(5*kappa)`, and the
adapter turns that source-shaped bound plus the displayed scalar smallness
restriction into normalized `CMP116PResidualSummability`.  Local source check:
`balaban-rg-II-cmp116-1104161193.pdf`, SHA256
`EE39523A0F7B83AF958513C7BD6F9C7731934B40355EF5D6B0F7A68EE6D022FC`; OCR text
SHA256 `1F783762D6EC6FFF9362BB993B2539201E0FE705A5E1C7E0545640CA9EAF2066`;
OCR lines 671--793, especially printed page 20 around line 767, show the
leading `2`, `(L+2)^4`, `O(1)`, `epsilon2`, and `exp 5*kappa` scalar
restriction.  This is still not a proof of the source `P` estimate or of the
construction of `pWeight`.

The P-source predicate is now also routed into the residual-stage consumers:
`cmp116H_postD_sum_le_of_pStageSourceBound_residualStages`,
`cmp116H_termWeightSum_le_of_eq229_of_pStageSourceBound_residualStages`, and
`cmp116Lemma3ActivityEstimate_of_eq229_pStageSourceBound_residualStages`.
These are composition theorems only.  They replace a normalized
`CMP116PResidualSummability` assumption by the source-shaped P bound and its
scalar smallness restriction; they do not assign source status to Eq. (2.29),
the `Z0` stage, the `Z0'` stage, the pointwise factorization, the termwise
complex estimate, or physical activity identification.

The finite P-family entropy step now has a separate Eq. (2.31) boundary in
`YangMills.RG.BalabanCMP116Eq231`: `CMP116Eq231PBondBoundary` records an
injective encoding of current `PIndex` entries as finite bond sets, containment
inside an eligible bond carrier, nonnegativity of the gap mass, and the
`4*M^4` carrier-count bound.  The theorem
`cmp116PGeometricFamilySummation_of_eq231` proves the finite powerset
calculation
`sum_P pGeometryWeight <= 1`, then weakens it to the existing constructor's
`pEntropyConstant * exp (5*kappa)` target through an explicit `htarget`
hypothesis.  This corrects earlier loose language: the `hgeometric` premise is
fed by Eq. (2.31), not by Eq. (2.30) alone.  The theorem still does not
construct `PIndex`, identify `pGeometryWeight`, prove the small-coupling
hierarchy or prove the pointwise P-residual majorization.  The exact source
bracket is now consumed directly through
`cmp116Eq231_rate_condition_of_source_bracket`; the separate theorem
`cmp116Eq231_rate_condition_of_source_smallness` remains only an elementary
sufficient reducer from `0 < gk` and
`80*M^4*gk^2 <= gamma2*epsilon1^2` to that bracket.
The source-facing specialization
`cmp116PStageSourceBound_of_eq231_sourceBondSets` now sets
`P : Finset (Cube × Fin 4)` and `pBonds Z D P := P`, so injectivity is no
longer a source hypothesis on that route; the only non-elementary source fact
left there is containment of every source `P` in the four-direction carrier.
The local citation key `cmp116.eq231.p-bond-sum` now records a visual
extraction of the actual source display: `rho = gamma2*epsilon1^2/(20*gk^2)`,
the source gap factor is `M^-4*|Z0 \ Y0|`, the P-summand has the two factors
`exp(-rho*M^-4*|Z0 \ Y0|)` and `exp(-2*rho*|P|)`, and the displayed
powerset/cardinality bracket is `rho - 4*M^4*exp(-2*rho)`.  That confirms the
rate and scale conventions for the generic Lean theorem, but it still does not
identify the repository's `PIndex` and `pBonds` with Balaban's finite bond set
`P`.
The follow-up citation key
`cmp116.eq231.p-family-carrier-source-target` is deliberately
`source_pending`.  It names the exact missing source data for removing the live
carrier-containment hypothesis from the concrete route: the eligible bond
carrier for fixed `(Z0,Y0)`, the orientation/adjacency convention, and the
carrier upper bound `|Carrier(Z0,Y0)| <= 4*|Z0 \ Y0|`.  The lower bound on
`|P|` visible before Eq. (2.31) is not that carrier upper bound.  Do not remove
the `hPcarrier` premise from the concrete source-bond-set route until these
facts are extracted from a primary source passage.
The fixed-index bridge `cmp116PStageSourceBound_of_eq231_pointwise` and the
scale-family constructor
`CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise` compose this
Eq. (2.31) finite subset-entropy theorem with the existing pointwise P-term
estimate.  They remove only the intermediate abstract `hgeometric` premise:
the source construction of `PIndex`, identification of `pResidualWeight` and
`pGeometryWeight`, source bracket condition, target
comparison, and post-`P` source estimates remain separate obligations.

The `Z0` stage now also has the source-shaped predicate
`CMP116Z0StageSourceBound` and adapter
`cmp116Z0ResidualSummability_of_z0StageSourceBound`.  The predicate records a
fixed-`(Z,D,P)` finite `Z0` sum bounded by
`((blockScale + 2)^4) * z0EntropyConstant * epsilon2`, and the adapter turns
that bound plus the separate scalar smallness restriction into normalized
`CMP116Z0ResidualSummability`.  This is anchored to the CMP116 printed page 19
Z0 resummation around the geometric estimate (2.32), together with the printed
page 20 smallness restrictions.  Equation (2.32) is treated as the geometric
input controlling the source resummation, not as a literal statement of the
Lean predicate.  This remains only a source-budget-shape interface: it does not
construct `Z0Index`, identify `z0Weight`, prove the source estimate, or assign
source status to `Z0'`.

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
The exact Eq. (2.29) product now has the reusable name
`cmp116Eq229Product`, and `cmp116Eq229WeightedPWeight` records the canonical
choice `pWeight = cmp116Eq229Product * pResidualWeight`.  The theorem
`cmp116PStageSummability_of_pResidualSummability_weighted`, with its
scale-family lift, proves only that a normalized P-residual sum gives the
budget-valued P-stage predicate with the Eq. (2.29) product itself as budget.
This is an algebraic alignment of budgets, not a source proof of the P-stage
estimate or any scalar smallness hierarchy.

`YangMills.RG.BalabanCMP116Lemma3ResidualStages` now also exposes the matching
fixed-P residual bridge `cmp116H_postP_sum_le_of_residualStages` and the
composed consumers
`cmp116H_postD_sum_le_of_pStageResidualStages`,
`cmp116H_termWeightSum_le_of_eq229_of_pStageResidualStages`, and
`cmp116Lemma3ActivityEstimate_of_eq229_pStageResidualStages`.  These theorems
consume an already supplied P-stage budget and normalized fixed-`P` residual
stages; they do not prove or source-identify those hypotheses.  They still
split the previous opaque `hpostP` premise into normalized `Z0` and `Z0'`
residual stages after a budget-valued P-stage, matching the order of the
source discussion around CMP116 pages 18--20.  They still do not prove the
source P-stage bound, identify the `Z0` stage or `Z0'` stage with any source
theorem, or discharge the constant hierarchy.

The scale-family wrapper
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages`
applies this same pStage/residual-stage route pointwise in `(t, k)`.  It is a
consumer of explicit per-scale source obligations, not a source extraction.
The companion wrapper
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageSourceBound_residualStages`
applies the P-source-bound route pointwise in `(t, k)`: it consumes per-scale
`CMP116PStageSourceBound` and the per-scale scalar smallness restriction, but
still leaves Eq. (2.29), `Z0/Z0'` residual summability, pointwise
factorization, termwise estimates, and physical activity identification as
explicit obligations.

A separate combined residual lane now exists for the source order visible on
CMP116 printed pages 19--20.  The source first controls the last `Z0/Z0'`
resummations through a combined/order-sensitive estimate; it is not currently
justified to label the existing normalized fixed-`(D,P,Z0)` `Z0'` predicate as
the printed source theorem.  The new declarations
`CMP116PostPResidualSourceBound`,
`cmp116PostPResidualBound_of_sourceBound`, `CMP116PostPResidualBound`,
`cmp116PostPResidualBound_of_residualStages`,
`cmp116H_postD_sum_le_of_pStagePostPResidualBound`,
`cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound`,
`cmp116Lemma3ActivityEstimate_of_eq229_pStagePostPResidualBound`, and
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound`
therefore consume a direct combined post-`P` finite-sum bound.  This is still
only a consumer route: `cmp116PostPResidualBound_of_residualStages` proves that
the split normalized residual route packages into the combined predicate, but
the split estimates, combined post-`P` bound, Eq. (2.29), P-stage budget,
activity identification, and termwise estimates remain source obligations.
`CMP116PostPResidualSourceBound` is the source-side predecessor for a supplied
combined estimate with its own amplitude and source weight; the adapter to
`CMP116PostPResidualBound` additionally requires an explicit majorization by
the canonical CMP116 Lemma-3 base factor.  It does not claim that the printed
equations literally contain that repository predicate or discharge the
majorization.  The per-scale predicate
`CMP116PostPResidualSourceMajorizationScaleFamily` now names this base-factor
majorization across `(t, k)`, and
`cmp116PostPResidualBoundScaleFamily_of_sourceBound` applies the already
verified single-scale adapter pointwise.  This still proves no CMP116 pages
19--20 constant hierarchy, no combined source estimate, and no majorization
from printed `O(1)` constants.
The scale source-boundary package
`CMP116Lemma3PostPScaleSourceAssumptions` records the same route at the
per-scale call site.  Its projection
`CMP116Lemma3PostPScaleSourceAssumptions.lemma3_activity_estimate` applies the
already verified scale-family theorem and deliberately carries a direct
`CMP116PostPResidualBound` field instead of adding a standalone `Z0'` budget or
identifying `CMP116Z0PrimeResidualSummability` with a printed equation.

`YangMills.RG.BalabanCMP116Lemma3AdmissibleAdapter` now records the admissible
domain transport as an explicit interface.  The zero-extension theorems consume
a native Lemma-3 estimate on the subtype `{X // admissible X}` and an explicit
outside-domain vanishing theorem.  The metric-domination theorem additionally
requires that every target-family polymer is admissible and that the complete
Appendix-F/CMP116 exponent comparison holds.  This adapter deliberately proves
none of those source facts and does not claim that all repository polymers are
CMP116 admissible domains.  The projection
`CMP116Lemma3PostPScaleSourceAssumptions.lemma3_activity_estimate_admissible_zeroExtension`
only composes the existing post-`P` source package on admissible subtypes with
the zero-extension theorem; it adds no duplicate admissible post-`P` structure
and does not discharge Eq. (2.29), the P-stage budget, the combined post-`P`
bound, activity identification, termwise estimates, or outside-domain
vanishing.

`YangMills.RG.BalabanCMP116SourceTheorem` now also exposes
`BalabanCMP116Lemma3ResummationSourceAssumptions`, a source-boundary record
that carries those explicit per-scale obligations instead of a monolithic
`CMP116Lemma3ActivityEstimateScaleFamily` field.  Its constructors derive the
existing `BalabanCMP116Lemma3SourceAssumptions` and `CMP116RawSourceM3Frontier`
records by applying the verified pStage/residual-stage scale-family theorem.
This is an audit improvement only: the P-stage budget, the two residual-stage
summability estimates, the activity identification, the termwise estimate, and
the source metric comparison remain primary-source obligations.
The parallel constructor
`CMP116RawSourceM3Frontier.of_lemma3ResummationSourceAssumptions` is the same
record projection with a normalized API name; it adds no source content.

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

## Recent CMP116 Route Note

`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_weightedPResidualPostPResidualBound`
is source-neutral composition only.  It consumes Eq. (2.29), normalized
P-residual summability, `alpha6 >= 0`, a direct combined post-`P` residual
bound for the Eq. (2.29)-weighted P weights, activity identification, and
termwise estimates.  It does not assert a source construction of the normalized
P weights, a standalone `Z0'` source bound, or any scalar replacement for the
Eq. (2.29) product.

`CMP116Lemma3WeightedPostPScaleSourceAssumptions` is the corresponding
source-boundary package.  Its fields keep the P-stage source bound, the scalar
smallness condition, pointwise P-residual nonnegativity, the combined post-`P`
source bound, and the post-`P` majorization separate.  Its projections are
packaging only; they do not prove any of those source obligations.

`CMP116Lemma3ActivityTermwiseScaleBoundary` only factors two common fields:
physical activity identification with `balabanCMP116H`, and the termwise norm
estimate.  Its `activityTermwiseBoundary` projections from the post-`P` packages
are audit handles, not proofs of those fields.

`CMP116Lemma3Eq229ScaleBoundary`,
`CMP116Lemma3PStageSourceScaleBoundary`, and
`CMP116Lemma3WeightedPostPSourceScaleBoundary` split the weighted post-`P`
package into source-neutral boundary records.  The constructor
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_boundaries` only copies
fields from those records plus `CMP116Lemma3ActivityTermwiseScaleBoundary`; it
does not prove Eq. (2.29), P-stage smallness, post-`P` source majorization, or
activity identification.

`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries`
is the direct downstream consumer of those boundary records.  It first assembles
the checked weighted post-`P` package and then applies the existing
`lemma3_activity_estimate` projection.  It adds no source theorem and discharges
none of the four boundary packages.

`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_boundaries`
is the Eq. (2.31)-specialized version of that consumer.  It constructs the
P-stage boundary internally from `CMP116Eq231PBondBoundary` plus the explicit
pointwise, source-rate positivity/smallness, target, residual smallness, and
nonnegativity hypotheses, then applies the existing weighted post-`P` route.
It removes only an intermediate record assembly premise and the opaque `hrate`
input on this route; it does not prove the CMP116 source construction of the
P-family, Eq. (2.31) constants, pointwise P-residual bound, post-`P`
majorization, activity identification, termwise estimate, or the full scalar
hierarchy.

The narrower scale constructor
`CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourceBondSets` is now the
first downstream source route whose P-index is literally a finite bond set
`Finset (Cube × Fin 4)`.  It removes arbitrary `CMP116Eq231PBondBoundary` data
from that route, but it still carries the source-specific `hPcarrier`
containment premise.

`CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets` is the
filtered-powerset variant of the same route.  It removes the per-`P`
`hPcarrier` premise when the resummation record's `PIndex` is explicitly equal
to `cmp116Eq231SourcePIndex gapCubes admissible`, since containment is then
just powerset membership.  It does not prove that Balaban's source `P` family is
that filtered Lean family; the `PIndex` equality is still the source dictionary
to be supplied by a later theorem.

`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_filteredBondSets` and
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_filteredBondSets`
propagate the same filtered route to the weighted post-`P` source package and
direct Lemma-3 estimate consumers.  They remove the abstract Eq. (2.31)
bond-boundary input at that downstream level, but only after the filtered
`PIndex` dictionary has already been supplied.

`rawSource_of_weightedPostPBoundaries` composes that direct consumer with the
pre-existing `rawSource_of_lemma3ActivityEstimate` adapter.  It still requires
the Gaussian pushforward, covariance-root localization, Wilson-Hessian
identification, and local physical activity construction hypotheses explicitly.
It is not evidence for any of those physical/source facts.

`rawSource_of_eq231_weightedPostPBoundaries` is the matching raw-source adapter
for the Eq. (2.31)-specialized route.  It composes
`lemma3_activity_estimate_of_eq231_boundaries` with
`rawSource_of_lemma3ActivityEstimate`, so the intermediate P-stage boundary
record is no longer a call-site premise when Eq. (2.31) bond-boundary data are
available.  It proves no Gaussian pushforward, covariance-root localization,
Wilson-Hessian identification, local activity construction, P-family source
construction, post-`P` majorization, activity identification, or termwise
estimate.

`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries` is the
record-level version of the same Eq. (2.31) packaging: it constructs the
weighted post-`P` source package from Eq. (2.29), Eq. (2.31) P-bond data,
explicit pointwise/source-rate/target/smallness/nonnegativity hypotheses, the
weighted post-`P` boundary, and the activity/termwise boundary.  The companion
projection `CMP116Lemma3WeightedPostPScaleSourceAssumptions.rawSource` applies
the package's Lemma-3 estimate to the existing raw-source adapter.  Both are
source-neutral plumbing; neither proves any physical source fact, analytic
source bound, full scalar hierarchy, or CMP116 identification.

`BalabanCMP116Lemma3WeightedPostPSourceAssumptions` is the source-theorem-layer
counterpart of that weighted post-`P` package.  It keeps all physical/M3
obligations visible and consumes a supplied
`CMP116Lemma3WeightedPostPScaleSourceAssumptions` package to produce the
existing Lemma-3 source record and M3 frontier.  Its projections
`lemma3_activity_estimate`, `rawSource`, `to_lemma3SourceAssumptions`, and
`to_m3Frontier` are record assembly only.  They do not prove Eq. (2.29),
Eq. (2.31), P-stage source construction, weighted post-`P` source estimates,
post-`P` majorization, activity identification, termwise estimates, Gaussian
pushforward, covariance-root localization, Wilson-Hessian identification, or
local physical activity construction.

`BalabanCMP116Lemma3WeightedPostPSourceAssumptions.of_eq231_boundaries` is the
Eq. (2.31)-specialized constructor into that source-theorem package.  It reuses
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries` for the
weighted post-`P` field and copies all physical/M3 fields from explicit
arguments.  It proves no Eq. (2.31) source construction, no pointwise
P-residual estimate, no full scalar hierarchy, no post-`P` source estimate or
majorization, no activity identification, no termwise estimate, and no
Gaussian/root/Hessian/local-activity source fact.  It only rewrites the exact
Eq. (2.31) source bracket condition into the generic exponential-rate premise
needed by the finite P-family summation theorem.

`CMP116RawSourceM3Frontier.of_eq231WeightedPostPSourceBoundaries` is the direct
M3-frontier consumer for the same Eq. (2.31)-specialized boundary data.  It
only composes
`BalabanCMP116Lemma3WeightedPostPSourceAssumptions.of_eq231_boundaries` with
`CMP116RawSourceM3Frontier.of_lemma3WeightedPostPSourceAssumptions`.  It does
not prove Eq. (2.29), construct Eq. (2.31) P-bond data, identify the pointwise
P-residual or post-`P` source weights, prove activity/termwise estimates,
construct Gaussian pushforwards or covariance roots, prove the H# identity, or
discharge any RG-flow or IR input.

`CMP116Eq237MajorizationBoundary` is the source-shaped Eq. (2.37) boundary for
the post-`P` majorization step only.  It records the seven-delta decay,
residual-exponent absorption budget, and the `C3*epsilon1` amplitude comparison.
The theorems `cmp116Eq237_residualExponent_absorbed` and
`cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237` discharge the
canonical Lemma-3 post-`P` majorization from that boundary.  The constructor
`CMP116Lemma3WeightedPostPSourceScaleBoundary.of_sourceBound_eq237Majorization`
therefore removes the independent `postP_majorization` input on this route,
but still requires the combined `CMP116PostPResidualSourceBound`.  It does not
identify CMP116's `Z0/Z0'` source indices with repository indices, prove the
post-`P` finite source sum, or evaluate/identify any source `O(1)` constants.

`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237Majorization` and
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237Majorization`
propagate that removal into the weighted post-`P` source package and direct
Lemma-3 estimate.  They still require Eq. (2.29), a P-stage source boundary,
the combined `CMP116PostPResidualSourceBound`, and the activity/termwise
boundary explicitly.

### CMP116 reference [26] behind Eq. (2.29)

CMP116 printed page 18 says that inequalities of the Eq. (2.29) type can be
proved by a simple modification of the argument in `[26]`.  The local CMP116
reference list delegates references to Part I, so the relevant bibliographic
anchor is CMP109 printed page 299.  The citation catalog now records the visual
identification under `cmp109.ref26.cammarota-infinite-range-cluster`: reference
26 is C. Cammarota, "Decay of correlations for infinite range interactions in
unbounded spin systems", CMP 85, 517-528 (1982).

Audit boundary: this only identifies the paper to inspect next.  It does not
extract Cammarota's theorem, prove the large-`K`/small-`alpha6` threshold,
identify Cammarota's objects with Balaban's `D` families, or identify those
families with the repository's `DIndex/DParts`.

The citation catalog now also records the direct Cammarota access target under
`cammarota.cmp85.polymer-mayer-source-target`.  Springer confirms the DOI,
pages, and paper-level polymer/Mayer-series relevance, while Project Euclid's
PDF endpoint returned an anti-bot HTML page to the automation environment and
the visible ResearchGate text remains an author-uploaded OCR/mirror, not a
local primary source artifact.  This status is deliberately `source_pending`:
it is an access ledger and source request, not a theorem or threshold
extraction.
