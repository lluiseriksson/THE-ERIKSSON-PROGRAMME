# Dimock-Balaban Source-Claim Audit for the P3/P4 Frontier

**Repository:** `lluiseriksson/THE-ERIKSSON-PROGRAMME`  
**Document status:** adversarial documentation only; not a Lean theorem and
not source evidence by itself  
**Audit date:** 2026-06-20  
**Last updated:** 2026-06-22
**Live code reference:** `47140047e70cddcd1e30263c56cbd57ec7cb342c`
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

Current Lean interface note: at `9a160b67`,
`BalabanCMP116AppendixFSupportHypotheses` asks the source side only for
`F.activeSupport X subset skeleton HF X.val`.  The theorem
`BalabanCMP116AppendixFSupportHypotheses.activeSupport_subset_full` derives
`F.activeSupport X subset X.val` from that skeleton fact and `skeleton_subset`.
Do not list full-target containment as an independent CMP116 source obligation
unless a later consumer requires a stronger enlargement convention.

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
