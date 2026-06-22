# CMP116 Weighted Hsharp Source Map

Updated: 2026-06-22

Public checkpoint inspected: `1e4add8`

Latest theorem frontier referenced below: the `9c2f42c` support frontier plus
the integrated scalar second-gas KP wrapper in the current snapshot.

Lean endpoints now in view:

* `BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_subset_target_inter_omegaRegion`;
* `BalabanCMP116AppendixFSupportHypotheses.omegaGraph_adj_imp_skeletonOverlapGraph_adj_of_activeSupport_subset_target_inter_omegaRegion`;
* `BalabanCMP116AppendixFSupportHypotheses.omegaGraph_adj_imp_skeletonOverlapGraph_adj_of_supportHypotheses`;
* `BalabanCMP116AppendixFSupportHypotheses.not_omegaGraph_adj_of_disjoint_skeleton_of_supportHypotheses`;
* `balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_majorant`;
* `BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source`;
* `appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric`;
* `BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source_of_card_le_metric`;
* `balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_rawMetricDecay_rooted_of_source_of_card_le_metric`;
* `singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_sourceMeasurable`.

This note maps the new weighted `H#` tree bridge onto the local primary-source
packet.  Its purpose is defensive: it records which hypotheses are source-backed
candidates and which remain proof obligations before the CMP116 endpoint can be
instantiated for Yang-Mills.

## Lean Target

The current bridge in `YangMills/RG/BalabanCMP116HsharpSource.lean` consumes:

* a pointwise first-activity estimate
  `||zK Q.val|| <= epsilon(t,k) * w Q`;
* a weighted fixed-union tree estimate
  `appendixFHoleHsharpWeightedTreeTerm ... <= Croot(t,k) * decay(P) * Cleaf(t,k)^n`;
* nonnegativity of weights and constants;
* the small-ratio condition `Cleaf(t,k) * epsilon(t,k) < 1`;
* a closed comparison for `(Croot * epsilon) / (1 - Cleaf * epsilon)`;
* the existing rooted hole-geometry and real-extraction hypotheses.

The Lean side then supplies only the finite transfer from those assumptions to
the existing geometric profile, cluster3 contract, and scalar UV consumer.

Current-main support correction: after `9c2f42c`,
`BalabanCMP116AppendixFSupportHypotheses` has only one source support field,
`activeSupport_subset_skeleton`.  The former full-support inclusion is now
derived in Lean as
`BalabanCMP116AppendixFSupportHypotheses.activeSupport_subset_full` using
`skeleton_subset`.  Source extraction should therefore target skeleton-local
active support, activity measurability, and the raw decay/integrability
statement, rather than asking for an independent full-support theorem.

The source can also target the common clipped-active-region form directly:
prove `F.Omega = HF.omegaRegion` and
`F.activeSupport X ⊆ X.val ∩ F.Omega` (or equality).  Lean rewrites this
through `skeleton HF X.val = X.val ∩ HF.omegaRegion` into the required
`activeSupport_subset_skeleton` package.

With the equality form, Lean also rewrites the CMP116 hard-core relation:
`F.zeta X Y = 0` is exactly non-disjointness of `skeleton HF X.val` and
`skeleton HF Y.val`, and `F.omegaGraph.Adj` matches the Appendix-F
skeleton-overlap graph on the polymers in `Λ`.  Thus the source still only has
to identify the localized active domain; the hard-core graph translation is
finite set theory.

If the source only gives the inclusion
`F.activeSupport X ⊆ X.val ∩ F.Omega`, Lean still proves the safe one-way
translation: every CMP116 Ω-overlap edge maps to an Appendix-F
skeleton-overlap edge.  The reverse direction remains tied to the equality
form above.

The one-way graph translation is also available directly from the support
package itself:
`omegaGraph_adj_imp_skeletonOverlapGraph_adj_of_supportHypotheses` consumes
only `F.activeSupport X ⊆ skeleton HF X.val`.  This is the narrowest graph
dictionary for a future source theorem that proves active-skeleton locality
directly, without separately restating the clipped-region form.

The same support package also supplies the no-cross-edge direction:
`not_omegaGraph_adj_of_disjoint_skeleton_of_supportHypotheses` proves that
disjoint Appendix-F active skeletons have no CMP116 Ω-overlap edge.  This is
the factorization-facing companion to the edge implication above.

Together, these two graph directions are the finite hard-core dictionary
available from the support package.  They do not discharge the package itself:
the next source theorem must still prove `F.activeSupport X subset skeleton HF
X.val` or supply the exact enlargement convention that replaces that target.

The integrated scalar second-gas side now has the same KP-ready interface as
the evaluated second gas:
`balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_majorant` consumes
`BalabanCMP116AppendixFIntegratedSecondGasKPMajorant` plus the with-holes
geometry and smallness hypotheses.  This is still a consumer interface: it does
not prove Dimock (642), the integrated scalar majorant, or the spectator-field
measure identification.  The source-package helper
`BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source`
now composes the already-formalized integrated `K#` norm estimate with that
consumer, reducing the remaining Lean-side input to a single scalar profile
inequality absorbing `exp t`, `exp |Y|`, and the chosen `A,q` metric constants.
That profile has now been separated once more:
`appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric` proves the finite
exponential absorption from a full-cardinality budget
`|Y| <= theta * (d_M(Y)+1)`, and
`balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_rawMetricDecay_rooted_of_source_of_card_le_metric`
feeds the resulting `A,q` profile into the integrated second-gas KP criterion.
The full-cardinality budget is intentionally not inferred from the skeleton
metric; it is the next explicit geometric/source obligation.

The finite part now also exposes the weaker cover-sum form:
`appendixFHoleTargetFiber_card_le_metricSum_of_source_card_le_metric` rewrites
the exact target-fiber equation and proves
`|Y| <= theta * Σ_{X in C} (d_M(X)+1)` whenever each source polymer in the
selected cover obeys `|X| <= theta * (d_M(X)+1)`.  This does not close the
KP profile above, because that profile needs `|Y| <= theta * (d_M(Y)+1)`;
the missing source theorem is precisely the compression from a cover-sum
budget to a direct target-metric budget, or an equivalent reformulation of the
second-gas KP constants.

Latest OCR/source-extraction verdict: CMP116 (2.5)--(2.11) supports the
product-Gaussian change of variables and the existence of localized activities
`H(Z)`, but the printed phrase "localized in the interior of Z with respect to
the external gauge fields" is not yet a Lean-ready theorem of the form
`F.activeSupport X ⊆ X.val ∩ F.Omega` or
`F.activeSupport X ⊆ skeleton HF X.val`.  The next source packet must supply
the exact enlargement convention, hole/large-field compatibility, and the map
from Balaban's localization domain `Z` to the current `OmegaPolymerType`
support fields before the support hypotheses can be instantiated honestly.

## Source Anchors

### CMP116: first localized activity

Local OCR:
`C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary\text\balaban-rg-II-cmp116-1104161193.txt`.

Relevant ranges:

* lines 453-493: Mayer/localization setup, resummation into `F(Z0,B)`,
  conditioning, the linear Gaussian change of variables, formula (2.6), and
  the product identity Gaussian `dμ0` after `B' = (C(k))^(1/2) X`;
* lines 494-545: localization of external-field dependence by interpolation
  and random-walk expansion, followed by the localized activity `H(Z)`;
* lines 541-553: (2.4), (2.6), and (2.8) imply (2.9), component
  factorization (2.10), and the hard-core polymer expansion (2.11);
* lines 671-793: the resummed estimate of `H(Z)`, ending in Lemma 3 / (2.38),
  with source constants and restrictions around (2.27), (2.29), (2.30),
  (2.32), and (2.36).

Lean map: this is the best source-backed candidate for the first-activity
hypothesis `hraw`, after translating constants, supports, measurability, and
the relevant metric.  It is not by itself a source for the second-Ursell
weighted tree estimate or the physical remainder identity `hR`.

### Dimock I Appendix B: tree/Ursell leaf mechanism

Local TeX:
`C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary\dimock-1108.1335-src\Balaban1v4.tex`.

Relevant ranges:

* lines 3178-3185: standard cluster theorem and final residual `H#` form;
* lines 3248-3256: metric stitching inequality `clams`;
* lines 3312-3315: definition of `H#` by the second Ursell series `hstar`;
* lines 3406-3438: Step 4, tree-graph domination and fixed-union rewrite
  `sundry`;
* lines 3487-3507: Cayley degree count `spit2`, division by `n!`, and the
  final order summation.

Lean map: this is the precise printed mechanism behind a leaf-summation proof
of the weighted tree estimate, but it is the no-hole version.  It supports the
formal strategy, not yet the exact with-holes Lean theorem.

### Dimock II Appendix F: holes/Omega adaptation

Local TeX:
`C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary\dimock-1212.5562-src\Balaban2l.tex`.

Relevant ranges:

* lines 6833-6919: disconnected-polymer summability and the pinned with-holes
  estimate `sumsum`;
* lines 6984-7005: theorem `cluster3`, including the with-holes activity
  decay assumption and final `H#` residual estimate;
* lines 7008-7049: `keykey1`, `keykey2`, the with-holes stitching inequality
  `otter`, and the connected `K(Y)` estimate `simplon`;
* lines 7068-7077: second Ursell definition `hstar` and the statement that the
  Appendix B estimates lead to the final bound.

Lean map: this is the source for the hole-aware final theorem and its geometry.
It does not print the exact order-wise weighted-tree term now exposed by Lean.
Either the order-wise theorem must be reconstructed from Dimock I Step 4 plus
the Appendix F modifications, or the formal route should consume `cluster3`
directly as a final theorem-shaped contract.

## Status Matrix

| Lean hypothesis | Source status | Remaining translation |
| --- | --- | --- |
| `hraw` / first activity | Source-backed candidate from CMP116 (2.4)-(2.11) and Lemma 3/(2.38). | Identify `zK`, `epsilon`, skeleton-local active support, measurability, integrability, and metric constants exactly; full support is Lean-derived from skeleton support. |
| `hleaf` / weighted tree estimate | Not printed in exact Lean form. | Prove the order-wise with-holes leaf summation, or switch to a direct `cluster3` consumer. |
| `hsmall` / ratio `< 1` | Compatible with Dimock smallness and CMP116 restrictions. | Translate source constants into `Cleaf * epsilon < 1`. |
| `hBclosed` | Not printed in the weighted split. | Derive the closed comparison after fixing source constants. |
| `beta` / product Gaussian | CMP116 (2.5)-(2.6) supports the product-Gaussian collar after change of variables. | Decide how the Lean spectator measure `nu` represents remaining/external fields after `dμ0` integration. |
| `hR` / concrete Yang-Mills remainder | Still open. | Need the CMP119/CMP122 large-field/R-operation source chain and exact scalar extraction. |

## Recommended Next Formal Move

The safest next step is not another algebraic wrapper.  Choose one source route
while keeping the current support interface in view:

1. Direct route: add a theorem-shaped consumer for Dimock II `cluster3` and prove
   that the current finite Appendix-F objects match its inputs.
2. Deeper route: formalize the order-wise with-holes leaf summation proving the
   weighted tree estimate from Dimock I Step 4 plus the Appendix F geometry.
3. In either route, extract only the support fact now consumed by Lean:
   `F.activeSupport X ⊆ skeleton HF X.val`; the full-target inclusion is no
   longer a separate source obligation.

Until one of those is done, CMP116 alone should not be treated as proving the
weighted `H#` tree hypothesis.
