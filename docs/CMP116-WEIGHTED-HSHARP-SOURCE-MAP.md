# CMP116 Weighted Hsharp Source Map

Updated: 2026-06-21

Public checkpoint inspected: `43e14d7`

Lean endpoint:
`singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_weighted_tree_geometric`

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

## Source Anchors

### CMP116: first localized activity

Local OCR:
`C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary\text\balaban-rg-II-cmp116-1104161193.txt`.

Relevant ranges:

* lines 453-493: Mayer/localization setup, resummation into `F(Z0,B)`,
  conditioning, the linear Gaussian change of variables, and formula (2.6);
* lines 494-545: localization of external-field dependence by interpolation
  and random-walk expansion, followed by the localized activity `H(Z)`;
* lines 541-553: (2.4), (2.6), and (2.8) imply (2.9), component
  factorization (2.10), and the hard-core polymer expansion (2.11);
* lines 671-793: the resummed estimate of `H(Z)`, ending in Lemma 3 / (2.38).

Lean map: this is the best source-backed candidate for the first-activity
hypothesis `||zK Q|| <= epsilon * w Q`, after translating constants, supports,
and the relevant metric.  It is not by itself a source for the second-Ursell
weighted tree estimate.

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
| `hactivity` | Source-backed candidate from CMP116 (2.4)-(2.11) and Lemma 3/(2.38). | Identify `zK`, `epsilon`, `w`, support carrier, and metric constants exactly. |
| `hleaf` / weighted tree estimate | Not printed in exact Lean form. | Prove the order-wise with-holes leaf summation, or switch to a direct `cluster3` consumer. |
| `hsmall` / ratio `< 1` | Compatible with Dimock smallness and CMP116 restrictions. | Translate source constants into `Cleaf * epsilon < 1`. |
| `hBclosed` | Not printed in the weighted split. | Derive the closed comparison after fixing source constants. |
| `beta` / product Gaussian | CMP116 (2.5)-(2.6) supports the product-Gaussian collar after change of variables. | Decide how the Lean spectator measure `nu` represents remaining/external fields. |
| `hR` / concrete Yang-Mills remainder | Still open. | Need the CMP119/CMP122 large-field/R-operation source chain and exact scalar extraction. |

## Recommended Next Formal Move

The safest next step is not another algebraic wrapper.  Choose one source route:

1. Direct route: add a theorem-shaped consumer for Dimock II `cluster3` and prove
   that the current finite Appendix-F objects match its inputs.
2. Deeper route: formalize the order-wise with-holes leaf summation proving the
   weighted tree estimate from Dimock I Step 4 plus the Appendix F geometry.

Until one of those is done, CMP116 alone should not be treated as proving the
weighted `H#` tree hypothesis.
