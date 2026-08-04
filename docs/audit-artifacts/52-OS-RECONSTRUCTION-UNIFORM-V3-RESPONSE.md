# (52) Response to the 5.14/10 review

Status: documentary revision for independent reassessment; not a self-issued
score.

The review recognizes that v2 reaches the reconstructed connected correlator
without loss, but keeps the score at 5.14/10 for three reasons: the analytic
estimate is inherited, the new step is mainly algebraic, and the paper is
brief and dependent on earlier work.

V3 makes the strongest revision available without inventing mathematics or
changing a formal statement:

| Review point | V3 response |
|---|---|
| The paper is not analytically autonomous | Sections 2--4 reproduce the complete chain: intrinsic heat-bath interdependence, the finite Dobrushin comparison bound, the anisotropic rectangle row sum, end-slice covariance decay, the Perron boundary tilt, and the decay-to-gap transport. |
| The exponent is only existential in the narrative | V3 records the existing witness `m = -log alpha` and explains why it is chosen before the spatial extent. |
| Only a real boundary vector is discussed | V3 identifies `A_L = R^(X_L)` as the full finite-dimensional commutative algebra of real functions on the boundary slice. |
| No larger family of correlators is shown | A paper-level corollary defines mixed connected correlators for arbitrary `u,v in A_L` and proves `|B_L(u,v;n)| <= ||u|| ||v|| exp(-mn)` directly from the checked operator norm. It is explicitly not mislabeled as a new Lean declaration. |
| The paper is short and highly dependent | The integrated proof can now be read without consulting the separate Dobrushin paper; the theorem map still distinguishes inherited declarations from the reconstruction module. |

What v3 does not change is equally important.  It proves no sharper
Dobrushin window, thermodynamic limit, boundary-condition independence,
continuum theory, Wightman reconstruction, or Yang--Mills mass gap.  Those
would require genuinely new mathematics and cannot be supplied by editorial
revision.

No Lean source changed after the frozen v2 body
`3478813bf02427bc48fbbbdb46a64d809882838b`; therefore no local or remote Lean
execution was needed for v3.  Its formal claims continue to point to the exact
v2 source, `.olean`, exhaustive oracle, and frozen-object hashes.
