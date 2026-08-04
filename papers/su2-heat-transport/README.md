# Exact SU(2) algebraic all-mode intertwining paper

This directory contains the manuscript accompanying
`YangMills/OS/SU2HeatAllModes.lean`.

The central claim is an operator intertwining on the algebraic direct sum
`ℕ →₀ ℝ`: one lift covers every finite real SU(2) character expansion,
recovers all coefficients by Haar pairing, is injective, and commutes with the
full diagonal Casimir heat step. The earlier `span{χ₀,χ₁}` theorem remains the
exact quotient connecting to the finite Dobrushin witness. The paper does not
claim Peter--Weyl completeness, a completed full `L²(SU(2))` spectral theorem,
a continuum limit, or four-dimensional Yang--Mills.

Build locally (TeX only):

```text
pdflatex -interaction=nonstopmode -halt-on-error su2_heat_transport.tex
pdflatex -interaction=nonstopmode -halt-on-error su2_heat_transport.tex
```

Lean verification is performed only in the Colab runtime described in
`LEAN-VERIFICATION-LOG.txt`.
