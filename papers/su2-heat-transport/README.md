# Exact SU(2) algebraic all-mode intertwining paper

This directory contains the manuscript accompanying
`YangMills/OS/SU2HeatAllModes.lean`.

Editorial status (2026-08-04): **public Technical Note 48F / NOT SUBMITTED**.
No arXiv, ai.viXra, or journal submission is recorded or authorized by this
closure. The frozen public PDF is
`output/pdf/su2_heat_all_modes_transport.pdf`: 9 A4 pages, 388057 bytes,
SHA-256
`044796414e307856be687e7d18a6372a17b895ec794f93fe14d704f1bafbbdd5`.

The central claim is an operator intertwining on the algebraic direct sum
`ℕ →₀ ℝ`: one lift covers every finite real SU(2) character expansion,
recovers all coefficients by Haar pairing, is injective, and commutes with the
full diagonal Casimir heat step. The earlier `span{χ₀,χ₁}` theorem remains the
exact quotient connecting to the finite Dobrushin witness. The paper does not
claim Peter--Weyl completeness, a completed full `L²(SU(2))` spectral theorem,
a continuum limit, or four-dimensional Yang--Mills.

Those boundaries are promotion locks, not editorial shorthand. A later record
may promote the object beyond a public technical note only after an explicit
owner instruction and an independent audit that addresses the missing
Peter--Weyl density/completeness step, the completed full-`L²` spectrum,
non-class matrix coefficients, and any claimed full-space operator norm. Until
then, the exact result remains the algebraic all-finitely-supported-mode
intertwining plus its retained `{0,1}` finite quotient.

Build locally (TeX only):

```text
pdflatex -interaction=nonstopmode -halt-on-error su2_heat_transport.tex
pdflatex -interaction=nonstopmode -halt-on-error su2_heat_transport.tex
```

Lean verification is performed only in the Colab runtime described in
`LEAN-VERIFICATION-LOG.txt`.
