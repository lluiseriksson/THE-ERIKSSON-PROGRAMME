# Exact SU(2) two-mode intertwining paper

This directory contains the manuscript accompanying
`YangMills/OS/SU2HeatIntertwining.lean`.

The central claim is an operator intertwining on the exact invariant sector
`span{χ₀,χ₁}`: the continuous lift is injective and Haar-isometric, the finite
lift is bijective, and both actual operators commute with
`diag(1, exp(-3t/4))`. It does not claim a completed full `L²(SU(2))` spectral
theorem, a continuum limit, or four-dimensional Yang--Mills.

Build locally (TeX only):

```text
pdflatex -interaction=nonstopmode -halt-on-error su2_heat_transport.tex
pdflatex -interaction=nonstopmode -halt-on-error su2_heat_transport.tex
```

Lean verification is performed only in the Colab runtime described in
`LEAN-VERIFICATION-LOG.txt`.
