# Exact SU(2) heat-mode transport paper

This directory contains the manuscript accompanying
`YangMills/OS/SU2HeatTransport.lean`.

The paper's claim is deliberately finite at the endpoint and infinite only at
the concrete Haar-convolution theorem. It does not claim a completed full
`L²(SU(2))` spectral theorem, a continuum limit, or four-dimensional
Yang--Mills.

Build locally (TeX only):

```text
pdflatex -interaction=nonstopmode -halt-on-error su2_heat_transport.tex
pdflatex -interaction=nonstopmode -halt-on-error su2_heat_transport.tex
```

Lean verification is performed only in the Colab runtime described in
`LEAN-VERIFICATION-LOG.txt`.
