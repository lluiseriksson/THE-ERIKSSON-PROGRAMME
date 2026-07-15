# CMP116 finite Gaussian reduction paper

This directory contains the manuscript

> *A Machine-Checked Reduction of Balaban's CMP116 Fluctuation Integral to
> Its Physical Analytic Frontier*

by Lluis Eriksson.

## Authoritative files

- `hrpoly_cmp116_reduction.tex`: LaTeX source.
- `hrpoly_cmp116_reduction.pdf`: compiled A4 manuscript.
- `CLAIM_MAP.md`: boundary between machine-checked claims and open analytic
  obligations.
- `../../output/pdf/hrpoly-cmp116-reduction.pdf`: release copy of the PDF.

## Reproducibility

The mathematical checkpoint is on branch
`codex/hrpoly-b3-card-tilt`, pull request
[#28](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/28),
under the immutable tag
`hrpoly-cmp116-main-reduction-v0.2-2026-07-15`.

```text
lake exe cache get
lake build YangMillsCore
lake env lean oracle_check.lean
```

The audited build completed 8,454 jobs. The four theorem endpoints in
`BalabanCMP116Eq214MainReduction.lean` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Claim boundary

The release proves the analytic kernel implications of equations
(2.20)--(2.22), the complete finite-dimensional determinant/source bound of
(2.24), and a terminal reduction whose remaining substantive premises are
the physical domination `hdom` and a uniform scalar source-norm certificate.
It does **not** prove the concrete CMP116 kernel inputs, a model-specific
uniform source-norm estimate, equation (2.26), `hraw`, `hRpoly`, a continuum
Yang--Mills construction, or a mass gap.
