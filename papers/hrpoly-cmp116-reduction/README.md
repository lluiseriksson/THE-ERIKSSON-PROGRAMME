# CMP116 finite Gaussian reduction paper

This directory contains the manuscript

> *Machine-Checked CMP116 Fluctuation Reduction: Physical Constraint
> Coordinates and the Interacting-Hessian Frontier*

by Lluis Eriksson.

## Authoritative files

- `hrpoly_cmp116_reduction.tex`: LaTeX source.
- `hrpoly_cmp116_reduction.pdf`: compiled A4 manuscript.
- `CLAIM_MAP.md`: boundary between machine-checked claims and open analytic
  obligations.
- `../../output/pdf/hrpoly-cmp116-reduction.pdf`: tracked release copy of the
  current PDF. The versioned v0.3 filename is supplied in the release bundle.

## Reproducibility

The mathematical checkpoint is on branch
`codex/hrpoly-b3-card-tilt`, pull request
[#28](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/28),
under the immutable tag
`hrpoly-cmp116-main-reduction-v0.3-2026-07-16`.

```text
lake exe cache get
lake build YangMillsCore
lake env lean oracle_check.lean
```

The audited root build completed 8,467 jobs. The 32 new mathematical
endpoints across the physical constraint construction, its norm estimate,
and its terminal consumption depend only on `propext`, `Classical.choice`,
and `Quot.sound`.

## Claim boundary

The release constructs the physical CMP96 constraint elimination
`C = I - E Q`, proves `Q E = I`, `Q C = 0`, `C^2 = C`, and the
volume-independent bound `||C|| <= 1 + M^(d-1)`, transports it isometrically
to CMP116 coordinates, and consumes it in the strongest flat-background
Gamma reduction. Together with the localized determinant and outer Gaussian
moment, the terminal bound has the polymer-volume form `exp(c * |Z0|)` and
contains no ambient-volume factor.

It does **not** construct the Wilson Hessian at the nontrivial small
background `Ubar`, prove the random-walk kernel estimate (2.16), instantiate
the physical domination `hdom`, prove equation (2.26), `hraw`, `hRpoly`, a
continuum Yang--Mills construction, or a mass gap. The exact hard block is
documented in `../../docs/HRPOLY-CMP116-INTERACTING-HESSIAN-BLOCK.md`.
