## What changed

- constructs the literal interacting Wilson Hessian and the physical corrections
  `R₁`, `R₂`, and `R₃`;
- proves the real positive inverse-root difference by Balakrishnan resolvents,
  with shifted Combes--Thomas localization uniform in the volume;
- constructs the exact physical `R₃ = Γ₁ - Γ₀` and `R₁` telescopes and packages
  `R₁`, `R₂`, and `R₃` at one common decay rate and amplitude;
- consumes that certificate at the full `su(Nc)` block level to prove the
  localized equation-(2.21) estimate without ambient-volume or Lie-dimension
  loss;
- replaces the abstract equation-(2.22) energy premise by the canonical
  coordinate carrier selected from the physical bond set `P`;
- defines the literal fixed-real-field interaction exponent and routes the
  signed `R₃` cross term exactly into the scalar Gaussian source;
- defines the source-faithful potential
  `V_k(Y,B) = 1/2 <B,Q(Y,B)B> + V''_k(Y,B)` and the finite real sum
  `Σ_{Y∈D} τ(Y)V_k(Y,B)`;
- formalizes the two distinct weights printed in equation (2.19): the
  domain-cardinality factor and the internal bond-distance kernel;
- proves the internal Schur estimate, the rooted exchange over domains, and a
  literal specialization with the exact (2.19) coefficients;
- formalizes the inverse contour radius (2.18), its positive solved form, and
  the source majorant (1.43);
- proves the exact scalar cancellation using `C3 ≤ E0*C1`, `q ≥ 8`, and
  `(1-3δ)κ ≤ (κ1-1)/8`;
- defines a localization domain as a nonempty finite family of `M`-blocks
  connected through codimension-one faces;
- constructs its literal fine-lattice carrier and proves the exact
  normalization `|Y| = M^4 * numberOfBlocks`;
- derives `physicalBondDist b b' ≤ 4*M*numberOfBlocks` for supported bonds
  by a spanning walk in the face graph;
- consumes that theorem to discharge `CMP116Eq219MetricBudget`, and therefore
  proves `(1.43) * |τ(Y)| ≤ (2.19)` without a hidden kernel hypothesis;
- derives a generic exact support theorem for mixed line derivatives of any
  function depending only on a finite coordinate set;
- applies it to the literal global evaluation of a localized CMP116 activity,
  proving its quadratic derivative kernel vanishes if either bond lies outside
  the declared active support;
- adds focused axiom audits for every new public endpoint.

## Why

The real-sector chain is now compositional through the literal potential and
its source-faithful two-layer resummation:

```text
physical Hessian
  -> R2 -> inverse-root difference -> R3
  -> covariance difference -> R1
  -> common equation-(2.16) certificate
  -> physical equation (2.21)
  -> literal real exponent
  -> face-connected localization geometry
  -> (1.43) + (2.18) -> equation (2.19)
  -> internal Schur + rooted Y-resummation
  -> equation (2.20)
  -> alpha5 absorption.
```

The formalization preserves the primary-source distinction between decay in
`|Y|`, used to sum domains containing a fixed root bond, and decay in
`|b_- - b'_-|`, used only for the internal bond kernel. It verifies the
normalization from equation (2.30), the cancellation of `epsilon1` and
`exp(C2*kappa1)`, and the `q ≥ 8` scale reduction to `M^-4`.

## Epistemic boundary

The following remain open and are not claimed here:

- the concrete CMP116 dictionaries constructing `D`, `τ`, `Q(Y,B)`, and
  `V''_k(Y,B)` from the localized fluctuation action;
- the physical dictionary identifying the real operator `Q(Y,B)` in (1.42)
  with the mixed derivative kernel of the localized activity (the derivative
  kernel support theorem itself is now proved);
- the source estimate for the residual `V''_k` contribution;
- the complex-contour analogue and the source-faithful distribution inside the
  complex equation-(2.14) integrand;
- the complete residual/cardinality ledger and factorization of (2.26);
- `hraw`, `hRpoly`, the continuum limit, or the Yang--Mills mass gap.

No synthetic summand or post-hoc `termWeight` is used to replace these open
physical identifications.

## Validation

- `lake build YangMillsCore`: success, **8,562 jobs** at head `3327af07`;
- focused source-geometry build: success, **8,359 jobs**;
- focused localized-derivative build: success, **8,189 jobs**;
- all 24 new source-geometry and derivative endpoints report only `propext`,
  `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, local `axiom`, `unsafe`, or `opaque` in the new modules;
- branch remains a draft stacked on `codex/hrpoly-b3-card-tilt`;
- frozen CMP116 reduction releases are unchanged.

No public GitHub Actions run is currently associated with this head; the build
and audits above were executed locally in the pinned project environment.
