> **Scope limitation — read before the title.** `Cross` is gauge-pure and
> does not participate in the effective weight or pairing. Its inversion
> under reflection is typed but is not exercised by this result. The declared
> weight is already factorized; no lattice plaquette factorization is derived.
> The separately proved complex Haar positivity for every continuous
> `F : SU2 → ℂ` and the exact lower bound `Qβ(tr) ≥ β/4` remain unchanged.

# SU(2) Wilson Haar-positivity certification

## Exact

- Exact analytic kernel:
  `Kβ(x,y) = exp ((β / 2) * Re tr (x y⁻¹))`.
- Matrix identity:
  `tr(x y⁻¹) = Σ i, j, xᵢⱼ * conj(yᵢⱼ)`.
- Eight real/conjugate coordinate features give a finite positive
  presentation of the exponent when `β ≥ 0`.
- Products and non-negative scaling give an exact finite positive
  presentation of every Taylor truncation.
- The Taylor series converges uniformly on `SU(2) × SU(2)`.
- The iterated Haar quadratic form is the limit of non-negative-real
  finite-rank forms.
- Fundamental Schur orthogonality on `sunHaarProb 2` gives
  `∫ conj(tr U) Uᵢⱼ dU = δᵢⱼ / 2`.
- The degree-one contribution and the complete two-term Taylor head both
  pair with `tr` to exactly `β / 4`.
- Every degree-at-least-two Taylor tail is PSD, so dominated convergence
  yields `Qβ(tr) ≥ β / 4` for the exact crossing kernel.
- The auxiliary cut has shape `Half × Cross × Half`; reflection swaps the
  halves and inverts each crossing variable at the type level.
- `Cross` is gauge-pure: it cancels identically from the effective weight and
  pairing. Its inversion is therefore not exercised by the result.
- `su2OnePlaquetteCutWeight` is a product-form definition.
  `su2OnePlaquetteCutWeight_eq_undressedKernel` proves only removal of the
  common gauge-pure transporter from its dressed kernel; it does not derive a
  lattice plaquette factorization.
- A plaquette with two independent transporters `c₁` and `c₂`, with holonomy
  `x c₁ y⁻¹ c₂⁻¹`, is not covered.
- The declared auxiliary pairing integrates left, crossing, and right
  variables against normalized Haar measure. Its proved equality with the
  analytic kernel quadratic form uses that the `Cross` integrand is constant.
- At `β > 0`, the kernel is non-constant and the constant observable has
  strictly positive pairing.
- At `β > 0`, the zero-mean fundamental character gives a reflected pairing
  equal to a real `r ≥ β / 4 > 0`.

## Certified by Lean

Pinned base:

```text
7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a
```

Executed on 2026-07-31:

```text
lake build YangMills.OS.SU2WilsonReflectionEndpoint
✔ [8182/8182] Built YangMills.OS.SU2WilsonReflectionEndpoint
Build completed successfully (8182 jobs).
```

The owned-source scan contains no `sorry` declaration and no `axiom`
declaration.  The executable oracle exits 0 and reports only the standard
Lean/Mathlib axioms:

```text
[propext, Classical.choice, Quot.sound]
```

The complete oracle command and output are in `ORACLE-TRANSCRIPT.txt`. That
transcript explicitly certifies its parent source-checkpoint commit, not the
later transcript commit that contains it. The source checkpoint SHA, UTC
timestamp, host/OS, toolchain, Mathlib pin, exit code, stdout/stderr, and
binary plus LF-normalized SHA-256 input hashes are recorded there. This
two-commit provenance model avoids an impossible recursive self-hash.
The count `8182` belongs only to the target
`YangMills.OS.SU2WilsonReflectionEndpoint`; it is not a claim that the global
`YangMillsCore` target was rebuilt or that the global oracle imports this lane.

The preregistered sharp character gate is fully certified in
`SHARP-GATE.md`; its fixed bound was not weakened.

## Verified

No numerical experiment is used as proof or as a gate.  The build and oracle
above are executable verification records.  External model review is tracked
separately and is not certified; see `AUDIT.md`.

**Repair status:** repair complete; not self-audited; fresh blind pre-audit
pending; Gate 7 suspended.
