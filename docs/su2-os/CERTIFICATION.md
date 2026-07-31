# SU(2) Wilson reflection-positivity certification

## Exact

- Physical kernel:
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
- The declared cut has shape `Half × Cross × Half`; reflection swaps the
  halves and inverts each crossing variable.  The crossing link transports
  both boundary holonomies to a common frame and cancels exactly from their
  relative Wilson holonomy.
- This is specifically the one-transporter temporal-gauge cut.  Its crossing
  variable is gauge-pure and cancels identically.  A plaquette with two
  independent transporters `c₁` and `c₂`, with holonomy
  `x c₁ y⁻¹ c₂⁻¹`, is not covered.
- The full reflected pairing integrates left, crossing, and right variables
  against normalized Haar measure and is bridged by a proved identity to the
  analytic kernel quadratic form.
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

The complete oracle command and output are in `ORACLE-TRANSCRIPT.txt`.
The count `8182` belongs only to the target
`YangMills.OS.SU2WilsonReflectionEndpoint`; it is not a claim that the global
`YangMillsCore` target was rebuilt or that the global oracle imports this lane.

The preregistered sharp character gate is fully certified in
`SHARP-GATE.md`; its fixed bound was not weakened.

## Verified

No numerical experiment is used as proof or as a gate.  The build and oracle
above are executable verification records.  External model review is tracked
separately and is not certified; see `AUDIT.md`.
