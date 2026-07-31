# SU(2) Wilson reflection-positivity contract

## Freeze

- Published base: `origin/main`
- Full base SHA: `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`
- Branch: `codex/su2-wilson-reflection-positivity`
- Scope: finite lattice geometry and compact SU(2) link variables only.
- Excluded: continuum limits, OS/Wightman reconstruction, transfer-operator
  mass gaps, and the Clay problem.

## Physical convention

For `x,y ∈ SU(2)` and physical inverse coupling `β`, the crossing factor is

```text
Kβ(x,y) = exp ((β / 2) * Re tr (x y⁻¹)).
```

This is the non-constant part of the usual Wilson factor for
`S_W = β * Σ_p (1 - (1/2) Re tr U_p)`.  The harmless global
`exp (-β * #plaquettes)` normalization is omitted.  The sign is positive in
the Boltzmann exponent.  The existing combination of
`wilsonPlaquetteEnergy := Re tr` with a `-β * wilsonAction` tilt uses the
opposite convention and is not imported as the definition of this kernel.

## Executable gates

1. **CLOSED.** Define the exact kernel above in Lean:
   `su2WilsonCrossingKernel`.
2. Prove a non-negative expansion, or an exact substitute.  The selected
   substitute is the Taylor/Fock expansion:
   each power of `Re tr (x y⁻¹)` is a finite non-negative combination of
   rank-one kernels, and `(β/2)^m / m! ≥ 0`. **CLOSED** by
   `su2WilsonExponent_finiteRank`,
   `su2WilsonTaylor_hasContinuousPositivePresentation`, and
   `su2WilsonTaylorCoeff_nonneg`.
3. **CLOSED.** Prove the complex quadratic form is non-negative with respect to
   `sunHaarProb 2`, for every continuous complex observable in the declared
   domain: `su2WilsonCrossing_isHaarPSDKernel`.
4. **CLOSED for the declared one-plaquette geometry.** Declare and prove the
   splitting identity for a finite temporal-gauge cut
   of shape `Half × Cross × Half`, keeping geometry and integration over
   crossing variables separate from kernel positivity:
   `su2WilsonCrossingKernel_dressed` and
   `su2OnePlaquetteCutWeight_splitting`.
5. **CLOSED.** Prove a non-empty SU(2) endpoint at `β > 0`.  The pre-registered strict
   gate is: the kernel is non-constant, its value changes with `β` at an
   explicit pair, and the pairing is strictly positive for an explicit
   continuous observable.  Closed by
   `su2OnePlaquette_reflection_positive`,
   `su2WilsonCrossingKernel_nonconstant`, and
   `su2OnePlaquette_constant_pairing_strict`.
6. **CLOSED.** Build all owned Lean modules with no `sorry` or project axiom
   and record `#print axioms` output for every headline.  See
   `CERTIFICATION.md`, `SU2OSOracle.lean`, and `ORACLE-TRANSCRIPT.txt`.
7. **BLOCKED EXTERNALLY.** Obtain an independent audit satisfying the
   model/account validation, or record the precise external-audit failure
   without upgrading the result.  See `AUDIT.md`.

## Outcome and stop rule

The exact exponential kernel and compact Haar inequality both close on the
pinned toolchain.  Uniform Taylor convergence follows from
`|Re tr (x y⁻¹)| ≤ 2`; two one-variable dominated-convergence steps then pass
the iterated Haar form to the limit.  No Fubini swap over a product measure is
used.

The remaining blocker is not mathematical: the requested external model audit
did not return a response satisfying its validation contract.  The result is
therefore shipped as compiled Lean code and a draft PR, not as an audited paper.

A finite Taylor truncation is never called the exact Wilson weight, and a
`ZMod N` model is never called SU(2).
