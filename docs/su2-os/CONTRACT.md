> **Scope limitation — read before the title.** `Cross` is a gauge-pure
> auxiliary variable. It does not participate in the effective weight or
> pairing, and its inversion under reflection is not exercised by this
> result. No lattice plaquette Wilson weight or physical factorization is
> derived. This geometric limitation does not weaken complex Haar positivity
> for every continuous `F : SU2 → ℂ` or the sharp bound `Qβ(tr) ≥ β/4`.

# SU(2) Wilson Haar-positivity contract

## Freeze

- Published base: `origin/main`
- Full base SHA: `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`
- Branch: `codex/su2-wilson-reflection-positivity`
- Scope: an exact compact-SU(2) Haar kernel and a gauge-pure auxiliary cut.
- Excluded: continuum limits, OS/Wightman reconstruction, transfer-operator
  mass gaps, the Clay problem, and a derived lattice plaquette geometry.

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
The product-form auxiliary identity below is explicitly not a gate:
`su2OnePlaquetteCutWeight` is defined in product form, and
`su2OnePlaquetteCutWeight_eq_undressedKernel` proves only that its common
gauge-pure transporter cancels from the dressed kernel. Consequently,
`su2OnePlaquetteReflectedPairing_eq_kernelIntegralForm` identifies the
declared auxiliary pairing with the analytic kernel form; it does not derive
a lattice Wilson weight or exercise inversion of `Cross`.

5. **CLOSED.** Prove a non-empty analytic SU(2) result at `β > 0`.  The kernel is
   non-constant, its value changes with `β` at an explicit pair, and the
   pairing is strictly positive for an explicit continuous observable.
   Closed by
   `su2OnePlaquette_reflection_positive`,
   `su2WilsonCrossingKernel_nonconstant`, and
   `su2OnePlaquette_constant_pairing_strict`.
   The stronger preregistered zero-mean character gate
   `Qβ(trace) ≥ β / 4` is also closed by
   `su2GaugePureCut_trace_pairing_positive_sharp`; see `SHARP-GATE.md`.
6. **CLOSED.** Build all owned Lean modules with no `sorry` or project axiom
   and record `#print axioms` output for every headline.  See
   `CERTIFICATION.md`, `SU2OSOracle.lean`, and `ORACLE-TRANSCRIPT.txt`.
   The documentary canary `scripts/check_su2_os_honesty.py` rejects the
   reintroduction of the removed geometric labels.
7. **SUSPENDED.** No terminal external audit is consumed by this repair.
   A fresh blind pre-audit of the repaired source is pending; see `AUDIT.md`.

## Outcome and stop rule

The exact exponential kernel and compact Haar inequality both close on the
pinned toolchain.  Uniform Taylor convergence follows from
`|Re tr (x y⁻¹)| ≤ 2`; two one-variable dominated-convergence steps then pass
the iterated Haar form to the limit.  No Fubini swap over a product measure is
used.

This repair does not declare its own audit result. Gate 7 is suspended and a
fresh blind pre-audit of the repaired source is pending. The result remains
compiled Lean code in a draft PR, not an audited paper.

There is also a typed integration blocker outside the owned producer: the
published `ReflectionSplitting` theorem cannot consume compact SU(2).  The
autonomous endpoint uses the new Haar producer directly; it is not represented
as an instance of the finite `ZMod N` theorem.  See `INTEGRATION-NOTE.md`.

A finite Taylor truncation is never called the exact Wilson weight, and a
`ZMod N` model is never called SU(2).
