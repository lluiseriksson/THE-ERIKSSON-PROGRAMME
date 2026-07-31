# Preregistered sharp non-vacuity gate

Date: 2026-07-31

For `β > 0`, let

```text
F(U) = tr U
Qβ(F) = ∫ x, ∫ y, conj(F(x)) Kβ(x,y) F(y) dHaar(y) dHaar(x).
```

The target is:

```text
∫ F dHaar = 0
Qβ(F) = r with β / 4 ≤ r.
```

The value `β / 4` is fixed before the Lean proof.  It is the degree-one
Taylor contribution:

```text
(β / 2) * Σ i,j |∫ conj(Uᵢⱼ) tr(U) dHaar(U)|²
  = (β / 2) * Σ i,j |δᵢⱼ / 2|²
  = β / 4.
```

The constant Taylor term must contribute exactly zero because `F` has Haar
mean zero.  Every degree at least two must enter through a separately proved
positive finite-rank tail; pointwise positivity of the Wilson kernel is not an
acceptable proof of this gate.

If the pinned Lean infrastructure cannot certify the monotone Taylor-tail
passage, the weaker `F = 1` strict pairing remains labelled only as a
non-nullity witness.  The `β / 4` inequality must not be weakened or reported
as proved by numerical evidence.

## Current status

- **CLOSED:** the observable is continuous.
- **CLOSED:** its Haar mean is exactly zero:
  `su2TraceObservable_haar_mean_zero`.
- **CLOSED:** Schur orthogonality on `sunHaarProb 2` gives the four entry
  moments exactly: `su2TraceEntryMoment_eq`.
- **CLOSED:** the degree-one quadratic form is exactly `β / 4`:
  `su2Trace_degreeOne_eq`.
- **CLOSED:** the finite two-term Taylor head, including the vanishing
  constant mode, is exactly `β / 4`: `su2Trace_taylorTwo_eq`.
- **CLOSED:** every finite Taylor tail beginning at degree two has a
  non-negative quadratic form:
  `su2WilsonTaylorTail_isHaarPSDKernel`.
- **CLOSED:** dominated convergence transports the lower bound to the exact
  crossing kernel: `su2Trace_crossing_lower`.
- **CLOSED:** the declared reflected one-plaquette pairing is a real number
  `r ≥ β / 4 > 0` for `β > 0`:
  `su2OnePlaquette_trace_reflection_positive_sharp`.

The finite head is proved by bare integral linearity and the repository's
fundamental Schur theorem, not by unfolding the eight-real-feature positive
presentation.  The positive-presentation machinery is reserved for the tail.
