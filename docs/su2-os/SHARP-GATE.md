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
- **OPEN:** expose the exact finite-rank sum-of-squares value without
  duplicating the large integral proof term.
- **OPEN:** prove that every Taylor tail beginning at degree two has a
  non-negative quadratic form and pass the lower bound to the exact limit.
- **NOT CLAIMED:** `Qβ(trace) ≥ β / 4`.

An attempted refactor of the existing finite-rank theorem reached Lean's
linters without logical errors, but the build process failed to materialize
the `.olean` artifact after several minutes.  The change was removed and the
previous green theorem restored.  This resource/elaboration failure is not
treated as a proof or as a mathematical obstruction.
