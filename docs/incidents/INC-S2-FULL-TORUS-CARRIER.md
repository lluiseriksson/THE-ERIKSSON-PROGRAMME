# INC-S2 — full-torus carrier registered for a main-saddle tail

**Opened:** 2026-07-12
**Status:** `OPEN`; `CARRIER_IDENTIFIED`; `CERTIFICATE_PENDING`

## Finding

The inherited S2 design named `Y=X/delta` but its only executable prototype,
`cascade4_presmoke.py`, formed `X` from all seven physical torus regions. That
is not the carrier of `(H_tail)`: the expansion

```text
X_main = T(c) delta + r_2(c) delta^2 + ...
```

is derived on the main saddle block. The mirror block is controlled
separately by `M` and `(H_cube)`. Mixing it into S2 double-counts that block
and produces a function incompatible with the registered `Theta_3` budget.

## Reproducible design evidence

Independent Gauss--Legendre quadrature with scaled Bessel functions gives,
at `t=2.9`, for the full-torus `Y`:

```text
beta 15: -0.7073469
beta 20:  0.0249078
beta 30:  0.3544025
```

whereas the main physical square `[0,1.2]^2` gives:

```text
beta 15: 0.3919840
beta 20: 0.3888442
beta 30: 0.3822452
```

and tends toward `T(c)`. A 260-node design profile estimates the main
weighted integral at about `0.00724`, versus the registered allowance
`Theta_3(c) delta_final / beta_1 = 0.01273`. These numbers design the
certificate only; they carry no theorem load.

## Repair contract

1. S2''' applies only to the main-saddle normalized carrier.
2. Mirror and far-region costs remain in their already named `M`/cube lanes.
3. The carrier is built from exact Arb jets of `K,KD,KF,HDD,HDF`; no finite
   differences or Gauss quadrature may certify it.
4. K2 still supplies the analytic `[0,delta_*]` extension.
5. G2 remains open until the literal weighted Arb sum passes with margin.

The executable exact-jet and adaptive-integration work lives in
`scripts/surface_remainder_y_carrier.py` and
`scripts/surface_remainder_y_integrator.py`.
