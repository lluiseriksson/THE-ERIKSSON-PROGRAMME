# CONTINUUM-C1 integration note

## Ownership

C1 owns only:

- `docs/continuum-c1/**`;
- `YangMills/Continuum/TightnessScaleNoGo.lean`;
- `scripts/continuum_c1_*`.

It does not edit or import Continuum-C0 files. It also does not edit
`YangMillsCore.lean`, the global oracle, README/dashboard/ledger/project-state
files, `YangMills/RG/**`, hRpoly, or Paper 13.

## Typed C0 connection

The lane-local `ScaleDict` is deliberately minimal:

```text
structure ScaleDict where
  a      : ℝ
  a_pos  : 0 < a
  g2     : ℝ
  g2_pos : 0 < g2
```

C0 may map its eventual scale object into this structure, but C1 does not
assume that C0 exists or has any theorem. The semantic equalities are:

```text
physicalLength n = a*n
physicalArea n   = a²*n
beta2D           = 1/(g²a²)
```

For a general trajectory, downstream code may instead provide

```text
Tendsto beta scaleFilter atTop
```

and apply `eventually_not_kpRadiusAtUnit_of_tendsto`. This is the typed
connection to C0: C0 supplies a scale filter and a divergent coupling
trajectory; C1 returns eventual incompatibility with the existing KP radius.
No C0 file needs to import C1 until that contract is chosen.

## Positive successor boundary

E2 requires a separate theorem for free-boundary `U(1)`:

```text
freeBoundaryU1WilsonFactorization :
  expectation WilsonLoop =
    (Real.besseli 1 beta / Real.besseli 0 beta) ^ enclosedPlaquettes
```

Its type must expose the finite domain, boundary condition, plaquette count,
orientation, and action normalization. Periodic tori are not accepted without
their global plaquette constraint. C1 has not constructed or assumed this
bridge.

## Build boundary

Check C1 directly with:

```text
lake env lean YangMills/Continuum/TightnessScaleNoGo.lean
python scripts/check_module_prose.py \
  YangMills/Continuum/TightnessScaleNoGo.lean
```

The file is intentionally absent from the global oracle and core import
graph.
