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

The first missing theorem is not the finite-lattice factorization. It is the
analytic identification between the repository's Γ-series and the Fourier
integrals produced by `U(1)` Haar measure:

```text
besselIReal_integral_repr_zero (x>0) :
  AmosClosure.besselIReal 0 x =
    (1/π) ∫ θ in 0..π, exp(x*cos θ)

besselIReal_integral_repr_one (x>0) :
  AmosClosure.besselIReal 1 x =
    (1/π) ∫ θ in 0..π, exp(x*cos θ)*cos θ
```

Only after these identities can a separate free-boundary theorem identify the
Wilson-loop expectation with
`(besselIReal 1 beta / besselIReal 0 beta)^enclosedPlaquettes`. Its type must
expose the finite domain, boundary condition, plaquette count, orientation,
and action normalization. Periodic tori are not accepted without their global
plaquette constraint.

A lower-cost warm-up is the two-dimensional `U(1)` heat-kernel/Villain
action: its character coefficients give exact subdivision invariance and an
exact fixed-area Wilson expectation. Such a theorem would validate the
factorization machinery with rate zero, but must be labelled as a heat-kernel
result rather than the Wilson `O(a²)` target.

## Build boundary

Check C1 directly with:

```text
lake env lean YangMills/Continuum/TightnessScaleNoGo.lean
python scripts/check_module_prose.py \
  YangMills/Continuum/TightnessScaleNoGo.lean
```

The file imports the checked two-plaquette producer directly. It remains
absent from the global oracle and core import graph, but its own build now
fails if the checked window ceases to supply `KPRadiusAtUnit`.
