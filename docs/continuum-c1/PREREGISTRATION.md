# CONTINUUM-C1 preregistration

Frozen in two stages.  The original Haar obstruction was frozen before its
implementation.  After round-one feedback, the following E1/E2 gates were
frozen before any E1/E2 Lean implementation.

## Dimensional contract

The lane-local contract will contain:

```text
ScaleDict.a       : ℝ,  0 < a             -- physical length
ScaleDict.g2      : ℝ,  0 < g2            -- physical g²
physicalLength n  = a n
physicalArea n    = a² n
beta2D            = 1/(g²a²)
```

For four dimensions E1 will not hard-code a perturbative coefficient: it will
consume the structurally sufficient condition `β(a) → +∞`.

## E1 — quantified no-go for the strong-coupling window

**Statement.**  Define

```text
β_max(d,N_c) =
  log(1 + exp(-3)/(16d+1)²) / N_c.
```

For `N_c>0`, `s>0`, `β≥0`, the `t=ε=1` KP radius hypothesis implies
`β<β_max(d,N_c)`.  Consequently every continuum trajectory
`β(a)→+∞` violates that hypothesis for all sufficiently small `a`.  In the
two-dimensional contract `β(a)=1/(g²a²)`, an explicit threshold is required.

**E1 failure.**  Reject the theorem if the cap contains a volume, if the
trajectory is only sampled at a fixed `a`, or if `s>0` is silently replaced by
`s=0`.

## E2 — positive two-dimensional Wilson-loop target

Boundary condition: plane/free boundary only.  Periodic tori are excluded
unless their global plaquette constraint is represented exactly.

Let

```text
n_p(a) = ceil(A/a²),
β(a)   = 1/(g²a²),
ρ(β)   = I₁(β)/I₀(β).
```

### G1 — factorization

Prove

```text
⟨W_a⟩ = ρ(β(a)) ^ n_p(a)
```

with the free boundary condition in the theorem type.

**FAILS** if any volume hypothesis, periodic global constraint, or
unidentified sign/convention remains.

### G2 — rate

Prediction frozen before calculation:

```text
|ρ(β(a))^n_p(a) - exp(-g²A/2)| ≤ 3 g⁴ A a²
```

on the explicit conservative domain

```text
g²a² ≤ 1,  a² ≤ A,  1 ≤ Ag².
```

The intended proof uses only the checked Amos bracket

```text
β/(1/2+sqrt(9/4+β²)) < ρ(β)
  < β/(1/2+sqrt(1/4+β²))
```

plus elementary real inequalities.  `C=3` is deliberately not optimized.

**FAILS** if the proof uses an unproved Bessel asymptotic, drops the ceiling
error, or produces a constant depending on volume or `a`.

### G3 — non-vacuity

Separate witness:

```text
g²=1, A=1, 0<a≤1,
limit value exp(-1/2) ∈ (0,1).
```

G3 does not count as evidence for G1 or G2.

### G4 — build and oracle

Every Lean artifact must build directly, contain no `sorry`, and use no
project axiom.  Run `scripts/check_module_prose.py` before claiming
“uniform in `a`”.

G4 does not count as evidence for G1, G2, or G3.

## Auxiliary Haar obstruction

For normalized Haar `U∈SU(N_c)`,

```text
P(a⁻⁴(N_c-Re Tr U) ≥ N_c/(2a⁴)) ≥ 1/3.
```

This remains a valid auxiliary negative result, but it is not substituted for
E1 or E2.
