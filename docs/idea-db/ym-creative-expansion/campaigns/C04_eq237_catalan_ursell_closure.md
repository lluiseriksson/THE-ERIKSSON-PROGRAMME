# Campaign C04 — Eq. (2.37) final summation via target-preserving/Catalan closure

## Goal
Close or sharpen the final post-(2.37) summation once fixed-Z0' estimates are supplied.

## Two-step candidate

1. Metric extraction:

```text
d(Y) ≤ Σ_i d(X_i)+(n-1)
=> Π_i exp(-b d(X_i)) ≤ exp(-b d(Y)) exp(b(n-1))
```

2. Component entropy closure:

```text
Σ_n Catalan(n) * (A K0 exp(b))^n < ∞, if A K0 exp(b) < 1/4.
```

## Safe version
Use the verified `4^n` tree bound first. Keep Catalan as optional conditional improvement until the general Catalan identity is closed in Lean.
