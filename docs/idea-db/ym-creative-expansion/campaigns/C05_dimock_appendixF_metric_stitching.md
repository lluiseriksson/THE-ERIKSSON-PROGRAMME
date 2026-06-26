# Campaign C05 — Dimock Appendix F metric stitching as a reusable theorem

## Goal
Turn Dimock's metric stitching inequality into a generic Lean algebra endpoint and reuse it in Eq. (2.37) and H#.

## Formula

```text
d_M(Y mod Ωᶜ) ≤ Σ_i d_M(X_i mod Ωᶜ) + (n-1)
```

For `b ≥ 0`:

```text
Π_i e^{-b d_i} ≤ e^{-b d(Y)} e^{b(n-1)}
```

## Payoff
The target decay is extracted before overcounting, matching the target-preserving rooted-tree philosophy.
