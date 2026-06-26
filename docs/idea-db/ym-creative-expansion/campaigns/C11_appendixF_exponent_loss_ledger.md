# C11 — Appendix-F exponent-loss ledger

Goal: turn losses such as `3*kappa0+3`, `5*kappa0+5`, and `6*kappa0+6` into explicit reusable records.

Why:
- prevents accidental double-spending of decay;
- helps compare CMP116 and Dimock routes;
- makes margin calculations visible.

Candidate theorem:
```lean
def EffectiveKappa := kappa - coverLoss - clusterLoss - ursellLoss
```
with positivity/nonnegativity lemmas and source-key annotations.
