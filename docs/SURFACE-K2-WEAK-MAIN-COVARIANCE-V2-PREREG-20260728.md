# Weak-main covariance v2 — denominator repair preregistration (2026-07-28)

This is the authoritative execution contract after
`INCIDENT-WEAK-MAIN-COVARIANCE-DENOMINATOR-20260728.md`.

All mathematical and partition choices from
`SURFACE-K2-WEAK-MAIN-COVARIANCE-PREREG-20260728.md` remain frozen:

```text
delta:  [0,9/1000], 18 boxes
t:      [21/10,31415927/10000000], 32 boxes
core:   [0,12]^2
grids:  24 then 48
Arb:    180 bits
target: X_main > -1/20
```

The sole instrument change is:

```text
generic KD*KD
    replaced by
monotone [KD_lower^2,KD_upper^2],
```

after the existing strict check `KD_lower>0`.

Production and replay must start from fresh paths, be byte-identical, have
empty stderr, and pass the preregistered independent transcript validator.
No result from the nonterminal first attempt may be loaded.
