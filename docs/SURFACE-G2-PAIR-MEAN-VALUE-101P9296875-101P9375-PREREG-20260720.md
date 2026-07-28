# G2 pair mean-value cell `[101.9296875,101.9375]` preregistration

Registered before production as the next dyadic cell after the two preceding
frontier candidates. This is candidate evidence only; it cannot promote G2/G6.

```text
beta       [13047/128,1631/16] = [101.9296875,101.9375]
lambda     [3/2,19/10]
modes      115
beta order 50
lambda order 50
Arb        500 bits
```

Production and independent replay must be byte-identical with matching
dependency hashes and a strictly negative total upper endpoint. Failure retires
this cell without changing any gate.

## Result

Production and replay passed with byte-identical SHA-256
`3b9f2f04b17668bf517d94defcac3d0c23e052c3e5714c15d785e7ed45369aec` and
strict total upper endpoint
`-3.689495216560598...e-109`. The candidate manifest is
`run-manifests/surface-scaled-pair-mean-value-cell-beta101p9296875-101p9375-lambda150-190-20260720.json`.
This remains one local candidate cell and does not promote G2/G6.
