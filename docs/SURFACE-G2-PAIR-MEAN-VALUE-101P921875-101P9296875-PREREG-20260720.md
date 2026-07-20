# G2 pair mean-value cell `[101.921875,101.9296875]` preregistration

Registered before production after the failed wider half-cell.

```text
beta       [6523/64,13047/128] = [101.921875,101.9296875]
lambda     [3/2,19/10]
modes      115
beta order 50
lambda order 50
Arb        500 bits
```

Production and independent replay must be byte-identical, with matching
dependency hashes and a strictly negative total upper endpoint. This is one
candidate cell only; a pass does not infer the adjacent interval or promote
G2/G6. A failure retires this configuration without changing the theorem.
