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
The 1/128 cell passed production and replay with byte-identical SHA-256
`d389524c6e5264fb428dbfd501967d24f29fd6ec8c71de1126df52cc572006fb` and
strict total upper endpoint `-3.761048008210427...e-109`. The candidate
manifest is
`run-manifests/surface-scaled-pair-mean-value-cell-beta101p921875-101p9296875-lambda150-190-20260720.json`.
It remains one local cell and does not promote G2/G6.
