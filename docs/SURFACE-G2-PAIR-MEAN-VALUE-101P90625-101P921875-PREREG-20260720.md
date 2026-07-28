# G2 pair mean-value cell `[101.90625,101.921875]` preregistration

Registered after the failed 1/32-width diagnostic, before running this new
cell. This is candidate evidence only and cannot promote G2 or G6.

```text
beta       [3261/32,6523/64] = [101.90625,101.921875]
lambda     [3/2,19/10]
modes      115
beta order 50
lambda order 50
Arb        500 bits
```

The existing mean-value driver is unchanged. Production and independent replay
must be byte-identical, with matching dependency hashes and a strictly
negative total upper endpoint. A pass supplies one narrow candidate cell only;
the failed parent, the remaining finite-beta union, sign-to-`H_tail` relay,
and G2 audit remain open.

## Result

Production and replay passed with the same SHA-256
`a7d9cfb8009af7f6952da90e70dd44a890487a46603409dd178353f7ed3ed993` and
strict total upper endpoint
`-3.736846365849948...e-109`. The candidate manifest is
`run-records/legacy/surface-scaled-pair-mean-value-cell-beta101p90625-101p921875-lambda150-190-20260720.json`.
This remains one narrow cell; it does not repair the failed 1/32 parent or
promote G2/G6.
