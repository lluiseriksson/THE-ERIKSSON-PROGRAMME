# G2 pair mean-value cell `[101.90625,101.96875]` preregistration

Registered before production. This is candidate evidence only and cannot
promote G2 or G6.

Frozen cell:

```text
beta       [3261/32,3263/32] = [101.90625,101.96875]
lambda     [3/2,19/10]
modes      115
beta order 50
lambda order 50
Arb        500 bits
```

The existing mean-value driver and its explicit mode/tail derivative bounds
are used without modification. Production and independent replay must have
identical transcripts, exact dependency hashes, and a strictly negative total
upper endpoint. A pass supplies one candidate cell only; the full finite-beta
union, the sign-to-`H_tail` relay, and the global G2 audit remain open.
