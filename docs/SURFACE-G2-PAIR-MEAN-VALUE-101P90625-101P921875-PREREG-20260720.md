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
