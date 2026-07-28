# Surface mirror-determinant involution

**Registered:** 2026-07-27

**State:** exact pure-mirror algebra proved; transformed determinant sign
certificate open

## Calibration

Put `p=sin(t/4)` and `C_p=2p^2-1=-C`, where
`C=cos(t/2)`.  In mirror coordinates
`T(s,alpha)=(pi-s,pi-alpha)`:

```text
D o T = -D_p,
N_C o T = -N_{C_p}.
```

For `F_C=N_C-CD`, direct substitution gives the exact identity

```text
(F_C+2 C D) o T = -F_{C_p}.
```

The determinant is unchanged by `F -> F+2CD`, so the calibration is free.

## Determinant identity

Let `(a_p,f_p,u_p,w_p)` be the four principal moments with parameter `p`.
After the mirror transformation of the square `B'` only, and allowing one
common positive chart scale `S`, the four mirror moments are

```text
b=-S a_p,  g=-S f_p,  v=S u_p,  x=S w_p.
```

Therefore

```text
b x-g v = -S^2 (a_p w_p-f_p u_p).
```

If

```text
X_p = 4 beta^3 (a_p w_p-f_p u_p)/a_p^2,
```

then the mirror-times-mirror contribution to the grouped adverse scalar is
exactly

```text
4 beta^3 (g v-b x)/d^2 = (S a_p/d)^2 X_p.
```

In unscaled physical moments `S=1`; the displayed form records the same
identity after a common saddle normalization.

This replaces the old independent-product estimate on the pure mirror
square, `O(beta exp(-8 beta delta4))`, by a weighted transformed
determinant.  It does **not** include the rest of the torus, and it does
**not** yet prove the sign of that determinant: the required statement is
`X_p>=0` on the registered `p<1/sqrt(2)` strip.  The rest is a third block
handled by `verify_surface_three_block_decomposition.py` and its independent
Abel-layer bound.

## Reproduction

```powershell
python scripts/verify_surface_mirror_determinant_involution.py
python -m pytest -q tests/test_surface_mirror_determinant_involution.py
```
