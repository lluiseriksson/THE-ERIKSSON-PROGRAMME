# Surface K2 direct joint-remainder relay

**Registered:** 2026-07-27

**State:** exact algebra verified; theorem-role promotion still pending

## Why this record exists

The regular K2 certificate proves a bound for the assembled carrier `Y`.
It does **not** prove the older manuscript statement about a separately
defined chain tail `tau`.  No identity in the manuscript equates those two
remainders, so the sentence “Consequently `(H_tail)` holds” is not admissible.

The valid route is stronger and simpler: replace the split
`extracted remainder + unextracted tau` bookkeeping by the already certified
joint remainder.

## Exact normalization

Put `delta=1/beta`.  For the main-saddle moments in manuscript notation, set

```text
X_main = 4 beta^3 (mu_D nu_F - mu_F nu_D) / mu_D^2.
```

The regular code applies one common positive scale
`S=beta^(3/2) exp(-4 beta c)` to the four moments:

```text
KD  = S mu_D,    KF  = S mu_F,
HDD = S nu_D,    HDF = S nu_F.
```

Any common quadrant multiplicity cancels in the same way.  Therefore the
code's quotient is exactly

```text
Y = 4 beta^4 (KD HDF - KF HDD) / KD^2 = beta X_main = X_main/delta.
```

This identity is checked symbolically by
`scripts/verify_surface_k2_direct_joint_relay.py`.

## Exact implication

The certified K2 statement

```text
abs(Y - T - r2 delta) <= Theta3 delta^2
```

implies, merely by multiplication by the positive number `delta`,

```text
abs(X_main - T delta - r2 delta^2) <= Theta3 delta^3,
```

and hence

```text
abs(X_main - T delta)
    <= (abs(r2) + Theta3 delta_max) delta^2.
```

On the certified half-line, `delta_max=9/1000`, and

```text
9/1000 < 1/15 < 2/15.
```

Thus the direct coefficient is strictly smaller than the manuscript's
conservative old coefficient
`R1=abs(r2)+2 Theta3/15`.  If the already proved mirror estimate is written as

```text
abs(X_full-X_main) <= M(c,beta),
```

the triangle inequality gives the extraction lemma's displayed conclusion
without introducing `(H_tail)` at all.

## What remains before promotion

1. The paper must define `Y`, `X_main`, and the moment normalization exactly
   as above.
2. The certificate proof must define its executed charges:
   `C4` is the outward upper bound for the fourth normalized coefficient
   assembled after the core/annulus completion; `C_value` is the
   componentwise determinant perturbation caused by the moving physical band
   plus the Bessel-companion errors.
3. The role audit must verify that the certified K2 union, the moving-edge G5
   union, and the unconditional mirror bound cover their stated domains with
   no overlap gap.
4. Only after those checks may the manuscript replace its conditional
   `(H_tail)` prose.  This record does not itself promote K2, G2, or G6.

## Reproduction

```powershell
python scripts/verify_surface_k2_direct_joint_relay.py
python -m pytest -q tests/test_surface_k2_direct_joint_relay.py
```
