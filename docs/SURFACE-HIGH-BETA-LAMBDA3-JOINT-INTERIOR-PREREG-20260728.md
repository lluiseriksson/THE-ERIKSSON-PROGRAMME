# High-beta joint interior splice at lambda three

**Registered:** 2026-07-28, before the terminal Arb sweep

**State:** frozen successor to the independent-maxima absolute ledger

## Claim

On

```text
beta>=1000/9,
lambda=beta(pi-t)>=3,
p=sin(t/4)>=101/200,
```

certify the main-plus-mirror adverse correction by retaining the common
physical variable `x=pi-t` until after all moment bounds and the mirror
mass ratio have been combined.  The fixed-gap certificate continues to
handle `p<=101/200`.

## Repaired dependency structure

The earlier absolute certificate separately maximized

```text
R_p, H_p, X_p, R_c, H_c, rho
```

over their full marginal ranges and multiplied the maxima afterward.  This
is rigorous but pairs the largest `R_p`, attained near `p=101/200`, with
the largest mirror ratio, attained near `p=1/sqrt(2)`.  Those configurations
cannot coexist.

For each rational `x` box, the new judge evaluates the already proved
principal-square bounds at

```text
p=sin((pi-x)/4), c=cos((pi-x)/4)
```

and forms in that same box

```text
rho/(1-rho)^2 * 4(R_p+R_c)(H_p+H_c)
  + rho/(1-rho) X_p.
```

Only the completed adverse expression is then maximized.  No sign
assumption or numerical quadrature is added.

## Frozen sweep

Split

```text
x_split=3/(1000/9)=27/1000,
x_max=103/100.
```

Use 512 boxes on `[0,x_split]` with `beta>=3/x`, and 2,048 boxes on
`[x_split,x_max]` with `beta>=1000/9`.  Retain 180-bit Arb and the same
principal-square mass and moment formulas as the certified lambda-four
splice.

The terminal targets are

```text
rho<1/25,
joint adverse correction<9/10.
```

Together with `Q>19/20` and the third-block rest `<1/100000`, the frozen
relay margin is

```text
19/20-9/10-1/100000=0.04999>0.
```

Production and replay must bind one source head and exact dependency
hashes.  A non-strict endpoint rejects the route.
