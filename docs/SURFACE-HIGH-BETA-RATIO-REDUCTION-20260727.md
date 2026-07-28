# Surface high-beta ratio reduction

**Registered:** 2026-07-27

**State:** exact `B union B'` algebra proved; two sign lemmas remain open;
the third-block rest perturbation is independently certified

## Exact reduction

Use the main moments

```text
a=muD, f=muF, u=nuD, w=nuF
```

and the corresponding principal moments at the complementary saddle
parameter `p`,

```text
a_p, f_p, u_p, w_p.
```

Under the mirror involution, with its common positive scale `S`,

```text
b=-S a_p, g=-S f_p, v=S u_p, x=S w_p.
```

Put

```text
d=a-S a_p,
rho=S a_p/a,
r=f/a,       r_p=f_p/a_p,
h=u/a,       h_p=u_p/a_p,
X_p=4 beta^3 (a_p w_p-f_p u_p)/a_p^2.
```

On the signed-mass domain, `a>0`, `d>0`, and hence `0<rho<1`.  Direct
algebra reduces the main-plus-mirror adverse scalar to

```text
adverse
 = 4 beta^3 rho/(1-rho)^2 (r-r_p)(h+h_p)
   - rho/(1-rho) X_p.
```

This is stronger than bounding the four cross products and the
mirror-times-mirror determinant independently.  Since `H_B>=0` and `D^2>=0`,
one has `h,h_p>=0`.  Therefore the two unilateral sign statements

```text
r <= r_p,
X_p >= 0
```

imply `adverse<=0` without estimating the small mirror mass.

The exact cancellation is checked by
`scripts/verify_surface_mirror_cross_decomposition.py`.

This is not yet the full torus.  The rest is added by the separate exact
identity in `scripts/verify_surface_three_block_decomposition.py`; its total
adverse contribution is certified below `1/100000` by
`scripts/verify_surface_high_beta_rest_perturbation_bound.py`.

## Principal-ratio derivative

Let `q` be a principal saddle parameter and integrate on the positive main
square.  With probability density proportional to `K_q D`, set

```text
phi_q=F_q/D,
r(q)=E_q[phi_q].
```

The exact score identity is

```text
r'(q)
 = E_q[(partial_q F_q)/D]
   + Cov_q(F_q/D, partial_q log K_q),

partial_q F_q = 16 q P(2P+Q-2),

partial_q log K_q
 = (z I_2(z)/I_1(z)) 2qD/R_q^2.
```

Here the first term is nonpositive on the registered square, while the
covariance should not be bounded independently.  The Bessel score converts
it exactly:

```text
Cov_q(F_q/D, partial_q log K_q)=4q X(q).
```

Moreover kernel symmetry and

```text
D-Phi_sym
 = 2[P(2-2P-Q)+Q(2-2Q-P)]
```

convert the explicit term.  If

```text
Q_main(q)=<Phi_sym>_q/<D>_q,
```

then the complete derivative collapses to

```text
r'(q)=4q [X(q)+Q_main(q)-1].
```

Thus principal-ratio monotonicity is not a new four-moment covariance
problem.  Its terminal scalar target is the upper inequality

```text
X(q)+Q_main(q)<1.
```

The executable derivation is
`scripts/verify_surface_principal_ratio_derivative.py`.

At `beta=infinity`,

```text
r(q)
 = -(4q-1/q) delta/2 + O(delta^2),

partial_q r(q)
 = -(2+1/(2q^2)) delta + O(delta^2),
```

which has the desired negative sign.  This is a design sanity check, not a
uniform remainder certificate.

## Minimal remaining certificate

For a fixed rational floor such as `q0=101/200`, it is enough to prove:

1. `X(q)+Q_main(q)<1` for
   `q in [q0,sqrt(1-q0^2)]`, `0<delta<=9/1000`;
2. `X(q)>=0` for `q in [q0,1/sqrt(2)]` on the same delta strip;
3. use the already certified absolute mirror bound for `q<q0`, where
   `sqrt(1-q^2)-q` has the fixed floor `7/20`.

The far mirror and the third-block rest budgets are now terminal
certificates.  The moving-edge G5 certificate remains an independent
direct-sign proof.  No paper-seal promotion follows from this note until
the two listed principal-square sign lemmas have terminal certificates.
