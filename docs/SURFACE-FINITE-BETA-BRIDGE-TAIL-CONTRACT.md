# Finite-beta scaled bridge: audited infinite-tail contract

**Status:** `AUDITED`; applies to the finite scaled-left production only.
It does not close the scaled bulk or the positive-delta regular lane.

This note supplies the analytic tail argument required by the pre-registration
in `SURFACE-FINITE-BETA-BRIDGE-PREREG.md`.  The production and independent
rerun transcripts enumerate all 912 rational beta intervals between `20` and
`1000/9`, and all their normalized and ordinary `t` rows.  The tail argument
below is the common justification for every row.

## Coefficient ratios

Write `J_n(x)=exp(-x) I_n(x)`.  The common positive factor `exp(-4x)`
multiplies both coefficient families and cancels from the sign of the
Wronskian.  For `x>0`, the elementary Bessel-series ratio gives

```text
J_{n+1}(x)/J_n(x) = I_{n+1}(x)/I_n(x) < x/(2(n+1)).
```

For a beta box `[x_-,x_+]` and `k=M+1`, the production code uses the
monotone majorant

```text
q_m     = x_+/(2(m+1)),       q_prev = x_+/(2m),
r_b(m)  = (m+1)/m * q_m^4,
r_a(m)  = q_m^2*q_prev^2 * (m+(m+2)q_m^2)/(m-1).
```

The first expression bounds `b_{m+1}/b_m` for `b_m=m J_m^4`.  For
`a_m=(m-1)J_{m-1}^2J_m^2+(m+1)J_m^2J_{m+1}^2`, applying the same ratio to
the two positive summands and factoring the lower summand gives the second
expression.  Every factor is decreasing in `m`, so the single value at `k`
is a valid geometric ratio for all subsequent indices.  The frozen choices
`M=floor(x_+)+55` and `x_+<=1000/9` give `r_a(k),r_b(k)<1/2` on every
production interval; this inequality is checked by the executable contract
test `scripts/verify_surface_scaled_tail_contract.py`.

## Beta derivatives

The exact recurrence

```text
J_n'=(J_{n-1}+J_{n+1})/2-J_n
```

together with `I_{n-1}/I_n=I_{n+1}/I_n+2n/x` implies

```text
|J_n^(q)| <= [2(1+2n/x_-)]^q J_n.
```

Each coefficient is a positive sum of degree-four adjacent products.  Leibniz
therefore gives the registered bound

```text
|c_m^(q)| <= [8(1+2(m+1)/x_-)]^q c_m,
```

where the factor `8` (rather than the unscaled factor `4`) accounts for the
`exp(-x)` term in each of the four Bessel factors.  Multiplying by `m^r`
for the `r`-th `t` derivative preserves a decreasing geometric ratio after
the explicit factor `(m+1)/m)^r` is included.

If `c_k` is the first omitted coefficient and `r` is the frozen ratio, the
remaining series is enclosed by the positive finite sum followed by
`term*r/(1-r)`.  This is exactly the implementation in
`scaled_general_derivative_tail`; no numerical differentiation or
quadrature tail is used.  The contract test compares the majorant with direct
12-term scaled sums for both coefficient families, derivative orders `0..4`,
and `t` weights through the production order.  The production validators then
check the resulting strict sign row-by-row.

This note is an analytic dependency of the finite-beta scaled-left rows only.
It is not used to infer the still-open scaled bulk, K2 positive births, K4, or
the global theorem seal.
