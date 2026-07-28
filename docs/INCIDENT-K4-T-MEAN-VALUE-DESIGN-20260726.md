# Incident — K4 t-mean-value route does not close the endpoint strip

Date: 2026-07-26  
Scope: design probe only; no K4, G6, S1''' or S2''' promotion.

## Question

The current K4 endpoint cover fails only the `nuD_main` budget on
`t=[2.97,2.975]` (total fraction `1.03914976867858`).  A proposed rescue was
the centred first-order mean-value form in `t`:

```text
sup_T |nu| <= |nu(t_mid)| + (width(T)/2) sup_T |d nu/dt|.
```

The proposal would require a signed derivative sum on the existing spatial
partition; it cannot be justified by summing absolute cell derivatives.

## Reproduction

Using the authoritative design imports and `ctx.prec=140`, the existing
`adaptive_integral` on the second delta segment `[0.049,0.05]` returns, at the
degenerate point `t=2.97125`, `1152` cells and `99` fallback cells.  The
aggregated intervals are already wide (for example
`nuD_main = [+/- 88.7]`), not the narrow point values required by the proposed
mean-value charge.  The same behaviour occurs at `t=2.97` and `t=2.97375`.

At `max_cells=576`, a central finite-difference probe with `epsilon=1e-4` at
`t=2.97125` gives the following *non-certified design quantities*:

```text
nuD_main midpoint radius 1.62e+3
nuD_main difference-quotient radius 1.60e+7
nuD_main charged fraction 176.6462
```

The other six rows are likewise far above one.  These numbers are not a
proof of a mathematical obstruction; they show that the current fallback
partition cannot supply the missing derivative enclosure.

## Consequence

No derivative route is promoted.  A valid rescue must first provide a new
rigorous nested `t`/spatial jet (or another cancellation-preserving majorant)
with explicit treatment of cutoff junctions, Bessel branch domains, and
differentiation under the fixed-domain integral.  Until that exists, the
authoritative state remains:

```text
K4_OPEN; G6_BLOCKED; S1'''/S2''' not discharged; DO_NOT_SUBMIT.
```

The failed route is retained as a design incident so it cannot be silently
reintroduced as evidence.

