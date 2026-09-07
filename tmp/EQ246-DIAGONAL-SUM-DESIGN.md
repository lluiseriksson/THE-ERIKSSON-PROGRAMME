# Eq. (2.46) bare diagonal branch: finite alias sum design

Status: static design checkpoint; no compiler claim.

The bare noncentral branch of
`cmp89Eq246StabilizedAliasFullSolution` is the literal quotient
`source m / fine m`.  It must not inherit the scale-uniform averaging weight
used by the rank-one correction.

The sealed noncentral complex gap supplies the pointwise inverse-Laplacian
factor `O(||q_m||^{-2})`.  The already sealed theorem
`cmp89Eq251AliasExcessProduct_div_euclideanNorm_rpow_le`, specialized to
`d = 4` and `alpha = -1`, has `beta = 1 - alpha = 2` and therefore gives

```
  (prod_mu (1 + |2*pi*m_mu|)^(1/2)) / ||q_m||^2 <= 3^2.
```

Equivalently, every noncentral diagonal summand is dominated by the explicit
factor `9` times the product weight with one-dimensional exponent `1/2`.
No infinite series is available or required at this exponent.

The remaining quantitative lemma is finite.  A concrete conservative target
with no hidden constant is:

```
  cmp89Eq251CenteredOneDimensionalAliasSum N (1/2)
    <= 4 * sqrt (N + 1).
```

The existing exact product factorization in
`BalabanCMP89Eq251MultidimensionalAliasProduct` then yields the four-
dimensional bound

```
  centeredAliasSum_4 N (1/2) <= 256 * (N + 1)^2,
```

which is the required `O((L^j)^2)` value scale for `N = L^j`.  Replacing this
step by alias cardinality would give `O(N^4)` and is not accepted.

Suggested proof of the one-dimensional lemma: enlarge the centered interval
to the symmetric window `[-N,N]`, split at zero, use evenness of the weight,
and dominate the positive tail by

```
  f(x) = (1 + x)^(-1/2).
```

`AntitoneOn.sum_le_integral` gives the comparison with the integral on
`[0,N]`.  Use `intervalIntegral.integral_comp_add_right` followed by
`intervalIntegral.integral_rpow`; the integral is
`2 * (sqrt (N + 1) - 1)`.  The central term plus twice the positive tail is
therefore at most `4 * sqrt (N + 1)`.  This route deliberately spends the
harmless constant four to avoid parity-sensitive endpoint bookkeeping.

Keep the finite-window scale visible in the theorem statement; do not route
through the divergent infinite `s = 1/2` series.  The acceptance gate for the
four-dimensional corollary is that the exact product factorization is cited,
so the exponent two is obtained by construction rather than by a cardinality
bound.
