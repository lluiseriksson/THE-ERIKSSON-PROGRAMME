# K2 covariance/MLR route: obstruction (2026-07-26)

This note records a bounded independent review of the proposed cancellation
route.  It is not a theorem claim and carries no K2, G2, or G6 promotion.

## Frozen algebra

The candidate double-integral factorization was supplied in the form

```text
2 B(x,x') = H(x) H(x') (d(x) f(x') - f(x) d(x'))
                         (r(x) d(x') - r(x') d(x)) .
```

With `Q=f/d` and `S=r/d`, the two brackets are proportional to differences of
`Q` and `S`.  The exact two-point identity therefore turns the integral into
`±2 N² Cov(Q,S)` under the positive measure `H d² dμ`; the sign is decided by
the orientation of the two displayed brackets and must be fixed from the
master formula before any covariance argument is admissible.

## Why monotone-likelihood-ratio is not a proof

For a fixed positive measure, an MLR argument reduces to a Chebyshev/FKG
argument and requires a common monotone coordinate.  The supplied leading
terms (with `C=cos²(t/4) in (1/2,1)`) are

```text
S = 4 sqrt(C) + eps*(2 sqrt(C)*(p+q) - 3/2) + O(eps²)
Q = -2(4 C-1) p + 4 eps(1-C) p q + O(eps²).
```

Thus `S_p,S_q>0` at first order, while `Q_p<0` and `Q_q>=0` near the
corner.  The Jacobian is already nonzero at first order, so pointwise
comonotonicity fails; no MLR/FKG proof follows from these expansions.

Moreover, if the carrier measure factorises in `(p,q)`, the leading covariance
is proportional to `-Var(p)` (up to the unresolved orientation).  Hence the
orientation and the exact carrier covariance are not cosmetic details: they
determine even the leading sign.

## Disposition

The minimum missing inputs are (i) the exact orientation/sign bookkeeping in
the master identity, (ii) the covariance of `(p,p+q)` under the actual carrier,
and (iii) a global remainder/concentration bound.  Without them, promoting a
covariance or MLR lemma would be unsound.  The Opus 5 Max review used only the
bounded prompt and no repository access; its conclusion was independently
checked algebraically at the level above.  A separate Fable High request on
the same question timed out and supplied no accepted result.
