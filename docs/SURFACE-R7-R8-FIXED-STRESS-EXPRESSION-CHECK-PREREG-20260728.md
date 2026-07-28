# R7/R8 fixed-stress expression check — preregistration (2026-07-28)

This check is an independent pointwise corroboration of the sparse exact
coefficient-list derivation.  It deliberately rebuilds the regularized
carrier as ordinary SymPy expressions and obtains its delta coefficients
with `sympy.series`; it does not import or call the sparse list-series
engine.

The fixed rational point is

```text
c_* =
7484994219661651049780560241386956279152584601396431 / 10^52.
```

It is tied to the stress point `t=2.9` by `c=cos(t/4)=cos(29/40)`.
The checker must verify, using exact rational arithmetic, that `c_*` lies
between the order-18 and order-19 alternating Taylor partial sums for
`cos(29/40)`.  Hence both `c_*` and the true cosine lie in the same explicit
rational interval.  This localization is only a point-selection guard; it
does not turn a pointwise check into an interval proof.

## Frozen acceptance contract

Acceptance requires all of the following.

1. The expression engine uses nine retained delta coefficients, obtains the
   exact cancellation `B(0)=0`, divides by the single regularizing delta, and
   returns `Y0,...,Y7`.
2. No returned coefficient contains a SymPy `Float`.
3. At `c=c_*`, all eight coefficients equal the already frozen exact targets
   in `surface_remainder_delta0_exact_targets.py`.
4. The exact Taylor inequalities
   `S_19 < c_* < S_18` hold, where `S_k` is the cosine partial sum through
   term `k`.
5. Production and replay terminate successfully, print exactly eight
   `Yj_MATCH` lines, have empty stderr, and have byte-identical stdout.
6. The transcript records Git HEAD, Python and SymPy versions, and SHA-256
   hashes of the checker, target module, and this preregistration.

A pass is only an independent exact **pointwise** corroboration near the
stress point.  It does not establish a functional identity in `c`, a
complex-disk bound, the true-companion estimates, K2, K4, or the Surface
Theorem.
