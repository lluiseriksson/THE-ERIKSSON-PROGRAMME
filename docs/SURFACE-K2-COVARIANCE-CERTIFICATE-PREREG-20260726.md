# K2 centered covariance certificate — nominal design preregistration

This is a nominal conditioning test of the exact covariance decomposition for
the factorized bilinear. It is fixed to `delta=0`, point `t=2.90`, spatial
side 12, grids 12 and 24, and Arb precision 140 bits. It omits all Bessel
companion and outer-domain tails and carries no K2/G2/G6 promotion.

For `dμ=H d^2 dx`, `a=(g/delta)/d`, and `b=f/d`, the exact identity is

```text
B/delta = -M^2 Cov_{μ/M}(a,b),   M=∫dμ.
```

The implementation computes cell masses and weighted means, evaluates the
between-cell covariance after midpoint centering, and bounds within-cell
covariance from certified first-derivative oscillations. Acceptance is only a
conditioning report: it prints the resulting interval and its radius. A
negative or wide interval is a terminal rejection of this nominal route; a
small interval does not imply a theorem until tails, delta jets, and the R3
budget are added.
