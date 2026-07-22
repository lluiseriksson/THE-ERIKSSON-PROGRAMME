# Independent K4 regular-ball design memo

**Source:** bounded Fable High request, verified model `claude-fable-5`,
2026-07-22.  This is design guidance, not a proof or a promotion.

The missing certificate is a simultaneous coefficient-and-tail enclosure for
all seven integrated carrier masses and their first two delta derivatives on
an interval reaching at least `delta=59/2000`, so that it overlaps the
positive-delta centred cover.  It must include explicit Taylor coefficients,
a uniform complex-disk modulus on `|delta|<=7/100`, both moving phi and
spatial tails with two delta derivatives and boundary terms, and a t-uniform
version or a preregistered t-box family.  The existing real coercivity,
complex-disk, Poisson, transport, and convergence oracles do not provide any
of these modulus or tail bounds.

The complex-disk gate only controls the branch `sqrt(1-delta A)`.  It does
not bound the modulus of the exponential, cosine/prefactor, cutoff jet, or
the moving tails.  A minimal reach-feasibility probe is therefore registered
separately: estimate a crude complex modulus at `rho=7/100`, `R=4`, and a
fixed phi head `Phi=4*pi`, then evaluate the second-derivative Cauchy tail at
`delta=59/2000` for degrees `N<=16`.  If no degree meets the preregistered
headroom test, the current regular-ball architecture cannot reach the
positive cover without a larger complex disk or a different majorant.
