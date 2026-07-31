# The extent-uniformity target, pre-registered

Written before any Lean of the campaign exists.  Probe:
`scripts/probe_uniform_window.py`, committed at `8f1ac3c5` before it was run.

## What was open, and what is open now

The lane's long-standing open analytic question was stated as *"is there an
extent-uniform spectral bound for the coupled kernel?"*.  As stated the answer is
**no**, and the lane had already measured it failing: under a ring weight
`specRatio(L) -> 1` outside the disordered region.  A question whose answer is
"no" is not a target; it is a target-shaped hole.

Two measurements turned it into a target.

## 1.  The kernel is the 2D Ising transfer matrix, and that fixes the boundary

The ring-weighted coupled kernel of this lane,

    K_w(s,t) = sqrt(w(s)) * prod_j e^{beta*sign(s_j,t_j)} * sqrt(w(t)),
    w(s)     = prod_j e^{gamma*sign(s_j,s_{j+1})}    (ring),

is the symmetrised transfer matrix of the anisotropic square-lattice Ising
model, `gamma` horizontal and `beta` vertical.  Exact algebra, not analogy.
Kramers--Wannier therefore puts its critical line at

    sinh(2 beta) * sinh(2 gamma) = 1.

Measured, before the prediction was allowed to license anything: every
subcritical cell converges to a limit strictly below 1, every supercritical cell
runs to 1, and the critical cell drifts slowly.  Ten cells, all as predicted.

## 2.  THE CANDIDATE THEOREM

    specRatio(L)  <=  tanh(beta) * e^{2*gamma}        for every L

Measured over 210 cells --- `beta` in {0.05,0.1,0.2,0.3,0.4,0.5,0.7},
`gamma` in {0,0.05,0.2,0.4,0.7,1.0}, `L` in {4,6,8,10,12} --- with **zero
violations**, always approached FROM BELOW, and saturated as `L -> infinity`.

Three properties make this the right target rather than one more inequality.

**It is extent-uniform by construction.**  The right-hand side does not mention
`L`.  That is the whole content of the open question.

**Its non-triviality window is exactly the disordered phase, not a subset.**
`tanh(beta) e^{2 gamma} < 1` and `sinh(2 beta) sinh(2 gamma) < 1` define the
SAME region.  With `t = tanh(beta)`, the boundary `e^{2 gamma} = 1/t` gives
`sinh(2 gamma) = (1 - t^2)/(2t)` and `sinh(2 beta) = 2t/(1 - t^2)`, whose product
is `1`.  So the bound stops being informative exactly where uniformity actually
fails --- it does not quit early, and it does not overreach.

**It degenerates to a theorem already proved.**  At `gamma = 0` the weight is
constant and the bound reads `specRatio(L) <= tanh(beta)`, which paper 11 proves
as an EQUALITY, by induction on the extent.  A candidate that recovers a proved
theorem as its boundary case is a candidate with a proof route.

## What this licenses, and what it does not

Licensed: an attempt at `specRatio(L) <= tanh(beta) e^{2 gamma}`, and statements
about the disordered phase that follow from it.

NOT licensed: any statement outside `sinh(2 beta) sinh(2 gamma) < 1`, where
uniformity is measured to be false; any claim that the bound is sharp at finite
`L` --- it is not, it is approached from below; and any transfer of importance to
Yang--Mills, which requires a proved reduction that does not exist.

## The proof route, and where it dies

Paper 11 proves the `gamma = 0` case by induction on the extent, closing because
`tanh(beta) * Z = D`.  The ring weight breaks that induction: adding a site
changes the ring, so the weight is not a product over the induction variable.
**That is where this dies if it dies** --- not in the analysis, in the fact that
a ring has no first site.  Two escapes to try, in order: run the induction on an
OPEN chain and pay for the closing bond separately, or diagonalise the weight in
the domain-wall basis where the ring becomes a product.

## Status

Probe PASS.  No Lean written.  Nothing here is proved.
