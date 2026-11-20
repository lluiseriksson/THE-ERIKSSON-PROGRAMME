# Can three consumption curves share one payment calendar?

Supplement to *Payment timing and the interpretation of monthly consumption with exponential memory*. The three rates used in Figure 1 of [Peña Velasco and Abancín Ospina](https://doi.org/10.70577/mpwp1487) motivate this diagnostic. Their analytical curves specify an income function. The question here is different: what can be checked when only monthly amounts and model outputs survive? The examples below are synthetic.

## The attainable third increment

Fix a month of length h>0, a positive total M, and three positive rates a<b<c. For each rate d, subtract the decayed previous closing value and divide by dM. Call the resulting normalized increments u,v,w. Draw a lag with probability proportional to payment mass. With X=exp(-a lag), L=exp(-ah), p=b/a and r=c/a, the three observations prescribe the expectations of X, X^p and X^r on [L,1]. Define H_k(s,t) as the value at u of the chord of x^k between s and t:

    H_k(s,t) = ((t-u)s^k + (u-s)t^k)/(t-s),  s ≤ u ≤ t.

It suffices first to check L ≤ u ≤ 1 and u^p ≤ v ≤ H_p(L,1). At v=u^p all payments have X=u, so w=u^r. At v=H_p(L,1), all payments are at the endpoints, so w=H_r(L,1). These rules include u=L or 1. An empty month requires three zero unnormalized increments.

In the interior choose z in (u,1) and t in (L,u) to solve

    H_p(L,z) = v = H_p(t,1).

The first chord height increases continuously as z increases from u to 1. The second decreases continuously as t increases from L to u. Strict convexity proves both statements, so there is a unique root on each interval. The full interval is

    H_r(L,z) ≤ w ≤ H_r(t,1).

For a direct proof, interpolate x^r by A+Bx+Cx^p at L and z with matching first derivative at z. The linear system is invertible by strict convexity. The interpolation error f has a zero at L and a double zero at z. Its second derivative divided by x^(p-2) is r(r-1)x^(r-p) minus a constant. This is strictly increasing. Rolle's theorem gives a zero of f' between L and z and hence a zero of f'' before z. Consequently f''(z)>0 and f is positive near z except at z. No fourth zero counted with multiplicities is possible because f'' has at most one. Thus f≥0 throughout [L,1]. Interpolating instead at the double node t and at 1 places the zero of f'' after t. The error now has a strict local maximum of zero at t and is nonpositive throughout. Integrating proves the two bounds. Both are attained: use the two-node schedules implicit in the chords. Mixing these schedules at fixed u and v realizes every intermediate w. Concatenating the monthly witnesses gives the full trajectory criterion, provided the same monthly inputs and starting states are used. The closed interval is for payment measures, with endpoint payments assigned once as in the manuscript.

This is an explicit instance of the principal-representation result of [Dette and Schorning, Lemma 2.1](https://arxiv.org/pdf/1306.4872). The two scalar equations and the following exclusion specialize that classical result to the payment model.

## An exact false positive for all three pairwise checks

Set L=1/2, p=2, r=3, u=3/4 and v=19/32. Take w=1/2. All three pairwise tests pass strictly. In particular v^3<w^2, and the two upper chords for w exceed 1/2. Nevertheless the exact attainable third interval is [125/256,127/256]. The proposed 128/256 exceeds the upper endpoint by 1/256.

The lower witness puts probabilities 1/3 and 2/3 at X=1/2 and 7/8. The upper witness puts probabilities 2/3 and 1/3 at X=5/8 and 1. The inequalities can be checked without a numerical optimizer by taking expectations of (X−1/2)(X−7/8)^2 ≥ 0 and (1−X)(X−5/8)^2 ≥ 0. These certificates give both endpoints using only u and v. Here the rate ratios are illustrative.

For the article's actual rates 0.03, 0.08 and 0.15 per month the companion script also constructs a strict interior false positive. It records both intervals for a selected feasible pair in three-rates.json. This is a worked test for the rates and not a diagnosis of the original figures. A test on rounded or digitized observations must preserve their error intervals; plugging a rounded midpoint into an equality test can give a false rejection.

## Reproduction

Run three_rates.py in the programme's Linux environment with mpmath. The illustrative certificate uses exact rational arithmetic. The source-rate demonstration uses 65 decimal digits and 180 steps of bisection; its decimals are numerical approximations. The script checks 27 additional synthetic payment mixtures. The previously reviewed manuscript and its assessment have separate immutable hashes.
