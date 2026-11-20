# The range of the first saturation correction

Use the independent common-cap model, the weighted stratum Q at S=m+h, the extra-hit vector E, and the unrestricted count C(m,h)=binom(m+h-1,h) from the [allocation theorem](surplus-allocation.md). Fix n>=3. For any admissible labelled vector e, write b(e) for the number of entries n-1. Uniformly over e, for 1<=h=o(m^(2/3)),
\[
 C(m,h)Q(E=e)=\exp[-n(n-1)b(e)h/m](1+o(1)).
\]
The error is relative even if the displayed exponential tends to zero. The exponent 2/3 cannot be increased in a statement uniform over fixed caps: at cap four we give a profile with b=0 for which the claimed equivalent fails when h is of order m^(2/3).

**Conditional density.** Use the exact unrestricted urn formula D_R(e) in the allocation theorem. Let d=R-h, w=n b(e) and let R<=Kh for a fixed K>2n. Before conditioning, the probability any of the m colours appears n times in R draws is at most the expected number of single-colour n-tuples of positions, bounded by O_n(R^n/m^(n-1)). This is O_K(h^3/m²) for n>=3. In the numerator, the probability of avoiding the b initially saturated sites is exactly the product over 0<=j<d of (1-w/(m+h+j)). Its log is -w d/m+O_K(h^3/m²). Given avoidance, at most h initially occupied unsaturated colours can overflow after two or more new draws. Their chance of any overflow is O_K(h d²/m²), by the two-draw union bound since each has initial weight at most n. Empty colours have overflow probability O_K(d^n/m^(n-1)). The total initial weight after conditioning on avoidance is m+h-w, of order m. Dividing by the unconditioned cap probability gives D_R(e)=exp(-w d/m)(1+O_K(h^3/m²)) uniformly on this range.

**Effect of the random suffix length.** For bounded h the earlier sub-square-root theorem already suffices. Take h tending to infinity. Write a=(m+h)/(mn), u_0=h/a. There are constants depending only on n such that for x>=2
\[
 \Pr(|R-u_0|>x)\le C\exp[-c x^2/(h+x)].
\]
For the upper tail count hits in the last floor(u_0+x) slots: when R exceeds that length the count is at most h, against mean h+a x+O(1). For the lower tail use the last ceil(u_0-x) slots, whose count is at least h+1 when these slots include the m-th hit. Adjust constants for rounding, empty tails and bounded x. Hoeffding's inequality at these sample sizes gives the displayed bound. [Hoeffding, 1963](https://doi.org/10.1080/01621459.1963.10500830).

For theta=w/m, theta sqrt(h)=o(1). Integrating theta exp(theta x) against this tail bound shows E exp(theta |R-u_0|)=1+o(1) uniformly in w: below h complete the square in the Gaussian integral to bound the excess by O(theta sqrt(h) exp(C theta² h)); above h use exponential decay. Moreover |u_0-nh|=O_n(h²/m) and theta h²/m=o(1). Consequently
\[
 E\exp[-w(R-h)/m]=\exp[-w(n-1)h/m](1+o(1)).
\]

To discard R>Kh in the actual density, take K sufficiently large. The order-statistic tail bounds give probability at R=u at most exp(-c_n u) there. For u<=delta m the distinct-colour lower bound on the urn cap probability gives D_u(e)<=exp(C u²/m); choose delta to absorb this in half the tail exponent. Above delta m use D_u(e)<=C(m,h)=exp(o(m)). Thus the contribution is exponentially small in h, even relative to the proposed factor, which is at least exp(-O_n(h²/m)). The same tail bound discards this range in the Laplace expectation. This proves the equivalent for unbounded h, and hence by subsequences for the full stated range.

**A second transition from tasks near saturation.** At cap n=4 take h even, h/m^(2/3) tending to c>0, and choose e with h/2 entries equal to two and all others zero. Its saturation count b vanishes. Nevertheless
\[
 C(m,h)Q(E=e)\ \longrightarrow\ \exp(-27c^3).
\]
Here R/h tends to four and d/h to three by the preceding count concentration. Conditional on R=O(h), before fixing e the chance of overflow is O(R^4/m³)=o(1). After fixing e, empty colours contribute another o(1) by the same bound. Each of the h/2 occupied colours starts with weight three and overflows on receiving at least two new draws. Let V count these overflows. Given a deterministic sequence d/h tending to three, the probability of V=0 tends to exp(-27c³), as follows.

For l fixed, the joint expectation of the product of binom(X_i,2) at l specified occupied sites, where X_i counts new draws there, is
\[
 (d)_{2l}\,6^l/(m+h)^{\overline{2l}} .
\]
Parentheses without an overline denote falling factorials. This identity follows from choosing disjoint pairs of draw positions and the urn predictive probabilities at these positions; the initial rising weight per pair divided by 2! is six. Replacing each binomial by its indicator X_i>=2 changes the expectation by at most O_l(d/m) times this quantity. Indeed the pointwise discrepancy is at most three times binom(X_i,3), and replacing one pair by a triple in the same joint formula adds O_l(d/m). Multiply by (h/2)_l. The resulting factorial moments of V tend to (27c³)^l. Upper and lower inclusion-exclusion sums of any fixed consecutive even and odd orders now bound the probability of V=0. Taking the orders to infinity gives exp(-27c³). The conditional bounds apply along every sequence d/h tending to three. The denominator is uniformly near one on R<=Kh; the earlier exponentially decaying estimates handle the tail R>Kh. Averaging proves the counterexample.

Under the same scaling the all-ones profile, also with b=0, instead has normalized density tending to one. Its h initially occupied sites need three additional hits apiece, costing O(h d³/m³)=o(1); each empty site needs four. Thus even profiles with equal surplus and equal saturated count can have different limiting probabilities on this scale. Both statements describe labelled allocations in the synthetic stopped experiment.

**Verification.** The [finite certificate](cubic-allocation.py) evaluates the exact stratum formula with outward rounding, for six cap-four banks from 3 to 1728 tasks. It checks both profiles against full binary enumeration at three tasks. The largest design has h=36 and c=1/4. The finite intervals and the limit have distinct roles: the limit follows from the displayed estimates. [Certified profile densities](cubic-allocation-results.json).
