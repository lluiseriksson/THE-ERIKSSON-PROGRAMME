# A critical single-sphere obstruction at quotient noise one quarter

Research note following programme commit 59794083537c96743b7b8582b9c8734ccbea42a1. It is outside the frozen PDF and has no assessment score.

Let P be ordinary noise of correlation rho = 1/4 on r signs and mu uniform. Let S be a single lattice magnetization d (mean of the r signs), 0 <= d <= d0 for a sufficiently small absolute d0. Assume that a positive potential H is constant on S, at most one off S and equal to one on the window 0 <= m(y) <= 1/sqrt(r) off S. Let pi = H PH / Z, with Z = E(H PH). If ||pi||_p <= B at p = 15/7, then for every x on S the probability that its Doob transition remains on S is at most

    C(B) r^(-2/15) exp(-c r d^4).

Constants are uniform over all sufficiently large r and admissible d. Sign reflection gives the corresponding result on the negative side with reflected window. In particular, tuning the radius toward zero, the height of a single spike or the thickness of the central bulk, while retaining the stated window, cannot produce a sticky single sphere at critical order. The result does not assert a uniform spectral gap for all these kernels.

## The rates and prefactors

Use I(d) = [(1+d)log(1+d)+(1-d)log(1-d)]/2. Write I2(u,v) for the joint Cramér rate of the means of r independent stationary rho-noise pairs. Put J = I2(d,d)-I(d) and E = I2(d,0)-I(d). For a fixed input with mean d these are precisely the conditional output rates at d and 0. Indeed, under a tilt by lambda X + theta Y the conditional sign factors for Y given X have tilt theta; choosing lambda to make the input mean d subtracts exactly the binary marginal cost I(d). Equivalently, conditioning on the two input counts gives the weighted sum of their two conditional log moment-generating functions. Its Legendre transform agrees with I2(d,v)-I(d). The tilting parameters for both target outputs are uniformly small in this neighborhood by positive definiteness of the noise-pair covariance at zero.

Write q=P(x,S), independent of x in S. Stirling's inequalities give mu(S) >= c r^(-1/2) exp(-rI(d)). Under the conditional tilt to output mean d the probability of a single output sum is O(r^(-1/2)). To see uniformity, one of the two independent groups of signs has order r, with tilted binomial success parameter in a compact subset of (0,1). Its maximum atom is O(r^(-1/2)), and convolution cannot increase this maximum. Undoing the tilt on the exact slice yields q <= C r^(-1/2) exp(-rJ).

For the lower bound from S to the bulk, tilt the conditional product to mean output zero. The tilt parameter theta is nonpositive because the original output mean is rho d. On the interval of sums [0,sqrt(r)] the change of measure from the tilted product to the original has density exp(-rE-theta sum) >= exp(-rE). Under the tilt each of the two groups has order r. For each group require its sum to exceed its own tilted mean by an amount between sqrt(r)/16 and sqrt(r)/8. Each such event has probability bounded below uniformly: it contains order sqrt(r) admissible counts, each with tilted binomial probability at least c/sqrt(r) by Stirling on a compact parameter interval. By independence their intersection has a fixed positive probability and puts the total sum in [0,sqrt(r)]. Removing S costs at most O(r^(-1/2)) under the tilt by the same maximum-atom bound. Thus P(x,window outside S) >= c exp(-rE).

## Quartic defect at the critical exponent

Put Delta(d)=J-2E-I(d)/p=I2(d,d)+(1-1/p)I(d)-2I2(d,0). If v=(1+rho)/2 and c0=1-rho^2, the two Taylor expansions are

    I2(d,d) = d^2/(2v) + (3v-1)d^4/(24v^3) + O(d^6),
    I2(d,0) = d^2/(2c0) + (3c0-2)d^4/(12c0^3) + O(d^6).

For the diagonal, symmetry of the strictly convex log moment-generating function gives equal optimizers. The variable (X+Y)/2 has second moment v and fourth cumulant v-3v^2. For (d,0), condition instead on a balanced Y margin, of rate zero. The conditional log moment-generating function per sign is (1/2) log(1+c0 sinh^2(t)), with fourth cumulant 4c0-6c0^2. Both transforms are even and analytic near zero. For variance V and fourth cumulant kappa, the fourth-order coefficient in the even Legendre transform is -kappa/(24 V^4). This gives both displays. Since I(d)=d^2/2+d^4/12+O(d^6), at v=5/8, c0=15/16 and p=15/7 the quadratic coefficient vanishes. The quartic coefficient is

    56/375 + 2/45 - 3328/20250 = 298/10125 > 0.

Hence Delta(d) >= c d^4 throughout the chosen neighborhood, including d=0.

## The stationary bound forces small retention

The stationary mass of S is at most B mu(S)^(1-1/p) = o(1) uniformly, since the maximum uniform binomial atom is O(r^(-1/2)). The part of Z with both endpoints outside S is at most one. The remaining part is at most 2 Z times the stationary mass of S, by symmetry of the edge law. Consequently Z <= 1+o(1). Write H_S for the constant on S. On that sphere pi >= H_S^2 q/Z, so H_S sqrt(q) <= C(B) mu(S)^(-1/(2p)). The transformed row has numerator H_S q for retention and its denominator PH(x) is at least the central-window transfer already bounded below. Substitution gives

    K_H(x,S) <= C(B) r^(-(1-1/p)/4) exp(-r Delta(d)/2).

The polynomial exponent is exactly 2/15. The same conclusion up to a fixed factor survives multiplication of H by exp(f) with uniformly bounded ||f||_infinity, since row probabilities and normalized stationary densities change by bounded factors. It therefore covers the vanishing exact-matching tilts of the subcritical manuscript whenever the corrected stationary critical moment is bounded. Multiple shells, a potential depressed on much of the central window, and other geometries remain genuine possibilities at the unresolved endpoint.
