# Spherical averaging can lower retention of an actual Hamming ball

Fix a Boolean noise parameter 0 < ρ < 1, a floor 0 < b < 1 and a constant C > 0. On the uniform L-cube write P for the noise operator and R for averaging over coordinate permutations about the all-plus vertex. For a positive potential h write w=hPh, Z=Ew, and π=w/Z. Reconstruct a radial potential u from uPu=Rw. This construction preserves the stationary mass of every Hamming shell, and consequently of every radial cut. Multiplying h and u by the common factor 1/√Z gives energy normalization and leaves both chains unchanged.

**Counterexample.** For arbitrarily large dimensions L=4m there exist positive potentials satisfying π≥b, Eπ^s≤2 at s=(1+ρ)/(1−ρ), and uniform marginals through degree floor(C√L), for which the stationary one-step retention of the ball of radius one is strictly **larger** for h than for u. The same holds for radius zero. In particular an upper bound proved only for radial potentials cannot be extended by this one-sided comparison with the reconstructed radial stationary density.

**Construction.** Partition the coordinates into four disjoint sets A,B,D,F of size m. Put

    v = (χ_A−χ_B)(χ_D−χ_F)/4,     h = 1+t v,     z = ρ^(2m).

For 0<t<1, positivity holds. Each of the four Walsh terms of v has degree 2m, so Pv=zv. Its spherical average is zero since those terms have the same degree and their coefficients sum to zero. Direct multiplication gives

    w = 1+(1+z)t v+zt²v²,
    v² = (1−χ_(A∪B)−χ_(D∪F)+χ_[L])/4,    Z=1+zt²/4.

Every nonconstant coefficient of w has degree at least 2m. This gives the exact required matching for all sufficiently large m. At fixed m choose t sufficiently small and positive. Continuity from π=1 gives the required floor and cap. Averaging over permutations preserves the matching, floor and cap of π.

**The radial correction.** Let a=zt², f=Rv². The equation uPu=1+af has a smooth solution near u=1 because its derivative there is I+P, whose Walsh eigenvalues are 1+ρ^j. Uniqueness near 1 gives radiality. In fact the positive solution is globally unique by strict convexity in log coordinates of the exponential scaling objective (Lemma 10.4 of the grouped manuscript). At each fixed m,

    u = 1 + a (I+P)^(-1) f + O_m(a²).

At the all-plus vertex, a symmetrized character of any degree has value 1. At distance one its value at degree j is 1−2j/L, by counting subsets containing the flipped coordinate. Therefore the first-order coefficients of u on the two innermost shells are

    d₀ = [1/2 − 2/(1+z) + 1/(1+z²)]/4
       = −(1−z)³/[8(1+z)(1+z²)] < 0,
    d₁ = [1/2 − 1/(1+z²)]/4 < 0.

The factors 1/2 come from the constant eigenfunction of I+P. These identities hold for every 0<z<1. Thus u<1 throughout the radius-one ball for all sufficiently small positive t in that dimension. Meanwhile v vanishes throughout that ball because both differences of block characters must be nonzero for v to contribute. Consequently h=Ph=w=Rw=1 there.

**Comparison of observables.** The actual conditional retention of a nonempty cut S equals

    [Σ_(x,y in S) μ(x) P(x,y) h(x) h(y)] / [Σ_(x in S) μ(x) w(x)].

The denominator is unchanged for either ball under spherical reconstruction. In the numerator each edge factor equals 1 before reconstruction and is strictly smaller than 1 afterwards. All noise transition probabilities are strictly positive. This proves both strict inequalities without exchanging limits or comparing only quotient kernels.

**Balls of radius proportional to dimension.** The same failure occurs on balls containing exponentially many vertices. Put s=(1+ρ)/(1−ρ) and α=1/(1+32s). Let R_L be the largest odd integer at most αL. For each sufficiently large L=4m, the construction above gives strictly greater actual retention on S={|x|≤R_L} than for the radially reconstructed chain. The limit R_L/L=α is positive.

To see this, let D=(I+P)^(-1)Rv² and let φ_j denote the average Walsh character of degree j. On shell i, φ_L=(-1)^i. For odd i, φ_(L/2)=0 because pairing a subset with its complement cancels its character. Thus

    D_i = [1/2 − 2 φ_(L/2)(i)/(1+z) + (−1)^i/(1+z²)]/4.

For all sufficiently large m, z²≤1/3. Then D_i≤−1/16 on odd shells and D_i≤7/8 on every even shell since |φ_j|≤1. Write q_i=P(x,S) on shell i and W_i=μ(shell i) q_i. For neighboring starts on shells i and i+1, every noise-transition likelihood ratio is at most s since only one input coordinate differs. Summing over S gives q_i≤s q_(i+1). For i<R_L,

    W_i/W_(i+1) ≤ s (i+1)/(L−i) ≤ s R_L/(L−R_L+1) ≤ 1/32.

Pair each even shell below the odd endpoint with the next odd shell. It follows that

    <1_S D, P1_S> = Σ_(i≤R_L) W_i D_i
                    ≤ (7/256−1/16) Σ_(i odd, i≤R_L) W_i < 0.

Here brackets denote the uniform inner product. The actual internal edge mass before energy normalization is exactly

    <1_S,P1_S> + t² <1_S v,P(1_S v)> ≥ <1_S,P1_S>.

The term linear in t vanishes since P1_S is radial and Rv=0. The quadratic term is nonnegative by positive semidefiniteness. In contrast the radial internal edge mass is

    <1_S,P1_S> + 2zt² <1_S D,P1_S> + O_m(t⁴).

At each fixed sufficiently large m, taking t small makes this quantity strictly smaller. Stationary masses of S coincide, proving the assertion. Choosing t smaller if needed also gives 1/2≤π≤2. Since α<1/2, the stationary masses of these balls decay exponentially by the binomial lower-tail bound. Their cardinalities grow exponentially: the shell at R_L contains at least (L/R_L)^R_L points by the product formula for binomial coefficients.

**Scope and remaining test.** The perturbation can depend on m, so the difference can be very small. This refutes exact upper domination on exponentially large, exponentially rare clustered cuts under the full growing matching regime. It establishes neither slow mixing nor the failure of a comparison with slack. The remaining quantitative question is whether the relative conductance loss can stay bounded away from zero for admissible non-radial potentials. The sign computation alone cannot establish this.

The Walsh multipliers are classical. Boyd, Diaconis, Parrilo and Xiao study symmetry reduction for reversible chains. Replacing the stationary density of a non-invariant chain and reconstructing its potential is a different operation. The comparison with these sources identifies established ingredients and leaves global priority open. Verification here consists of exact algebra and finite-dimensional differentiation in the shared research context. No numerical or Lean check was run.

Sources: [O'Donnell, Analysis of Boolean Functions](https://arxiv.org/abs/2105.10386), [Boyd et al., Symmetry Analysis of Reversible Markov Chains](https://web.stanford.edu/~boyd/papers/symmetry.html).
