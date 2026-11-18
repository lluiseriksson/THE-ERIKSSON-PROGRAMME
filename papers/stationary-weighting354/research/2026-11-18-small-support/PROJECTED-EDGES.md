# Projected stationary edges and cuts decided by few coordinate queries

The preceding two notes use the size and separation of a cut. A subcube obtained by fixing a few coordinates contains exponentially many nearby vertices. Here exact stationary marginal matching controls such cuts by comparing the **joint law of the two ends of a stationary step** with ordinary product noise. All statements concern one actual stationary step.

Let μ be uniform on the L-cube, let P=Pρ be product noise at 0<ρ<1, let h>0 and normalize Eμ hPh=1. Set π=hPh and ν=πμ. Assume ν has uniform marginals on every set of at most k coordinates and ‖π‖_p≤B for some p>1+ρ. Set η²=ρ max(1,1/(p−1)), e=Bη^(k+1). No pointwise floor on π enters this result. Under the original critical cap take p=(1+ρ)/(1−ρ) and B=2^(1/p).

**Projected edge theorem.** Write J(x,y)=μ(x)P(x,y)h(x)h(y) for the oriented stationary edge probability, and J₀(x,y)=μ(x)P(x,y). For a coordinate set I of size m let J_I and J₀,I be the joint marginals of both ends. Uniformly over every pair of patterns i,j on I,

    |J_I(i,j)/J₀,I(i,j) − 1| ≤ Δ_m = e² + 2 u_m + u_m²,
    u_m = (1+1/ρ)^(m/2) e.

In particular Δ_m decays exponentially in k if m≤c k and c<log(1/η²)/log(1+1/ρ), with p,B,ρ,c fixed.

**Proof.** Write Q=P_{√ρ}, a=E h and v=1−a²=‖Qh−a‖₂². The stationary rigidity lemma in the [published window paper](https://airr.science/papers/ARR-2026-4T35VQ6MZB8F99F4/versions/v2/) gives v≤a²e². For clarity, g=Ph=Q(Qh) satisfies ‖Π_{>k}g‖_{p'}≤η^(k+1)√v by the Walsh multipliers and forward hypercontractivity (if p'≤2, norm monotonicity suffices). Matching gives EπΠ_{≤k}g=a. Thus Eπg≤a+e√v and 1=(E hg)²≤a Eπg. Rearranging yields the claim, also when v=0.

Let Q_out act only on the complement of I and put F_i=(Q_out h)(i,·) as a vector in the complement's uniform L² space. The product formula and self-adjointness give the **exact** ratio J_I(i,j)/J₀,I(i,j)=〈F_i,F_j〉. In particular, retaining only one-time marginals would miss the off-diagonal quantities required for an exit probability.

To bound every section, expand Qh−a in the Walsh basis on I with vector coefficients b_S on the complement. Parseval gives Σ_S ‖b_S‖²=v. Inverting Q on I alone gives F_i−a=Σ_S ρ^(−|S|/2) χ_S(i)b_S (including the potentially nonzero coefficient b_empty). Vector Cauchy–Schwarz gives ‖F_i−a‖≤(1+1/ρ)^(m/2)√v≤u_m. Expanding the inner product about the constant vector a and using 0<a≤1 proves the displayed relative bound. The denominator J₀,I is positive even for opposite patterns.

**Adaptive cuts.** Let D be decided by a deterministic tree reading at most d coordinates on each path. Different paths may inspect different coordinates. For d≤k, ν(D)=μ(D) exactly, since its accepting leaves are disjoint cylinders. For each ordered pair of leaves, each at one endpoint, the event is a disjoint union of pair-atoms on their combined set of at most 2d coordinates. Summing the two-sided comparison for those atoms compares its J and J₀ probabilities with relative error at most Δ_min(2d,L). Summing over accepting pairs gives the same comparison for D×D. This argument has no factor equal to the number of leaves.

With α=ν(D)>0, forward hypercontractivity gives J₀(D,D)=‖Q1_D‖₂²≤μ(D)^(2/(1+ρ)). Thus

    Pr_ν[X₁∈D | X₀∈D] ≤ (1+Δ_min(2d,L)) α^((1−ρ)/(1+ρ)).

For an arbitrary cut A with mass t>0 assume there is such a tree with ν(A△D)≤εt. Since each J endpoint has law ν, J(A,A)≤J(D,D)+2εt and α≤(1+ε)t. Its conditional retention is at most

    2ε + (1+Δ_min(2d,L))(1+ε)^(2/(1+ρ)) t^((1−ρ)/(1+ρ)).

The latter proof also covers D empty. Consequently, in a family with t→0, k→∞ and exponentially small Δ_min(2d,L), retention bounded below by δ>0 forces liminf ε≥δ/2 for any sequence of these approximations (restrict to a bounded-ε subsequence if necessary). This is a relative-error restriction on classifiers for rare traps.

**Checks.** At ρ=1/2, p=3 and d=⌊k/4⌋, both-leaf u is at most B·2^(−1/2)(3/4)^(k/4). A subcube fixing d bits has mass 2^(−d) and conditional retention tending to zero even though its other L−d bits are free. In fact the exact reference retention here is (3/4)^d, because each fixed bit independently stays unchanged. The relative atom comparison with m=d places actual retention between (1±Δ_d)(3/4)^d. For h constant the Gram ratio equals one exactly. If k=0 or Δ_m≥1 the lower estimate need not give positive information. Across several time steps the coordinate projection need not be Markov.

**Relation to the open problem.** This proof removes the floor and relaxes the cap for the projected-edge conclusion only. It establishes neither a full gap nor uniform escape from each starting vertex. A ball defined by all L coordinates need not have a shallow decision tree with small relative error. The remaining test is whether the original factorized edge law controls the conductance of such clustered, poorly approximable cuts. The [Bonami inequality](https://aif.centre-mersenne.org/articles/10.5802/aif.357/) supplies the ordinary noise estimate. The Gram argument supplies the comparison for the tilted stationary edge. The comparison with these sources establishes the provenance of the ingredients and leaves global priority open. This analytic research note has received only same-context algebraic checks.

**Limitation for Hamming balls.** A nonempty accepting leaf has mass at least 2^(−d) under matching. If t<2^(−d−1), every nonempty depth-d tree event has ν(A△D)≥ν(D)−t>t, while the empty event has error exactly t. In particular take h=1 and the ball of radius ⌊L/8⌋. Its mass is at most [3^(1/8)(4/3)/2]^L by summing binomial coefficients with weight 3^(−j). The base is below one since 3·2⁸<3⁸. When k is of order √L and d≤k this gives t<2^(−d−1) eventually. It disproves the proposed universal relative-approximation step even with exact matching in all degrees. It supplies an obstruction to the proof method; no slow mixing is asserted for this ball.
