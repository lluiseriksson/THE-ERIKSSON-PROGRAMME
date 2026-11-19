# Minimum support size of a persistent cut for Boolean Doob noise

Research note for the stationary-gap question, 18 November 2026. The proof applies to the full chain and to the trace studied in candidate R. The estimate is effective for a specified range of noise correlations.

Let the uniform probability measure on the Boolean cube of dimension L be μ. Write P=Pρ for product noise with fixed 0<ρ<1, g=Ph, π=hg, ν=πμ, and K(x,y)=P(x,y)h(y)/g(x). Assume h>0, Eπ=1, π≥b>0, and Eπ^s≤2 where s=(1+ρ)/(1−ρ). Write s'=s/(s−1), p=(1+ρ)/2 and

    β = p (1+ρ³) 2^(1/s),     M = 2^(1/s)/b².

For every nonempty vertex set A of cardinality m, the killed transition operator on A in the stationary inner product satisfies

    ‖K_AA‖ ≤ min(1, M β^L m^(1/s')).

In particular, if β<1 and m=exp(o(L)), the norm tends to zero exponentially. The same holds whenever limsup L⁻¹ log m < −s' log β. The statement requires no marginal matching. A bound on cardinality is stronger as a premise than small stationary mass.

**Proof.** The floor gives h≥b/g. Positivity and Jensen yield g≥b P(1/g)≥b/(Pg). To control Pg pointwise, let Q=P_{√ρ}. Self-adjointness and the semigroup law give ‖Qh‖₂²=E hPh=1 and Pg=P_{ρ^(3/2)} Qh. In the uniform *probability* normalization the row density for noise with correlation t is the product over coordinates of (1+t x_i y_i). Its squared L² norm in y equals (1+t²)^L. Thus 1/g²≤b⁻²(1+ρ³)^L everywhere.

Conjugation by √π sends K to S=diag(√(h/g)) P diag(√(h/g)), which is positive semidefinite because the Walsh eigenvalues of P are nonnegative. It commutes with restriction in the sense that the same conjugation identifies the killed operators. Its diagonal entry is p^L π(x)/g(x)². The norm of its compression is at most the matrix trace, and Hölder in *counting* measure gives Σ_A π ≤ m^(1/s') (2·2^L)^(1/s). Multiplying proves the stated inequality. The Markov contraction supplies the upper bound one.

**Trace chain.** Fix 0<a≤b/4 with b≤1, let B={h<a}, C=Bᶜ, θ=a²/b. For A⊂C the same bound holds for the trace-chain killed norm with M replaced by M/(1−θ). Indeed S_BB≤θ I since h/g=h²/π≤θ on B. Write D=S_BC. Positivity of S and Cauchy–Schwarz in its quadratic form give |〈u,Dv〉|²≤〈u,S_BB u〉〈v,S_CC v〉. Taking the supremum over unit u gives D*D≤θ S_CC. The successive-visit operator is conjugate to T=S_CC+D*(I−S_BB)⁻¹D by the convergent sum over excursions in B. Consequently S_CC≤T≤S_CC/(1−θ) in quadratic-form order. Compress to A and apply the full-chain bound. If B is empty the full-chain proof applies directly. This multiplicative comparison retains exponential decay even where an additive O(θ) error would dominate it.

**Cut interpretation and exact parameter check.** For either chain the fraction retained after one step from stationarity conditioned on A is the Rayleigh quotient of its indicator for the killed kernel. If this fraction is ≥δ>0, then m≥(δ/M_eff)^s' β^(−s'L), with M_eff the appropriate prefactor above. At ρ=1/4, s=5/3 and β=(325/512)2^(3/5)<1 because 325/512<16/25 and 8·16⁵<25⁵. By continuity this applies on an open interval. At ρ=1/2 the fifth-root comparison is inapplicable and β=(27/32)2^(1/3)>1 (2·27³>32³). The estimate becomes vacuous there. For h=1 the diagonal reduces to p^L, providing a direct normalization check. For A equal to the full cube one must retain the norm-one bound. No worst-start escape estimate follows from the conditional-stationary statement.

**Scope and sources.** This excludes subexponential-support bottlenecks in the effective range, including after the small-potential excursions in R. It leaves exponentially large sets of vanishing mass and the general gap open. The full-chain proof uses the explicit noise row, Jensen, Hölder and positivity. The trace argument uses the classical successive-visit chain. See [O'Donnell on Boolean noise](https://arxiv.org/abs/2105.10386) and [Aldous and Fill, section 2.7](https://www.stat.berkeley.edu/~aldous/RWG/Book_Ralph/Ch2.S7.html). The original programme inputs are the inverse-floor identity in the [published v2](https://airr.science/papers/ARR-2026-4T35VQ6MZB8F99F4/versions/v2/) and the trace formula in candidate R. The literature comparison establishes the classical ingredients only. This is an analytic derivation with a same-context algebraic check. Global priority and formal verification remain unestablished.

The next test on the existing question is whether exact marginal matching constrains the stationary mass of exponentially numerous vertices with large π/g² strongly enough to control internal flow. A bound that merely substitutes the desired killed norm as a hypothesis would leave this test unresolved.
