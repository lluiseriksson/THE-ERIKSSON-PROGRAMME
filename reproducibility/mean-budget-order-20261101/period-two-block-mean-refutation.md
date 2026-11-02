# Exact microscopic arithmetic means do not control coercivity

Research unit096, 2026-11-02. Same mean-budget question and existing paper dossier. Analytic derivation only; no new Lean, numerical run, PDF, deposit or independent review. Mathematical base: main7bee3af77b35d7197509bf067eb021493258fae4. Frozen appendix PR145 is untouched.

## Statement and scope

Even strictly positive, period-two total conductances with exactly the same arithmetic mean m in every translated microscopic block need not have a Poincare constant improving as n^2/m. In the actual finite flat componentwise gradient model this also prevents a uniformly bounded observation rank at m>=n^2. The rank lower bound proved here grows linearly with n, not with the D-dimensional volume. There is no interacting-background or continuum mass-gap conclusion.

## Scalar proof, with counting norms

Let n=2N, N>=3, m>=1. On the directed cyclic edges x to x+1 of Z/n set

 a_(2r)=A=2m-1, a_(2r+1)=B=1, w_x=a_x-1>=0.

Every adjacent pair, including pairs crossing a period/cycle boundary, satisfies (a_x+a_(x+1))/2=m. The global mean is m. The heavy edges occupy exactly half the sites; their support does not shrink with n.

For g:Z/N->R define the injective linear lift Tg by

 (Tg)(2r)=(Tg)(2r+1)=g(r).

Direct substitution gives all three exact identities:

 ||Tg||_n^2=2||g||_N^2,
 sum_x(Tg)(x)=2 sum_r g(r),
 E_a(Tg):=sum_x a_x |(Tg)(x+1)-(Tg)(x)|^2
          =sum_r |g(r+1)-g(r)|^2.

Indeed every A-edge difference is zero and each B-edge is the corresponding coarse difference. This includes the closing edge r=N-1 to0. The restricted energy is independent of m; the repair term alone is identically zero on the entire lifted space.

Choose an integer R>=1 with 2R<N. On the real span of cos(2pi kr/N), sin(2pi kr/N), 1<=k<=R, the mean vanishes and the real dimension is exactly2R. Orthogonality on Z/N follows by summing a geometric progression; 2R<N excludes zero, duplicate conjugates and the Nyquist mode. Each cyclic difference has multiplier exp(2pi ik/N)-1, of squared modulus4sin^2(pi k/N). Consequently every f in the lifted band obeys

 E_a(f)<=2sin^2(pi R/N)||f||_n^2
        <=8pi^2 R^2/n^2 ||f||_n^2.                  (1)

Monotonicity of sin on [0,pi/2] applies since R<N/2. In particular the mean-zero spectral gap lambda_a satisfies

 4sin^2(pi/n)<=lambda_a<=2sin^2(pi/N)<=8pi^2/n^2.

The lower bound uses a_x>=1 and the ordinary directed-cycle Fourier diagonalization. If C_a is the optimal mean-zero Poincare constant, this implies

 1/[2sin^2(pi/N)]<=C_a<=1/[4sin^2(pi/n)].          (2)

Thus C_a>=n^2/(8pi^2) for every m>=1. A bound C_a<=K n^2/m with one finite K independent of n,m contradicts (2) as soon as m>8pi^2 K. No asymptotic or computation is required for this contradiction.

## Separate algebraic consistency check: the two-site Bloch block

Write u_r=f(2r), v_r=f(2r+1). At coarse Bloch angle theta=2pi k/N the energy matrix in the counting inner product is

 [[A+B, -A-B exp(-i theta)],
  [-A-B exp(i theta), A+B]].

Its characteristic polynomial is (A+B-lambda)^2-(A^2+B^2+2AB cos theta); hence

 lambda_+(theta),lambda_-(theta)
 =2m +/- sqrt(4m^2-4(2m-1)sin^2(theta/2)).

Rationalizing the lower branch gives

 lambda_-(theta)=4AB sin^2(theta/2)
   /[A+B+sqrt((A+B)^2-4AB sin^2(theta/2))].

At small theta its leading term is AB theta^2/[2(A+B)]. Physical wave number is theta/2, so the effective coefficient is the harmonic mean

 a_eff=2AB/(A+B)=2-1/m<2,

although the arithmetic mean m is unbounded. At fixed theta, m->infinity gives lambda_-(theta)->2sin^2(theta/2), consistent with the lifted trial upper bound. At m=1 the matrix is the folded unweighted-cycle matrix; at theta=0 the lower branch is zero. These are analytic normalization checks, not independent numerical verification.

## Actual finite flat field adapter and observation-rank consequence

Take D>=2, Nc>=2, and a nonzero actual adjoint coordinate H. Coordinates are numbered1,...,D. For every derivative direction i and field component j choose total coefficient

 a_(i,x,j)=a_(x_1), w_(i,x,j)=a_(x_1)-1.

Every translated axis-aligned cube of side2 has exactly half even and half odd x_1; its arithmetic mean is exactly m for each i,j. The global directional mean is also m. For every even side length the same statement holds. This hypothesis is local arithmetic averaging, not a lower bound on each individual edge or a statement about all possible paths/resistance averages.

Use fields U_2(x)=f(x_1)H and U_j(x)=0 for j!=2. The actual backward-divergence term in direction2 vanishes because U_2 is independent of x_2. Thus these are actual flat divergence-zero fields. The existing componentwise finite flat Hodge identity, formally established at dfd49d0b0730a4d36f58a4cbb7a17d6a41fb60bc, identifies the total quadratic form with the sum of actual weighted squared forward differences. In this family both energy and squared norm acquire exactly the same factor n^(D-1)||H||^2. Equation(1) therefore holds on an actual real subspace W of dimension2R with beta=8pi^2 R^2/n^2. This NEW period-two adapter is proved here on paper, not Lean-compiled.

For completeness derive the nonlinear-observation step rather than posit a rank certificate. Suppose C:E->F is differentiable at0, C(0)=0, dimF=q<infinity, and near0 Phi(y)<=K||y||^2 for finite K>=0. Suppose the original local coercivity inequality

 c||U||^2<=Q_w(U)+Phi(C(U))

holds on sufficiently small actual divergence-zero fields, with c>0. If q<2R, rank-nullity on W gives a nonzero U in W with DC(0)U=0. Along tU, differentiability gives C(tU)=o(|t|), so its image lies in the penalty neighbourhood for sufficiently small t. Divide coercivity by t^2 and let t->0. Homogeneity of Q_w yields c||U||^2<=Q_w(U)<=beta||U||^2. This contradicts beta<c. Therefore

 q>=2R whenever 2R<N and 8pi^2 R^2/n^2<c.          (3)

Choose an integer k>=5 with 8pi^2/k^2<c. For all even n>=k set R=floor(n/k)>=1. Then 2R<N since4R<=4n/k<n, and beta<=8pi^2/k^2<c. Thus

 q>=2 floor(n/k)                                 (4)

uniformly for all m>=1. In particular choosing m=n^2 rules out a profile-uniform bounded-rank upper guarantee of the proposed order max(1,(n/sqrt(1+m))^D), even under the exact microscopic cube-mean condition. Local radii, K and C may vary with n; only c stays fixed. This does not establish volume-order rank and does not refute the infimum over profiles: the constant profile a=m retains the earlier upper witness.

## Primary-source comparison and falsification protocol

Marek Biskup, Recent progress on the Random Conductance Model, Probability Surveys8(2011),294-373, DOI10.1214/11-PS190. Author-hosted source inspected directly: https://www.math.ucla.edu/~biskup/PDFs/papers/CSnotes-final.pdf . Exercise3.12, equations(3.43)-(3.44), printedp334/PDFpage41, explicitly construct the one-dimensional harmonic coordinate using inverse conductances; section4.1, equations(4.1)-(4.2), printedp335/PDFpage42, check it and display the inverse-moment dependence. Its random-walk covariance normalization is not silently identified with this counting-norm graph Laplacian. The finite period-two identities and Bloch normalization above are derived directly. The harmonic-mean/resistance mechanism is classical; no priority or new-homogenization claim. This is a useful falsifier for this dossier's proposed stronger sufficient hypothesis, grouped with the existing repair-budget analysis, not a separate paper.

One active research question remains: which proved distribution condition, weaker than a uniform relative pointwise lower bound, suffices for the fixed-profile mean-budget rank upper order? Candidate mechanism to assess next: effective path resistance/Poincare control inside observation blocks, derived from actual coefficients rather than packaged as an assumed certificate. Falsifier: an explicit positive profile satisfying that proposed coefficient condition but violating the derived block Poincare inequality. Abandonment criterion: reject any condition contradicted by the period-two profile above; after three substantive units without proving a coefficient-to-Poincare implication or a new useful counterexample, audit the route and switch or identify the exact blocker. This is a next-step protocol, not a theorem that such a weaker condition has been found.

## Model assessments and review context

FIRST exact-note source assessment:6/10, same preparing Codex agent, served backend identity and reasoning setting not exposed. No independence, peer review, acceptance, PDF score, or inherited assessment. Rubric0-10: internal derivation7, original contribution3, dossier relevance7, reproducibility maturity4; overall6 is a qualitative judgement, not a calibrated probability or arithmetic average. Checks: exact pair norm/mean/closing edge; real frequency dimension; theta0 and m1; large-m rationalized branch; n>=6 and strict2R<N; k>=5 and strict beta<c; nonlinear derivative/penalty-neighbourhood limit; distinction q~n versus n^D; infimum-versus-universal quantifier.

O1. No new Lean kernel verification: scalar periodic construction and actual field adapter remain analytic.
O2. Harmonic-mean and Bloch mechanisms are classical; source comparison does not establish an original theorem worthy of a separate publication.
O3. The higher-dimensional rank bound is only linear in n; no volume-order conclusion may be claimed here.
O4. Local arithmetic averaging does not imply effective resistance control; the sufficient weaker condition remains open within this bounded research task.
O5. Normalization is for directed cyclic differences, counting norms and this finite flat componentwise model; other operator conventions require a new adapter.
O6. Source-only self-assessment is neither independent model review nor human peer review; no new PDF has been rendered or reviewed.
O7. No physical interacting Yang-Mills gap or continuum result, and no new AIRR submission. PR29 remains20/41 and TermSource=0.