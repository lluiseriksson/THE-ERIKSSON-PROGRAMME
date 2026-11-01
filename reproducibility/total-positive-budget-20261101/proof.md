# Volume-rank obstruction with a positive total-stiffness budget

Analytic grouped extension, 1 November2026. Base main7e9c9f6bbb9d1b21cbf54a8083229090ca201fe5. Existing SignedPositiveMeanFamily.lean already proves a positive-part sufficient theorem on a one-direction strip. This note does NOT rediscover that mechanism or claim a new formal endpoint. Its extension is the full coexact volume packet and the sharper total coefficient max(1+w,0).

## Theorem and explicit changed hypothesis

Use the actual flat unit-spacing counting cochains, D>=2,Nc>=2, packet span S and original local nonlinear observation/upper-quadratic penalty/coercivity hypotheses of restricted-support-positivity-20261101/proof.md. Retain c>0, differentiability of C:E->F at0, C(0)=0 and finite-dimensional real F. For EVERY direction i and occupied component l in{0,1}, assume

 V^-1 sum_x max(1+w(i,x,l),0)<=m, with m>=0 and V=n^D.

All original weights are arbitrary finite real numbers, with NO pointwise lower bound, and all unoccupied weights are unrestricted. Then for R>=1,2R<n, H=2R(2R+1)^(D-1), B=4*pi^2*D*R^2/n^2,

 dim_R F >= H*(1-m*B/c).                             (T)

For a family with fixed m,c,D,Nc, let alpha=min(1/4,sqrt(c/(8*pi^2*D*max(1,m)))). For n>=2/alpha, (T) implies dim_R F>=alpha^D*n^D/2 by R=floor(alpha*n). Fixed m is a sufficient volume-density condition, not a necessary one.

This theorem eliminates occupied lower bound-1 by a proved monotone envelope. It DOES NOT claim the unchanged signed-mean upper bound alone suffices. The new explicit budget controls the mean of a pointwise positive total coefficient, which can exceed its signed mean. That changed assumption must travel with every use.

## Actual envelope construction and proof

The actual all-cochain Hodge identity componentwiseFlatGradient_eq_hodge and componentwiseWeightedRepair_energy give

 Q_w(A)=sum_(i,x,l) (1+w(i,x,l))*||G_i A_l(x)||^2.      (1)

Define the actual ambient quadratic form

 P(A)=sum_(i,x,l in{0,1}) max(1+w(i,x,l),0)*||G_i A_l(x)||^2.

Its real self-adjoint operator is concretely G* diag(a) G where a equals max(1+w,0) on occupied components and0 elsewhere. No order or positivity certificate is a hypothesis. Each coefficient is nonnegative, so P(A)>=0 on ALL E. For A in the whole actual packet span S, unoccupied components and their componentwise gradients vanish. Formula(1), a<=max(a,0), and nonnegative gradient squares prove Q_w(A)<=P(A). This comparison is asserted only on S: unoccupied positive original weights can prevent it on all E. Invariance of S is unnecessary.

For each actual normalized packet quadrature b_k,q, its exact spatial density is V^-1*|p_k,l|^2*|chi_k(e_i)-1|^2. Multiplying the positive-total mean bound by these nonnegative coefficients and using sum_(l=0,1)|p_k,l|^2=1 gives

 P(b_k,q)<=m*sum_i |chi_k(e_i)-1|^2=m*lambda(k)<=m*B.

The actual H-dimensional orthonormal packet basis therefore gives tr(P_S T_P inclusion_S)<=H*m*B, by trace in an orthonormal basis, where T_P is the constructed operator of P. This is a genuine compression of P, not a claim that the trace of indefinite Q_w has a nonnegative complement.

For v in U=S intersect ker DC(0), the original local coercivity and upper-quadratic penalty imply c||v||^2<=Q_w(v) by the unchanged t->0 argument. The proved comparison gives c||v||^2<=P(v). Extend an orthonormal basis of U within S. Each complementary P diagonal is nonnegative because P is a proved sum of nonnegative squares. Rank-nullity and trace invariance imply

 c*(H-dim F)<=c*dim U<=tr(P_S T_P inclusion_S)<=H*m*B,

which proves(T), including dim F>H. The proof never requires positivity of original Q_w. With the chosen alpha, R>=alpha*n/2>=1,2R<n and m*B<=c/2 because m/max(1,m)<=1. Hence dim F>=H/2>=alpha^D*n^D/2. The definition max(1,m) avoids division by zero; m=0 also gives the stronger finite statement dim F>=H directly.

## Relation to the earlier hypotheses and strict witnesses

If occupied w>=-1 and mean(w)<=M with M>=0, then max(1+w,0)=1+w, so m=1+M recovers the previous theorem with exactly its finite bound. No stronger hypothesis is added on that old domain. For general signed weights,

 max(1+w,0)<=1+max(w,0),

so bounded occupied positive-part repair means also imply this volume theorem with m=1+Mplus. Direct total-positive budgeting can be strictly cheaper than that coarse bound. Existing signed strip endpoints control a different selected packet/dimension; they are not relabelled as volume-density endpoints.

For n>=3 take ALL original weights w=-n^(2D). Then occupied total-positive means are0, while no uniform occupied lower bound exists as n grows. Formula(1) gives Q_w=(1-n^(2D))*<A,K0 A>, negative on every nonconstant Hodge eigenmode. Nevertheless the retained local hypotheses are compatible: <A,K0 A><=4D||A||^2 by shift isometry, and F=E,C=id,Phi(y)=(c+4D*(n^(2D)-1))*||y||^2 make coercivity hold globally. Thus this is a full-hypothesis strict extension beyond w>=-1, not only a separated weight condition. Its output is large, so it does not prove rank sharpness. Arbitrary negative values are allowed because P controls the easier quadratic form; no claim is made that negative directions themselves become positive.

Positive-part means are not necessary: the already verified square-cycle-cancellation-20261031 construction has critical positive-part budget but actual repair<=0. That retained negative result is not refuted by this sufficient criterion. Signed means alone remain insufficient for the older strip result, as localized-signed-mean-20261031 shows; this note supplies no new signed-mean-only volume theorem.

## Verification, primary sources and model context

Symbolically checked against the actual Hodge and weighted-gradient identities, normalized packet Gram/density source and restricted-support rank proof at the pinned base. No new Lean theorem, numerical experiment, paired Colab reproduction, external evaluation or PDF is claimed. The original SignedPositiveMeanFamily.lean and its paired077/077b evidence establish prior in-repository monotone-envelope results; the square-cycle construction and paired081/081b evidence retain the insufficiency of treating this budget as necessary.

Primary library source checked1November2026: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Trace.html , LinearMap.trace_eq_sum_inner. It supports the genuine trace step, not originality. Positive-part domination and finite trace/rank comparison are classical. Exact combined priority unestablished; this is a grouped refinement, not a separate discovery paper. No physical/interacting/continuum mass-gap claim; PR29 stays20/41;TermSource=0.

Same preparing Codex agent, continuing author context; backend model and effort unexposed. First exact-source assessment is hash-bound separately, no inherited score, blind/independent/external-model/human review or target grade. Public v4 and its assessment remain unchanged.
