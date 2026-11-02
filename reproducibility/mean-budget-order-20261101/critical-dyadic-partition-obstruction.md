# Critical block observations: dyadic trees can require a logarithmic overhead

Unit103, 2026-11-02. Base b65803f7ec0fd8bfea61d051b4d8b2caf26ac3b1. A useful obstruction inside the existing mean-budget dossier, not a separate paper. All new geometry/partition adapters below are analytic, not Lean-verified or independently reviewed.

## Precise separation

Fix D>=3,Nc>=2,c>0 and h=D*(Nc^2-1). There is a FIXED finite M_0 and a scalar actual coefficient family on tori of increasing dyadic side n, satisfying

    m>=1, 1<=a(x)<=2m, mean(a)=m,
    mean((m/a)^(D/2))<=M_0,
    max(1,(n/sqrt(1+m))^D)=1,                            (1)

with the following separation for actual normalized block means.

* Every coercive full dyadic cube-tree partition, even allowing an arbitrary translated torus origin, needs at least 1+(2^D-1)*(log2(n)-q+1) leaves, with fixed q independent of n.
* The SAME coefficient profile admits an explicit axis-aligned rectangular partition with exactly L^D+D leaves, L=2^q fixed, and the required coercive observation inequality for every actual cochain.

Here a full dyadic cube tree starts from the side-n torus coordinate cube, splits every selected cube into all 2^D equal children, and retains all unsplit siblings as leaves. It need not satisfy neighbouring-level balance. This definition permits arbitrary refinement decisions and arbitrary root translation, not just the greedy inverse-mass test of unit101. It does NOT include arbitrary anisotropic rectangle splits, compressed trees with non-cube leaves, non-partition covers, or compressed linear combinations of mean outputs.

For a partition P use the actual ordinary Euclidean observation

    C_P(U)_(B,j)=sqrt(|B|)*mean_B U_j,
    dim F=h*#P.                                         (2)

The lower bound already follows if coercivity is required only on actual divergence-zero fields. In fact, the bad witness has C_P(U)=0, so ANY penalty with Phi(0)=0 fails when Q_w(U)<c||U||^2. The positive rectangular construction supplies C_P, Phi(y)=c||y||^2,K=c globally, hence also the original nonlinear data in any neighbourhood of zero.

## 1. One fixed weak region meets the critical moment

Choose an integer ell>3D/c, and a dyadic integer L=2^q>=4ell+2. Let gamma=max(1,c/4), take n=2^J with J>=q+1, and set

    m=gamma*n^2,
    S={0,...,L-1}^D, s=L^D/n^D,
    a=1 on S, a=A=(m-s)/(1-s) off S.                    (3)

Every direction and field component uses this same actual total coefficient at the actual forward-gradient start; repairs w=a-1 are nonnegative. Since s<=2^(-D)<=1/2 and m>=1,

    A>=m, A/m<=(1-s)^(-1)<=2,
    s+(1-s)A=m.

With p=D/2, the critical inverse moment obeys

    mean((m/a)^p)=s*m^p+(1-s)*(m/A)^p
      <=L^D*gamma^p+1=:M_0.                             (4)

All D,c,Nc,ell,L,gamma,M_0 are fixed while J increases. Since gamma>=1, the target maximum in(1) is exactly1. A higher exponent p'>D/2 would make the weak contribution L^D*gamma^(p')*n^(2p'-D) grow; thus this example does not contradict the higher-moment dyadic upper bound of unit101.

## 2. Actual compact curls invisible inside one leaf

For completeness the needed actual field is the compact curl already derived in unit100, global-reciprocal-mean-trap-refutation.md. Let t(r)=max(1-|r|/ell,0), put psi(x)=product_i t(x_i-y_i), extended by zero outside its local box, and take a fixed nonzero actual adjoint H. Define

    U_1=(partial^-_2 psi)H,
    U_2=-(partial^-_1 psi)H, U_j=0 for j>=3.

The backward differences commute, so the actual backward divergence is zero. Each component has total sum zero by telescoping. Both the field support and all START SITES of nonzero actual forward gradients lie in y+[-ell,ell]^D, of side2ell+1. The directed-difference identities are

    T=sum t^2=(2ell^2+1)/(3ell),
    V=sum (partial^-t)^2=2/ell,
    W=sum (partial^+partial^-t)^2=6/ell^2,
    ||U||^2=2VT^(D-1)||H||^2>0,
    E_0(U)=2[WT^(D-1)+(D-1)V^2T^(D-2)]||H||^2.

Consequently its exact Rayleigh quotient is

    lambda_ell=W/V+(D-1)V/T
      =3/ell+6(D-1)/(2ell^2+1)<=3D/ell<c.                (5)

These identities follow from the finite triangular window sums; the original note checks the actual backward constraint and gradient-start convention. The old n-multiple-of-(2ell+2) assumption was used for packing MANY separated windows. It is unnecessary here: a SINGLE window inside a cube of side2ell+1, with n>=2L>2ell+1, has the same integer finite-difference values after zero extension. We do not impose an incompatible packing divisibility condition on n=2^J.

If that gradient-start box lies in S, its total weighted energy is Q_w(U)=E_0(U), by a=1 there and the existing actual flat Hodge identity (formal source dfd49d0b0730a4d36f58a4cbb7a17d6a41fb60bc). If its entire field support lies in a single partition leaf, that leaf's component means are zero, because they contain the full zero-sum field; all other leaves see zero. Thus C_P(U)=0 and(5) contradicts c||U||^2<=Q_w(U)+Phi(C_P(U)) for any Phi(0)=0. This is an actual curl obstruction, not a certificate supplied as a new assumption.

## 3. Lower bound for every translated full dyadic cube tree

Write j_*=J-q. Consider the COMPLETE hypothetical dyadic level j_* of the chosen translated root. Its cells have side L. In each coordinate, the cyclic interval {0,...,L-1} meets at most two length-L grid intervals. One intersection is an ordinary integer interval of length at least L/2>=2ell+1. Selecting the largest intersection independently in each coordinate gives a subrectangle of S, contained in ONE level-j_* cube, and large enough to contain a gradient-start box of side2ell+1. Cyclic wrap causes no extra intersection inside S: n>=2L, and each coordinate interval is split at most once by this grid.

Suppose a proposed tree partition had maximum leaf depth at most j_*. Then its leaves are coarser than the hypothetical complete level j_*, so that selected box lies entirely in one actual leaf. Place the actual curl of section2 inside it. Its gradients start in S, its means vanish on all leaves, and(5) contradicts coercivity. The test field may depend on the proposed partition, as is allowed when disproving an inequality asserted for EVERY field.

Hence every coercive such partition has maximum depth at least j_*+1. A path to that depth contains at least j_*+1 internal nodes. A full 2^D-ary tree with I internal nodes has exactly 1+(2^D-1)I leaves: count edges both as nodes minus one and as 2^D I. Therefore

    #P >=1+(2^D-1)*(J-q+1).                              (6)

In particular no uniform constant depending only on D,c,Nc,M_0 can bound these uncompressed dyadic mean codomains at the target order1 as n grows. This lower bound concerns ALL such trees, including a translated grid chosen after seeing a, not merely a defect of one inverse-mass stopping rule. It does not refute arbitrary rectangular means or global spectral observations.

## 4. A constant-size actual rectangular partition succeeds

Partition S into its L^D singleton vertices. Decompose its complement into the D disjoint rectangles

    R_i={x: x_k in[0,L-1] for k<i,
             x_i in[L,n-1],
             x_k in[0,n-1] for k>i}, 1<=i<=D.            (7)

Every point outside S has a unique first coordinate outside[0,L-1], proving both coverage and disjointness. Every internal positive-axis edge of R_i starts at a vertex with coefficient A. The rectangles may have aspect ratios tending to infinity, which is precisely outside the preceding cube-tree restriction.

For an integer interval of length l and constant coefficient A, the counting variance identity and the unique-path Cauchy-Schwarz estimate give

    sum ||u-mean u||^2
      =(1/l)sum_(a<b)||u_b-u_a||^2
      <=l(l-1)/(4A)*sum_internal_edges A||du||^2.        (8)

Indeed use path resistance at most(l-1)/A; for edge cut t the number of crossing pairs is t(l-t)<=l^2/4. This proof also holds for vector values, and l=1 has zero residual. Tensorize the counting product variance over coordinate fibres BEFORE summing the original energies. With every side length<=n, each rectangle has

    residual_(R_i)^2 <=n^2/(4A)*E_(a,R_i)(U).

There is no extra factor D: each fibre estimate multiplies its own directional energy and all coefficients are bounded by the SAME n^2/(4A). Singleton residuals in S vanish. Internal edges of different rectangles are disjoint; omitted boundary/wrap edges have nonnegative energy. Thus

    c*sum_B residual_B^2 <=c*n^2/(4A)*Q_w(U)
      <=c/(4gamma)*Q_w(U)<=Q_w(U).

With(2), exact orthogonal counting decomposition yields

    c||U||^2<=Q_w(U)+c||C_P(U)||^2,
    #P=L^D+D, dim F=h*(L^D+D),                          (9)

uniformly in n. This is a directly supplied original observation for the SAME profiles used in(6), not merely the spectral-existence theorem invoked as a substitute.

## Consequence for the active route and novelty boundary

The critical block-mean question remains OPEN for arbitrary actual scalar profiles. This unit eliminates the route of repairing the critical endpoint solely by changing the stopping criterion within a full dyadic cube tree: a logarithmic overhead is genuinely necessary for that entire class, even under root translations. A proof for unrestricted rectangles must use additional geometry, such as large-aspect-ratio cuts around concentrated weak regions. Equations(7)-(9) show that such an escape can work, without claiming a general covering theorem.

Recursive cube refinement and its depth cost are classical. Primary bibliographic check: Hanan Samet's own publication list, https://www.cs.umd.edu/~hjs/hjsyear.html , entry297, records The quadtree and related hierarchical data structures, ACM Computing Surveys16(2),187-260(1984), also TR-1329. The author-PDF URL returned404 and publisher DOI10.1145/356924.356930 returned403 in this unit; no full-text novelty comparison is claimed. The present analytical proof uses no uninspected theorem from that survey. Independent priority and standalone publication significance are unestablished; this is grouped with the existing critical threshold, compact curls and resistance/tensorization results. No source prose or figures reproduced.

ONE active question is preserved: does the critical inverse moment imply the target rank for normalized means on unrestricted axis-aligned integer rectangular partitions? Hypotheses remain actual scalar1<=a<=2m,exactmeanm,fixedD>=3,c>0,Nc>=2,M. The mechanism must now leave full cube trees, using anisotropic cuts or another proved rectangle construction. Falsifier must defeat EVERY such rectangular partition, not merely every dyadic tree. Abandon/change after three substantive units without a proved reduction or useful falsifier, preserving the concrete obstruction. This unit supplies a proved class-wide mechanism obstruction and an actual escape example; no general-endpoint closure is claimed.

## Model assessments and review context

FIRST exact-note self-assessment5/10 by the same preparing Codex agent. Actual served backend identity and effort are unexposed. Rubric0-10: analytic derivation7, originality2, route relevance7, verification maturity3; overall5 is a qualitative judgement, not a probability or arithmetic average. No independent review, human peer review, PDF assessment or editorial acceptance. No inherited score, rerating or search for a better grade.

Audit of this exact source: fixed M_0 at critical scaling, exact arithmetic mean and upper coefficient bound; actual backward divergence, total component means and forward-gradient START support; single-window dyadic-n compatibility; translated-grid intersection lengths and independent coordinate choices; hypothetical full level refining any shallower partition; field-dependent-on-partition quantifiers; full-arity leaf identity; complement rectangles' first-outside coverage; scalar/vector path coefficient and tensorization without extra D; omitted-edge positivity; gamma>=c/4; singleton outputs and real dimension; distinction between cube trees, arbitrary rectangles and global spectral observations.

O1. New translated-grid/partition/curl adapters remain analytic, not Lean-verified; no numerical diagnostic or terminal reproduction is claimed.

O2. The theorem forbids full equal-child DYADIC CUBE trees, not all bounded-aspect boxes, anisotropic dyadic rectangle trees, arbitrary rectangles, covers or compressed observations.

O3. The unrestricted rectangular positive result is only for the explicit one-weak-cube family. It does not prove the general active endpoint.

O4. Classical refinement/path/tensorization mechanisms and earlier compact curls limit novelty. The primary full-text quadtree comparison was unavailable; independence and priority remain unestablished.

O5. Constants L^D,M_0 may be large and depend on fixed c,D. They remain independent of n, as needed; no optimal count or cost is asserted.

O6. Self-assessment is no independent mathematical validation. New Lean/oracle/Colab execution and exact-PDF review are absent; previous exact-version grades remain unchanged.

O7. Critical distribution assumptions are not removed, and no physical interacting/continuum gap, new small paper, AIRR deposit/acceptance/publication or PR29 progress is claimed. PR29 remains20/41, TermSource=0.
