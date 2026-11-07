# Rectangular means for a coefficient gap, and the failure of singleton isolation beyond that gap

Hash context: source/base fa9919536bad2003eb04163f4e4c393d99b9a531; checked remote main88f31a1981b757b9240a9076e2012545066b9028. Unit179,7November2026. Analytical research note for grouped consolidation, not a separate paper, AIRR deposit, numeric assessment or formal certificate.

## Actual problem and scope

Let D>=3, p=D/2, X={0,...,n-1}^D with periodic forward edges, N=n^D, h=D(Nc^2-1). The actual energy throughout THIS note is the componentwise weighted-gradient energy of the original critical inverse-moment question:

    E_a(U)=sum_(x,i,j) a(x)|U_j(x+e_i)-U_j(x)|^2.

We do not substitute the variable-coefficient weighted curl energy, whose cross terms do not generally cancel. The proof works for every cochain, hence on the actual divergence-free and coexact subspaces without using a divergence correction.

For an axis-aligned integer rectangular partition P put

    C_P(U)_(R,j)=sqrt(|R|)*mean_R(U_j).

We construct original coercivity data with K=c:

    c||U||^2 <= E_a(U)+c||C_P(U)||^2.                 (1)

The construction is linear and global quadratic, so it supplies the required near-zero differentiable map and finite locally upper-quadratic penalty as well.

## 1. Arbitrary exceptional vertices: the geometric construction

**Lemma.** Suppose a(x)>0, and a(x)>=A>0 off an arbitrary set S of k vertices. Set

    L=min(n,max(1,floor(sqrt(A/c)))).

There is an actual rectangular partition satisfying (1), with

    #P <= ceil(n/L)^D+2Dk.                          (2)

No shape, separation, connectedness, or box representation of S is assumed. In particular no product of all coordinate cut sets and no full equal-child cube tree is used.

**Construction.** Partition each coordinate interval into ceil(n/L) consecutive intervals of length at most L; take their Cartesian products. This gives q0=ceil(n/L)^D starting rectangles.

Process each distinct s in S. If its current leaf is already a singleton, do nothing. Otherwise, in coordinate1 cut that leaf immediately before and after s_1 when those cuts are internal. Retain the at most two side slabs and continue only inside the central slice of width1. Repeat for coordinates2,...,D. There are at most2D actual binary cuts, each increasing the number of nonempty rectangles by one. The final central rectangle is {s}. Already isolated vertices remain singleton leaves. Induction proves disjointness, complete coverage, integer rectangle shape, at mostq0+2Dk leaves, and every nonsingleton leaf avoids S. Every side length remains at most L.

This is a derived local geometry operation. It is not an assumed partition or a common refinement with q0*k or k^D cost.

## 2. Complete energy proof, including thin rectangles and edge orientation

For a length-l interval and a scalar or vector-valued u, counting variance satisfies

    sum|u-mean u|^2 = (1/l)sum_(s<t)|u_t-u_s|^2
       <= ((l-1)/l)sum_edges [number of pairs crossing edge]*|du|^2
       <= l(l-1)/4 * sum_edges|du|^2
       <= l^2/4 * sum_edges|du|^2.                (3)

The first inequality uses path Cauchy-Schwarz and t-s<=l-1; an edge after r vertices is crossed by r(l-r)<=l^2/4 pairs. For l=1 the residual is exactly zero. Thus no aspect-ratio or continuum assumption enters.

For a product rectangle, tensorization gives variance at most the sum of the counting conditional variances on original coordinate fibres. One proof writes P_i for averaging in coordinate i: the commuting orthogonal projections give

    I-product_i P_i <= sum_i(I-P_i)

as quadratic forms (diagonalize their simultaneous 0/1 eigenvalues). Applying (3) on each fibre yields

    sum_R|U-mean_R U|^2 <= L^2/4 * sum_internal_edges|dU|^2.    (4)

If L=1 every leaf is a singleton, so (1) is immediate. If L>=2 then L^2<=A/c, including the case L=n. A nonsingleton leaf avoids S; every positively oriented edge retained in (4) starts at a vertex with a>=A. Hence its residual is at most E_internal/(4c). Internal edge sets of distinct leaves are disjoint, and all omitted cross-leaf and periodic wrap edges have nonnegative energy. Singletons have zero residual, even if their coefficients are small. Summing gives

    c sum_R||U-mean_R U||_R^2 <= E_a(U)/4.

Finally the exact orthogonal decomposition

    ||U||^2=sum_R||U-mean_R U||_R^2+||C_P(U)||^2

proves (1), in fact with E_a/4 in place of E_a. No kernel angle, strict Schur margin, or extension outside the actual field space is supplied as a hypothesis.

A convenient uniform bound from (2) is

    q0 <= 4^D max(1,c^p) max(1,N/A^p).             (5)

For A/c<4, L=1 and N <=(4c)^p*N/A^p. Otherwise, if L<n then L>=sqrt(A/c)/2, so q0<=(1+2n sqrt(c/A))^D <=3^D max(1,c^p)max(1,N/A^p). If L=n, q0=1. These alternatives include n=1 and small A.

## 3. Positive critical-moment theorem with a fixed coefficient gap

**Theorem.** Fix B>=1 and 0<theta<=1 independent of n and mu. Suppose the original profile obeys

    mu>=1, 1<=a<=2mu, mean(a)=mu,
    (1/N)sum(mu/a)^p<=M,

and the ADDITIONAL coefficient-gap condition

    for each x: a(x)<=B or a(x)>=theta*mu.        (6)

Then an actual rectangular mean map satisfies (1) and

    dim F <= h*2^p [4^D max(1,c^p)theta^(-p)+2D*M*B^p]
                    * max(1,N/(1+mu)^p).         (7)

**Proof.** Let S={a<=B}. The moment assumption derives, rather than assumes,

    k <= M*B^p*N/mu^p.

Off S, (6) gives a>=theta*mu. Apply the lemma with A=theta*mu and (5). Since theta<=1 and mu>=1,

    max(1,N/(theta*mu)^p)<=theta^(-p)max(1,N/mu^p),
    max(1,N/mu^p)<=2^p max(1,N/(1+mu)^p).

Insert the k bound in (2) and multiply the number of leaves by h. This proves (7). The target rank order is exactly that in the active question. The arithmetic mean and upper coefficient bound are retained for that question's subclass; they are not needed by the geometric lemma.

**Fixed-floor two-phase corollary.** For arbitrary geometry S, all original profiles taking values {1,H} satisfy this theorem with B=1,theta=1. Indeed the actual arithmetic mean gives H>=mu, also when S is empty; if H=1 all sites can be put in S and mu=1. More generally the weak value can be any value bounded by a fixed B. This removes the earlier contiguous weak cube, fixed-box geometry and separation requirements from this positive subclass.

It does NOT cover every two-valued family with an n-dependent unbounded lower value. An early progress sentence in this unit saying 'all two-valued profiles' was too broad and was corrected before this note. Condition (6) remains extra; no hypothesis has been removed from the unrestricted original theorem.

## 4. Useful scoped falsifier: optimal threshold singleton isolation can cost a power

Fix c=1, D>=3, integer t>=2. Set

    n=t^2, N=t^(2D), mu=t^4, b=t^2,
    S={0,...,t-1}^D, k=t^D, s=k/N=t^(-D),
    a=b on S, a=H=(mu-s*b)/(1-s) off S.

These are actual nearest-neighbour profiles with exactly two values. Direct algebra gives H>=mu, H<=mu/(1-s)<2mu, mean(a)=mu and a>=1. Their normalized critical inverse moment is

    s*(mu/b)^p+(1-s)*(mu/H)^p <=1+(1-s)<2.       (8)

Thus D,c=1,M=2 are fixed, and max(1,(n/sqrt(1+mu))^D)=1.

Consider precisely this strategy, for ANY threshold T and ANY valid constant lower bound A on its remaining vertices: isolate EVERY vertex in S_T={a<=T} as a singleton, and begin with the uniform product mesh of side max(1,floor(sqrt(A))) capped at n. If T<b, no vertex is exceptional and A<=b, so every mesh interval has length at most t. There are at least(n/t)^D=t^D base cells. If T>=b, at leastk=t^D distinct singleton leaves are mandatory. This includes T>=H. Consequently EVERY threshold choice in this strategy costs at least t^D; T<b,A=b attains t^D. The threshold-optimized strategy has exact minimum t^D versus constant target rank order.

But the ACTUAL rectangular problem on this SAME family has a D+1-cell solution. Use S itself as one rectangle, together with

    R_i=[0,t-1]^(i-1) x [t,n-1] x [0,n-1]^(D-i), i=1,...,D.

Each outside point belongs to its first coordinate outside [0,t-1], proving disjoint coverage. On S, (4) bounds variance by t^2/(4b) times its internal energy, at most1/4. On R_i, the largest side is at most n and coefficients are H>=n^2, so variance is at most n^2/(4H) times energy, again at most1/4. Therefore (1) holds globally with c=K=1 and q=D+1.

The lower bound refutes only the named uniform-mesh-plus-threshold-singleton strategy. It refutes neither all rectangular partitions nor the active question. It proves that an extension beyond the fixed coefficient gap must use the physical size of intermediate-coefficient regions, rather than automatically resolving all their vertices. This negative result is preserved, not discarded in favour of the positive corollary.

## 5. Originality, relevance, assessments and verification limits

The one-dimensional Poincare estimate, variance tensorization, and orthogonal mean decomposition are elementary classical tools. The current dossier already uses them for one cubical weak region. The present adapter derives the O(k) guillotine isolation count for arbitrary S and proves the corresponding fixed-gap subclass and the limitation family above. Original priority is not established; this is a consolidation contribution, not grounds for a separate small-corollary paper.

Primary literature checked on7November2026:
- Pechstein and Scheichl, Weighted Poincare inequalities, IMA J Numer Anal33(2),652-686(2013), DOI10.1093/imanum/drs017; author-institution record https://researchportal.bath.ac.uk/en/publications/weighted-poincar%C3%A9-inequalities/ and publisher abstract https://academic.oup.com/imajna/article-abstract/33/2/652/653341. Their abstract explicitly concerns high contrast and geometry/topology of coefficient regions. This is context, not an imported theorem proving (7).
- Perez and Rela, Degenerate Poincare-Sobolev inequalities, arXiv:1805.10388v2, https://arxiv.org/abs/1805.10388. Its weighted-cube/self-improvement setting is relevant background; the abstract alone does not establish equivalence to this discrete rank theorem.
- The initially retrieved old Bath PDF address redirected to the university home page; a Caltech subsampled-Poincare PDF returned502. Neither was read as a full paper or used as proof. No unavailable lookup is treated as a priority conclusion.

Verification: complete analytical self-audit above, exact symbolic families and boundary checks. No Lean/Lake build, oracle, rational certifier, model review or new CPU/GPU session ran in this unit. The previous unit178 outputs are NOT evidence that this new partition construction has executed. No exact-PDF numeric stars are assigned; existing public AIRR v7 and its3.0/10 grade remain unchanged and are not inherited. Authorship assistance is the same Codex research context, not an independent reviewer.

The unrestricted coefficient problem remains the sole active question. PR29 remains20/41 and TermSource=0. No interacting or continuum Yang-Mills spectral gap follows.

Next: implement and reproduce the new rectangular isolation and intermediate-island examples with complete partition coverage, energy identities and real rejecting mutations in own Colab. Then investigate actual scale-adapted intermediate regions, without assuming their rectangular geometry, within the same active question. The stopped common-refinement, trace and cube-tree routes remain stopped; neither this note nor a later replay resets their counters.