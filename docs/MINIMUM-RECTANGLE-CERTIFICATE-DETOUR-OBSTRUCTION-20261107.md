# Actual local detours defeat minimum-coefficient rectangular certificates

Hash context: base e0c68daafda7752c1844d5841a86f9051b8792de; checked programme main88f31a1981b757b9240a9076e2012545066b9028. Analytical unit181,7November2026. Grouped research note, no new AIRR deposit, numeric assessment, formal certificate or priority claim.

## Result and precise scope

For the actual componentwise start-weighted nearest-neighbour energy, an explicitly derived three-edge detour proves

    E_a >= (H/4) E_0                                             (1)

when the coefficient is at least H off a periodically separated weak set. The weak coefficients may be arbitrarily small nonnegative numbers. All paths and congestion are constructed below; neither a flow nor an energy comparison is assumed.

This yields actual admissible profiles at c=1 and mu=n^2 such that one rectangular global mean gives the original all-cochain coercivity inequality, whereas EVERY partition accepted by the coefficient-minimum/unweighted-Neumann-gap certificate needs an unbounded number of rectangles. The obstruction persists for any fixed multiplicative improvement of that certificate, and for every fixed critical moment bound M>1. This defeats a specified sufficient certificate, not all rectangular partitions: the same family explicitly has a one-cell solution.

The unrestricted original critical rectangular problem remains the sole active question. The mechanism of Dirichlet-form comparison by short paths is classical. This note contributes an explicit periodic directed-start adapter and its coefficient/moment/certificate separation, with originality unestablished.

## 1. Actual conventions

Let D>=2,n>=3,X=(Z/nZ)^D. For an actual real vector-valued cochain U (all h=D(Nc^2-1) scalar coordinates), use counting norm and

    E_0(U)=sum_(x,i,j)|U_j(x+e_i)-U_j(x)|^2,
    E_a(U)=sum_(x,i,j)a(x)|U_j(x+e_i)-U_j(x)|^2.

The positive direction edge (x,i) has coefficient at its START x, including cyclic wrap edges. We do not replace this by a variable-coefficient weighted-curl form. Work componentwise; every inequality extends by an orthogonal sum to all h coordinates, hence to the actual divergence-free and coexact subspaces without a correction operator.

Let W subset X have periodic l-infinity separation at least3: every pair of distinct weak vertices differs by cyclic distance at least3 in some coordinate. Assume a(x)>=H>0 off W and a(x)>=0 on W. Write

    E_strong=sum_(x notin W,i,j)|D_i U_j(x)|^2,
    E_weak=sum_(x in W,i,j)|D_i U_j(x)|^2,
    E_0=E_strong+E_weak.

## 2. Construct every detour and derive congestion ONE

Index directions cyclically, and let sigma(i)=i+1 modulo D, a fixed-point-free permutation. For each weak-start edge x -> x+e_i take the path

    x -> x-e_sigma(i) -> x+e_i-e_sigma(i) -> x+e_i.              (2)

It has exactly three edges and telescopes to the actual edge difference, also across the torus seam. In positive-edge notation its three used edges are:

    type1: (x-e_sigma(i), sigma(i)), traversed backward;
    type2: (x-e_sigma(i), i), traversed forward;
    type3: (x+e_i-e_sigma(i), sigma(i)), traversed forward.

Each positive start is at periodic l-infinity distance1 from x, distinct from x because n>=3 and sigma(i)!=i. Separation therefore makes every used positive start strong. In particular the first edge traversed away from the weak site is NOT assigned the weak start coefficient: its positive orientation is reversed, and its start is x-e_sigma(i).

Fix any positive edge (y,k), strong or otherwise. For each of the three types its possible weak-start path source is uniquely determined:

    type1: i=sigma^(-1)(k), x=y+e_k;
    type2: i=k,             x=y+e_sigma(k);
    type3: i=sigma^(-1)(k), x=y-e_sigma^(-1)(k)+e_k.             (3)

These three candidate sources are distinct for D>=2,n>=3, and every pair has periodic l-infinity distance at most2. At most ONE can lie in W. Each type has a unique i, so no two uses of (y,k) survive. Thus every strong positive edge is used by at most one detour, counting uses rather than merely distinct paths. This proves congestion<=1 directly, independent of D and |W|.

For each weak edge, Cauchy-Schwarz on (2) gives |D_i U_j(x)|^2<=3 times the sum of its three strong edge squares. Summing and using (3) proves

    E_weak <= 3 E_strong,
    E_0 <= 4 E_strong,
    E_a >= H E_strong >= (H/4)E_0.                            (4)

No weak coefficient enters the lower bound. Empty W is included. The constant4 is a proved safe value, not claimed optimal. The previous pending candidate used a much looser1+3D congestion estimate; the explicit edge-preimage calculation above replaces it, not an empirical fit.

## 3. Derive actual one-rectangle original data

The counting-unitary Fourier basis on the torus diagonalizes E_0, with eigenvalues

    4 sum_i sin^2(pi*k_i/n).

The zero mode is exactly the global constant. Every nonzero mode has eigenvalue at least4sin^2(pi/n)>=16/n^2, since sin z>=2z/pi on [0,pi/2]. Parseval therefore gives

    E_a(U) >= (4H/n^2)||U-mean_X U||^2.                       (5)

Consequently, if4H/n^2>=c, the single actual rectangle X, with

    C(U)=sqrt(n^D)*mean_X(U),   Phi(y)=c||y||^2,

satisfies

    c||U||^2 <= E_a(U)+c||C(U)||^2                            (6)

globally on all cochains. Its actual finite output dimension is h, K=c, C(0)=0, and any positive configuration-space neighbourhood works. This proves original data rather than only positivity on a supplied kernel. There is no unproved strict margin or Schur complement assumption. The local meaning in the original problem is near zero in field space; this spatial observation is exactly the allowed one-cell normalized mean.

## 4. What the minimum-coefficient certificate actually asserts

For a nonsingleton integer rectangle R, let L_R^0 be the unweighted INTERNAL-edge Neumann graph Laplacian, and lambda_1(R) its first nonzero eigenvalue in counting norm. A common sufficient local certificate is

    min_R(a)*lambda_1(R) >= c.                               (7)

Singletons have zero residual and are admitted directly. This is the best unweighted Neumann gap multiplied by the minimum coefficient, not merely a loose path or trace estimate. It is sufficient for normalized block means, but its NECESSITY for actual weighted coercivity is not asserted.

Here is a self-contained upper bound using an actual test function, without approximating lambda_1. Let l be the largest side of a nonsingleton R and put u(r)=r-(l-1)/2 along that side, constant in other coordinates. The side energy is l-1 and its counting square norm is l(l^2-1)/12. Hence

    lambda_1(R) <= 12/[l(l+1)] < 12/l^2.                     (8)

This is valid for arbitrarily thin or anisotropic rectangles. For a cyclic interval, use its own consecutive coordinate order and omit the cut edge, as required by the internal Neumann graph. For a full-period side, the cyclic internal edge can instead be included; if such a side occurs, the periodic gap is <=4pi^2/n^2, not the interval value in (8). The lower-bound argument below handles this convention separately rather than silently using (8) on a cycle.

To make the convention explicit, (7) in the theorem below uses the product-of-PATHS Neumann graph obtained by cutting each coordinate interval, INCLUDING a full-period interval, as is usual for the rectangle-local certificate used in the dossier. If one insists on retaining periodic edges on a full-period side, the strengthened conclusion still holds after the adjustment in Section7; no periodic energy is discarded from the actual global proof (4)-(6).

## 5. Admissible family, arbitrary fixed moment excess, and every passing partition

Fix D>=3 and any M>1. Choose an integer m>=4 with 1+m^(-D)<=M. Let t run through sufficiently large multiples of m. Set

    n=t^2, N=t^(2D), mu=t^4=n^2, b=t^2,
    W={0,mt,2mt,...,n-mt}^D,
    k=|W|=(t/m)^D, s=k/N=1/(m^D*t^D),
    a=b on W, a=H=(mu-s*b)/(1-s) off W.                      (9)

The periodic weak separation is exactly mt>=3 (when there is more than one weak vertex). All quantities are actual integers/rationals; H is determined by the original mean, not chosen independently after the bound.

Since b<mu and s<1/2,

    H>=mu, 1<=b<=a<=H<=mu/(1-s)<2mu,
    mean_X(a)=s*b+(1-s)*H=mu.

With p=D/2, the normalized critical inverse moment is

    s*(mu/b)^p+(1-s)*(mu/H)^p
       =1/m^D+(1-s)*(mu/H)^p
       <1+1/m^D<=M.                                        (10)

The original target rank scale is max(1,(n/sqrt(1+mu))^D)=1. Since H>=n^2, (5) proves E_a>=4 times global mean-zero norm, and (6) holds at c=K=1 with ONE rectangle and output dimension h.

Now let ANY unrestricted axis-aligned integer rectangular partition pass (7) at c=1. A weak-containing nonsingleton leaf has min_R(a)=b. From (7)-(8), its largest side satisfies

    l^2<12b=12t^2,   so l<sqrt(12)*t<4t<=mt.                (11)

It cannot contain two distinct weak vertices, since some coordinate separates any such pair by cyclic distance at least mt, while the side has fewer than mt vertices. A singleton also contains at most one. Thus EVERY passing partition has

    #P>=|W|=(t/m)^D -> infinity,                              (12)

although the same actual profiles admit (6) with one rectangle. The proof permits any cut locations and translated origins, not just a prescribed mesh, singleton strategy, binary tree or cube tree. It therefore strictly goes beyond the strategy-specific obstruction in unit179.

This is an asymptotic analytical statement; no finite case fitting is used. The original unrestricted rectangular existence question is not refuted: its positive answer is explicitly realized for this family.

## 6. Fixed multiplicative repairs do not rescue the minimum-gap rule

For any fixed eta>0, replace (7) by eta*min_R(a)*lambda_1(R)>=1. The same proof yields l^2<12eta*b. Choose m>sqrt(12eta) as well as1+m^(-D)<=M. Equations (9)-(12) are unchanged except for this fixed m. Thus no fixed-factor loosening of this particular certificate achieves the target order uniformly over the original critical-moment class. This does not cover tests using actual weighted paths, capacities, connected geometry, boundary coupling or the full weighted spectrum.

## 7. Full-period periodic-edge convention

If a certificate uses cyclic rather than cut-path edges whenever a rectangle spans an entire coordinate circle, replace (8) by a uniform bound

    lambda_1(R) <= 4pi^2/l^2 < 40/l^2

when its longest side is full-period; for a path side (8) is already stronger. A nonconstant Fourier character on a cyclic longest side gives this bound directly, independent of other sides. For eta-fixed certificates choose m>sqrt(40eta), with m>=7 sufficient at eta=1, and 1+m^(-D)<=M. Then every weak-containing leaf still has l<sqrt(40eta)*t<mt and (12) follows. Alternatively, for every fixed m and sufficiently large t, a weak-containing leaf with a full-period side is impossible: eta*b*4pi^2/n^2=4eta*pi^2/t^2<1. The finitely many small t do not affect the lower bound.

Thus even the more favourable periodic-boundary certificate cannot evade the result. The main presentation fixes the cut-path convention to avoid an unannounced boundary change.

## 8. A separate non-necessity example for the global inverse moment

The comparison theorem also gives an elementary alternative-geometry family where the normalized critical moment diverges but one rectangular mean still works. Take n through multiples of3, W={0,3,...,n-3}^D, s=3^(-D), a=1 on W, mu=n^2, H=(mu-s)/(1-s) off W. Then1<=a<=2mu, mean a=mu and H>=mu. The weak separation is3, so (4)-(6) give one-cell original data at c=K=1. Nevertheless

    mean_X((mu/a)^(D/2)) >=3^(-D)*n^D -> infinity.

This shows that the critical inverse moment is not a necessary condition for a GIVEN profile family to have bounded rectangular rank. It does not contradict its established sufficiency or sharpness among universal scalar inverse-moment assumptions, and does not derive a geometric separation hypothesis from the original moment. It is not described as removal of the moment assumption from the original unrestricted theorem.

## 9. Primary attribution, self-audit, failures and review context

Diaconis and Saloff-Coste, Comparison Theorems for Reversible Markov Chains, Annals of Applied Probability3(3),696-730(1993), Section2B/Theorem2.1 and Example2.1, already develop comparison via path length and edge congestion and use three-edge bypasses for missing grid edges. Read from the author-hosted primary PDF https://pi.math.cornell.edu/~lsc/papers/comp-rev.pdf and the Stanford institutional report record https://statistics.stanford.edu/technical-reports/comparison-theorems-reversible-markov-chains on7November2026. We do not claim a new path comparison principle. Our unnormalized start-weighted finite calculation is derived above, so no stationary-measure or Markov normalization is imported silently. Originality of the application (9)-(12) is unestablished; this limited lookup is not an exhaustive novelty certification.

Self-audit covers reversed first-edge orientation, all three exact source preimages, repeated edge uses rather than distinct paths, cyclic wrapping, D2/n3 boundary of the detour lemma, empty W, integer divisibility, exact arithmetic mean, upper profile bound, critical moment, all translated/cyclic rectangles, singleton exception, full-period Neumann-versus-periodic conventions, actual h-component observations and K=1.

Corrections preserved: the pending candidate's crude1+3D comparison was replaced by a derived congestion-one bound4; spacing3t alone would not directly cover the sharper unweighted-gap certificate with the ramp bound, so the presentation uses fixed spacing mt with m>=4 (or m>=7 for a uniform periodic-edge version). The full-period-side convention was detected during self-audit and handled explicitly in Section7. No executed failure, certificate threshold or model grade was changed after seeing results: no execution/model review occurred in this unit.

No Lean/Lake, oracle, rational scientific run or CPU/GPU allocation occurred. Proof is analytical self-audit, not independent model review, peer review or formal verification. The new note has no exact-PDF star assessment and is not published in AIRR. Existing public v7 and its3.0/10 assessment remain bound only to that exact older PDF. PR29=20/41 and TermSource0; no interacting or continuum Yang-Mills spectral gap follows.

Next: freeze an acceptance-safe exact finite replay for the actual detour path/preimage dictionary and coefficient family, with explicit boundary-convention and orientation mutations; execute only in own Colab, normal/-O, with full logs, actual decimal exits and two fresh pinned clones. Then group this with units177/179 and their reproductions into one substantial manuscript revision, with a genuine new exact-PDF model assessment and numeric stars before any publication. Do not reopen the stopped trace, full cube-tree, common-refinement or singleton-universal routes. The remaining substantive mechanism must use actual local weighted energy rather than minima alone.