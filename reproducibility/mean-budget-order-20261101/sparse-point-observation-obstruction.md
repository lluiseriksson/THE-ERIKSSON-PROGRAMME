# Sparse spectral pivots do not supply a coercive local observation

Unit110, 3 November 2026. A failed construction attempt, with an exact
class-wide falsifier for point-supported observations. Group with the
inter-block notes, not a new small paper. No Lean or executable arithmetic.

## 1. The attempted reduction and its missing estimate

The critical inverse-moment spectral result bounds the dimension of a low
spectral subspace. One tempting conversion is to choose a comparable number
of vertex evaluations that separate that subspace, then use a point-pinning
estimate as a certificate for a rectangular observation construction.
Linear independence of sampled low modes does not prove that certificate:
unobserved high-mode corrections can cancel all sampled values at low cost.
The uniform family below disproves the point-pinning estimate for EVERY
choice of a bounded number of sampled vertices, already with critical
moment exactly1. This does not disprove using the additional averages of
complementary rectangles in a partition.

## 2. Scalar all-vector lower bound for arbitrary observation functions

Let V=n^D, n>=2, and use the actual forward-edge scalar energy

    E_m(f)=m sum_(x,i)|f(x+e_i)-f(x)|^2,  m>=1.

Let S be ANY set of s<V sampled vertices. Allow an arbitrary observation
C(f) that depends only on f|S, with C(0)=0, and ANY penalty Phi with
Phi(0)=0. No linearity, differentiability, output dimension or bound on
Phi is needed for the following necessary condition. If, near zero,

    c||f||^2 <= E_m(f)+Phi(C(f)),                          (1)

then

    s >= c V/(2D m+c).                                   (2)

Proof: take f=1 off S and f=0 on S. Then ||f||^2=V-s. Each forward-edge
occurrence on which f changes has one endpoint in S, so there are at most
2D s such occurrences. This includes the parallel forward occurrences at
n=2. Hence E_m(f)<=2D m s. For any sufficiently small nonzero t,
C(tf)=C(0)=0 exactly, so the observation and its penalty vanish. Dividing
(1) by t^2 gives c(V-s)<=2D m s, which is(2).

Now fix D>=3,c>0 and take m=n^2. The actual constant coefficient a=m
satisfies 1<=a<=2m, mean a=m and mean((m/a)^(D/2))=1. The target order
max(1,(n/sqrt(1+m))^D) is1, whereas(2) tends to infinity like n^(D-2).
Thus bounded point support cannot give the required ALL-COCHAIN kernel
certificate, irrespective of finite penalty rescaling or nonlinear output.
This is a support lower bound, not a lower bound for the dimension of an
arbitrary globally supported observation.

## 3. An actual divergence-zero version in D>=4

Let S again be arbitrary, now sampled vertices at which all physical
components may be read. Fix a cochain component j, and let T be the
projection of S onto the other D-1 coordinates. Write t=|T|<=s. Set that
component equal to one fixed unit internal real vector on every j-line
whose transverse coordinate is outside T, and zero on the remaining
j-lines. All other components vanish. Call the resulting cochain U.

Because U_j is independent of x_j, its actual flat divergence is zero.
It vanishes at every sampled vertex. If t<n^(D-1), then

    ||U||^2 = n*(n^(D-1)-t),
    E_m(U) <= 2(D-1)*m*n*t.                              (3)

The energy bound counts at most2(D-1)t transverse forward-edge boundary
occurrences of T, repeated on n j-levels. Derivative direction j contributes
zero. Actual uniform total stiffness is precisely the componentwise
forward-gradient energy, so no surrogate physical form is substituted.
The same small-t scaling argument as above, for any observation depending
only on U|S, forces

    s >= t >= c*n^(D-1)/(2(D-1)m+c).                      (4)

If t=n^(D-1), the right side is smaller than t and(4) still follows
directly, although that particular U is zero. Thus(4) holds for EVERY S.

At m=n^2 this grows like n^(D-3), hence diverges for D>=4. In particular
the actual four-dimensional divergence-zero class already defeats every
bounded-support point-observation proposal in this uniform critical regime.
For D=3 this physical bound is only constant: the stronger n^(D-2) result
in Section2 is all-cochain, and is NOT claimed on the full physical space.
Nc>=2 supplies the needed internal unit vector; no Nc growth is used.

## 4. A rectangular mean succeeds on the SAME coefficients

The failure is specific to point support. Let C_0 be normalized global
mean in each cochain/internal component, the partition with one rectangular
block. Ordinary discrete characters diagonalize the uniform forward energy:
the eigenvalue at frequency k is

    4m sum_i sin^2(pi*k_i/n).

Every nonzero frequency has eigenvalue at least4m sin^2(pi/n). Concavity
of sin on[0,pi/2] gives sin(pi/n)>=2/n for n>=2. Thus at m=n^2,

    E_m(U)>=16||U-lift(mean U)||^2.

For any fixed0<c<=16, the ACTUAL data

    C=C_0, Phi(y)=c||y||^2

give(1) for all cochains, hence for divergence-zero fields. The output
dimension is h=D*(Nc^2-1), independent of n, in the claimed target order.
This checks the normalized-map requirement as well as the fixed penalty.
The scalar version has one output. It is not an all-partition falsifier:
one allowed partition explicitly succeeds.

Nor does Section2 disprove taking sampled singleton blocks PLUS the
averages on complementary rectangular blocks. Our indicator witness does
not generally have zero complementary means. What fails is a proposed
proof via the singleton/point observation alone. A valid partition proof
must establish the stability provided by its genuinely averaged outputs.

## 5. Prior context, verification and route audit

The indicator/edge-boundary test is elementary Dirichlet-energy reasoning,
not a novelty claim. Primary context checked: P.G.Doyle and J.L.Snell,
Random Walks and Electric Networks, author record
https://arxiv.org/abs/math/0001057 (2000 author version). Its abstract and
metadata identify the classical random-walk/network framework. No full
book theorem is invoked or claimed verified here; all inequalities above
are proved explicitly. No exhaustive priority search or independent review.

Analytic audit: scaling near zero with EXACTLY zero observations; edge
occurrences rather than simple-graph degrees at n2; s=0 and full-support
limits; transverse projection t<=s; exceptional t=n^(D-1); actual component
divergence; norm and energy multiplicity n; scalar cap/mean/moment1; D3
versus D4 threshold; fixed c and the comparator range c<=16; normalized
mean norm and nonzero-frequency sine estimate. No local test or numerical
campaign was run. Same preparing Codex agent, backend/effort unexposed.
No new numerical grade or inherited score. Earlier exact notes/reports
remain unchanged. No Lean certificate, human review or physical mass gap.

Conservative audit of the current mechanism:108 shorted fixed-penalty
criterion,109 finite-K/slack criterion,110 attempted spectral-pivot-to-local
conversion. None proves the GENERAL critical rectangular count/coercivity
or defeats every such partition. Keep THREE units without global endpoint
advance. Stop the abstract Schur/sparse-pivot construction route. The
concrete blocker is now quantified: spectral rank and injective point
sampling do not provide a stable spatial observation, even for uniform
critical coefficients; one needs a coefficient-adapted AVERAGE stability
construction with the target rectangular count.

ONE active mathematical question remains unchanged. A further attempt must
bring that constructive spatial ingredient (and retain the original/fixed
penalty distinction), not another block-matrix reformulation or a reset
of this counter. Preservation, formal verification and consolidation of
closed results may continue independently. No new paper/PDF/AIRR action;
PR29 remains20/41,TermSource=0; interacting/continuum gap remains open.
