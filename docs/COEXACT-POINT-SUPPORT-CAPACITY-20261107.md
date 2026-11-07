# Growing point support is necessary even on actual coexact fields in dimension three

Hash context: programme main88f31a1981b757b9240a9076e2012545066b9028;
analytical unit177,7November2026. Research note for grouped consolidation.
No new AIRR deposit, numerical assessment, formal certificate or priority
claim. The exact public v7 PDF and its3.0/10 assessment are unchanged.

## Result and the hypothesis actually removed

The public v7 subsection "Sparse point samples cannot replace stable
averages" constructs divergence-free fields constant along selected lines.
That physical test excludes bounded point sampling for D>=4 at a uniform
coefficient of order n^2, and uses fields with a harmonic component.

Here an explicit local two-form correction gives a stronger conclusion:
for every D>=3, including D=3, bounded point support cannot give target-c
coercivity **even on im(d_1*)**, the actual coexact domain. No separation
assumption on the sampled points is needed. A uniform coefficient already
satisfies the original normalized critical inverse-moment hypothesis with
M=1. The construction is spatially local and uses the actual backward
adjoint, not the nonlocal graph of unit175.

This removes the extra D>=4 restriction from that *particular point-data
existence obstruction over the admissible profile class* and avoids harmonic
witnesses. There is an essential parameter distinction: our family is
mu_n=c n^2/384, not the older mu=n^2 comparison at 0<c<=16. For the latter,
the nonzero Fourier gap is already at least16; on the coexact domain zero
observation then suffices. We do not assert a stronger counterexample at
that unchanged normalization or failure for every uniform profile.
The new construction does not refute the original
rectangular-mean question: a complementary rectangle mean observes values
outside the sampled points and need not vanish on our witness. It does
not prove a new spectral principle or an interacting/continuum mass gap.

## Conventions and a coexact low-energy starting field

Let n>=4 be even, D>=2, X=(Z/nZ)^D, N=n^D. Use the actual counting norm
and unit-spacing differences D_i=T_i-I, D_i*=T_i^(-1)-I. For the actual
curl d_1 on positive unordered pairs,

    (d_1 A)_{ij}=D_i A_j-D_j A_i,
    delta A=-sum_i D_i* A_i,
    E_mu(A)=mu(||d_1 A||^2+||delta A||^2).

For a two-form with only B_12=g nonzero, d_1*B has components

    (d_1*B)_1=-D_2*g,   (d_1*B)_2=D_1*g.

Commuting the backward differences proves delta(d_1*B)=0. All scalar
formulas below occupy one fixed internal unit coordinate e, available
for Nc>=2. No extra internal direction is needed.

On the one-dimensional cycle define the rational triangular profile

    f(t)=1-4 dist_Cn(t,0)/n.

It has mean zero, |f|<=1, and every forward difference has absolute
value4/n. Direct summation gives

    sum_t f(t)^2=n/3+8/(3n).

Define F(0)=0 and F(t)=-sum_{r=1}^t f(r), extended periodically.
The zero sum makes this well-defined, and

    F(t-1)-F(t)=f(t),   |F(t-1)-F(t)|<=1.

Take B^0_12(x)=F(x_1)e and other two-form components zero. Then
U^0=d_1*B^0 has only component2 nonzero, equal to f(x_1)e. In particular
U^0 is coexact, has mean zero and zero actual backward divergence, with

    ||U^0||^2=N(1/3+8/(3n^2)) >= N/3,
    E_mu(U^0)=16 mu N/n^2.                              (1)

No trigonometric approximation or numerical eigenvalue claim enters(1).

## Local correction at an arbitrary sample set

Let S be any set of s sampled vertices. Join two points of S when their
periodic l-infinity distance is at most4. Let S_alpha be the connected
components, s_alpha=|S_alpha|, and choose p_alpha in S_alpha. These
components are derived from S, not an added geometric hypothesis.

Write N_r(S_alpha) for its periodic l-infinity r-neighbourhood and set
chi_alpha=1 on N_1(S_alpha) and0 elsewhere. Define a periodic two-form
G_alpha by its only nonzero component

    (G_alpha)_12(x)=chi_alpha(x)[F(x_1)-F((p_alpha)_1)]e.

Put eta_alpha=d_1*G_alpha, eta=sum_alpha eta_alpha and U=U^0-eta.
Thus U is explicitly coexact. There is no assumed right inverse of
divergence or unproved correction map.

For x in S_alpha, chi_alpha is1 at x,x-e_1,x-e_2. The adjoint formula
therefore gives (eta_alpha)_2(x)=f(x_1)e and
(eta_alpha)_1(x)=0. Other components vanish. Every other eta_beta
vanishes there, because distinct S components have distance greater
than4 and eta_beta is supported in N_2(S_beta). Consequently

    U_i(x)=0 for every x in S and every component i.    (2)

The sets N_2(S_alpha) are pairwise disjoint: a point in two of them
would give two sampled points at distance at most4, contrary to the
component definition. Their total cardinality is at most5^D s.
Outside their union U=U^0. Since |U^0(x)|<=1, this proves

    ||U||^2 >= N/3-C_D s,      C_D=5^D.                (3)

This lower bound deliberately makes no nonzero-witness assertion when
its right side is nonpositive; U is certainly nonzero when it is positive.

## Quantitative correction energy, with clustering retained

A simple path through the sample-component graph has at most s_alpha-1
edges. Each edge changes the first cyclic coordinate by at most4.
Together with the unit bound on increments of the periodic F, this gives
for x in N_1(S_alpha)

    |F(x_1)-F((p_alpha)_1)| <=4(s_alpha-1)+1<=4s_alpha.

No choice of a global coordinate lift, separation assumption or small
diameter compared with n is needed. Periodicity and telescoping along
short cyclic coordinate paths give the stated bound, even across a wrap.

Each of the two possibly nonzero components of eta_alpha consequently
has absolute value at most8s_alpha. Its support has at most5^D s_alpha
vertices. Disjointness of these supports yields

    ||eta||^2 <=128 C_D sum_alpha s_alpha^3.             (4)

The unit flat Hodge identity is

    ||d_1 A||^2+||delta A||^2=sum_{i,j}||D_i A_j||^2.

It follows by expanding the curl and divergence squares and translating
finite sums; their mixed terms cancel since translations commute.
Every difference has norm at most2, so E_mu(A)<=4D mu||A||^2.
Apply this to(4), and use the quadratic inequality E_mu(U^0-eta)<=
2E_mu(U^0)+2E_mu(eta). Equations(1)--(4) give the completely explicit bound

    E_mu(U) <=32 mu N/n^2+A_D mu sum_alpha s_alpha^3,
    A_D=1024 D 5^D.                                    (5)

In particular sum_alpha s_alpha^3<=s^3. The cubic bound is a safe,
nonoptimal arbitrary-clustering estimate, not a sharp capacity formula.
If all sample components have size at most B, the sharper bound
sum_alpha s_alpha^3<=B^2s is available; B is not assumed in the main result.

## Consequence for all finite penalties on point-supported data

Fix c>0 and take, for every sufficiently large even n,

    a(x)=mu_n=c n^2/384.

Then mu_n>=1, 1<=a<=2mu_n, mean(a)=mu_n, and
mean((mu_n/a)^(D/2))=1. These are the actual original scalar moment
hypotheses, without shifting them to a supplied structure.

Suppose C(A) depends only on the full vertex values of A at S, with
C(0)=0. It may have any finite output dimension and need not be linear.
Equation(2) implies C(tU)=0 for every t. A penalty locally bounded
above by K||y||^2, with any finite K, has value at zero at most0.
Local target-c coercivity on the coexact domain therefore necessarily gives

    c(N/3-C_D s) <=32 mu_n N/n^2
                       +A_D mu_n sum_alpha s_alpha^3.  (6)

The same necessity holds if C is differentiable at0 and only its
derivative factors through these point values. Then C(tU)=o(t) and the
quadratic upper bound on the penalty is o(t^2); divide the proposed
inequality by t^2 and let t tend to0. No exact linearization or fixed
penalty K=c is assumed. No separate fine-space repair is covered here.

If s<=N/(12C_D), equations(3) and(6), and
32mu_n N/n^2=cN/12, imply

    sum_alpha s_alpha^3 >= (64/A_D)n^(D-2).              (7)

Thus, without any separation assumption, every successful point-supported
observation satisfies

    s >= min{n^D/(12C_D), (64/A_D)^(1/3)n^((D-2)/3)}.  (8)

For fixed D>=3, eventually the second term is the smaller. The support
must therefore grow at least as a positive constant times n^((D-2)/3).
In D=3 this is a genuine divergent lower bound, proportional to n^(1/3).
It holds on coexact fields, not merely on a harmonic or unrestricted sector.
For bounded-size sample clusters, (7) yields the stronger n^(D-2)/B^2
support order. Neither exponent is asserted optimal for arbitrary S.

## A bounded-rank global observation still exists for these same profiles

For a centred lattice frequency k, the actual Fourier symbol obeys
lambda_n(k)>=16|k|^2/n^2. Hence

    mu_n lambda_n(k)>=c|k|^2/24.

Observe all real Fourier coordinates with |k|^2<24, componentwise. There
are at most9^D scalar real coordinates, since each centred coordinate
then lies in {-4,...,4}; real conjugate-pair bookkeeping preserves that
real dimension count. An orthonormal real Fourier convention gives

    E_mu_n(A)+c||C_global(A)||^2 >=c||A||^2

on all one-cochains, and hence on the coexact domain. The output dimension
is at most D(Nc^2-1)9^D, independent of n. The desired moment-based order
max{1,(n/sqrt(1+mu_n))^D} is also bounded independently of n.

This is a concrete local-form separation between a bounded-rank global
spectral map and bounded **point support**. It is not a lower bound on
the rank of every spatial averaging map. Point samples plus complementary
block means fall outside the point-support hypothesis and are not refuted.

## Verification, primary context and consolidation

The new proof was checked analytically against the actual positive-pair
curl, its backward adjoint, delta d_1*=0, periodic wraps, empty sample
sets and the possible zero witness when the norm lower bound is negative.
All constants above were derived in the displayed estimates. No Lean,
numerical oracle, rational replay or independent model audit was run in
unit177. An offline Linux/Colab replay specification is retained separately.

The existing paper comparison is the exact v7 source/PDF at
<https://airr.science/papers/ARR-2026-7EPM3V3DP796BBRR/versions/v7/>.
Its point-sampling subsection uses the weaker line-constant physical test;
its general rectangular question remains open. Its3.0/10 model assessment
does not assess or grade this new note.

Diening, Feireisl and Lu, *The inverse of the divergence operator on
perforated domains* (2017),
<https://www.numdam.org/item/COCV_2017__23_3_851_0.pdf>, studies continuum
correction operators under hole-size and separation conditions. It gives
context for preserving divergence near excluded regions, not a theorem
used to justify our finite formula. We assume no such continuum operator.

Teixeira, *Random Lattice Gauge Theories and Differential Forms* (2013),
<https://arxiv.org/abs/1304.3485>, provides primary lattice-exterior-calculus
context; its abstract was consulted. The specific counting-norm cubic
torus stencils here are those of the programme and are checked directly.
The cutoff-potential method and capacity motivation are classical in
spirit. No exhaustive priority search or new general capacity principle
is claimed; the contribution here is the explicit actual coexact adapter
and its dimension-three consequence relative to the existing dossier.

Group this result with the spatial-localization obstructions if a later
substantial manuscript revision warrants it. Do not submit a separate
small paper, inherit v7's score, or call the original rectangular problem
solved. PR29 remains20/41, TermSource=0; the continuum problem remains open.
