# Growing-volume observation budgets and the quadratic repair scale

Status: analytic proof by the preparing agent, 2026-10-31. **Not a new
Lean-verified theorem, external assessment, or originality claim.** This note
extends the same flat obstruction dossier; it is not a separate paper and is
not included in the frozen public c9de v3 PDF.

Repository basis: `6b7f5cf0f6d69bba40f982ef05c49d3e1cdfff39`, containing
the finite coexact energy theorem tested at
`299736d8ba7fb530c37bfe73a07a59faa289aaad` in Colab054/054b.
Those runs certify their exact six endpoints, not the additional arguments here.

## 1. Concrete setting and retained hypotheses

Fix D>=2 and Nc>=2; a=Nc^2-1. The actual real physical space is the
counting-L2 space of a-component fields on positively oriented bonds of
(Z/nZ)^D, with n>=1. This is precisely the repository's SUNLieCoord and
PhysicalGaugeOneCochain coordinate model; no identification with an interacting
Lie-algebra Hessian is asserted. Work at the trivial background, unit spacing.
Let H_n be the actual flat Hodge operator and S_n=ker(div_n) the actual linear
divergence-zero sector. Let G_n be the componentwise forward gradient.

The proved global identity is q_n(x)=<x,H_n x>=||G_n x||^2. For actual
constructed repair weights w_n(p)<=M_n, M_n>=0, its proved energy formula gives

    Q_n(x) = q_n(x)+<x,V_(w_n)x> <= (1+M_n) q_n(x).                 (1)

Nonnegativity of w_n is not required for this upper bound; the examples below
use nonnegative weights. Observations C_n:E_n -> F_n have finite-dimensional
real normed outputs, are Frechet differentiable at0, and C_n(0)=0. Penalties
satisfy Phi_n(y)<=K_n||y||^2 for ||y||<delta_n with delta_n>0. Assume

    c||x||^2 <= Q_n(x)+Phi_n(C_n(x))                             (2)

on S_n intersect a positive-radius ball about0, with c>0 independent of n.
The radii, derivative norms, K_n, delta_n, outputs and maps can vary with n.
No uniform radius or uniform penalty constant is needed.

## 2. The family lower bound from the checked finite theorem

For any integer R>=1 with2R<n and

    (1+M_n)*4*pi^2*D*R^2/n^2 < c,

the checked `coexactFlat_local_coercivity_false`, contraposed, implies

    m_n := dim_R F_n >= 2R(2R+1)^(D-1) >= (2R)^D.                (3)

All band construction, injection, dimension, divergence and Hodge comparison
obligations are conclusions already proved for the actual operator; they are
not new family-structure fields.

For a common M_n<=M, set

    alpha = min(1/4, sqrt(c/(16*pi^2*D*(1+M)))) > 0.

For every integer n>=2/alpha take R=floor(alpha*n). Then R>=alpha*n/2>=1,
2R<=n/2<n, and the threshold in (3) is at most c/4<c. Consequently

    m_n >= alpha^D n^D                                       (4)

for every such n, not merely a dilation subsequence. Therefore m_n=o(n^D)
is impossible under a uniform weight cap. This closes the analytic family
question without assuming an integer cutoff family. It also supplies the
explicit all-n strengthening of the initially selected n=kR route.

For varying caps the identical proof gives (3), and gives

    m_n >= (alpha_n*n)^D,  alpha_n=min(1/4,
                  sqrt(c/(16*pi^2*D*(1+M_n)))),                (5)

whenever alpha_n*n>=2. In particular, if M_n=o(n^2), then alpha_n*n tends
to infinity, so **a uniformly bounded observation dimension is impossible**.
This weakens the former uniform-cap hypothesis to subquadratic growth for
the fixed-output conclusion. It does not derive a subquadratic cap for any
interacting theory or remove all repair-growth assumptions.

An even shorter proof of the last conclusion: for m_n<=m choose one fixed
R with(2R)^D>m; eventually2R<n and (1+M_n)4*pi^2*D*R^2/n^2<c. This
contradicts (3). The argument remains valid along any unbounded subsequence
on which M_n/n^2 ->0 and m_n stays bounded.

## 3. Exact optimal output dimension, analytic classification

The following strengthens the nonoptimal selected-band lower bound. It
optimizes over admissible repairs w<=M and observations C; it does **not**
claim attainability for each preassigned nonconstant w or each preassigned C.

At fixed n,M>=0,c>0 put tau=c/(1+M). Let

    L_n(tau) = range of the spectral projection of H_n|S_n onto [0,tau).

Then the minimum possible real output dimension for (2), even among nonlinear
differentiable C and locally upper-quadratic Phi, is exactly

    b_n(c,M) = dim_R L_n(c/(1+M)).                            (6)

Necessity: if m<dim L, the derivative DC(0)|L has a nonzero kernel vector v.
Differentiability gives C(tv)=o(|t|); the penalty upper bound then gives
limsup_(t->0) Phi(C(tv))/t^2 <=0. Divide (2) along the exact sector line tv
by t^2, use the fixed quadratic Q, and obtain c||v||^2<=Q(v).
But (1) and the finite strict spectral cutoff give
Q(v)<(1+M)*tau*||v||^2=c||v||^2, a contradiction. Finite dimensionality
makes the largest eigenvalue in the nonzero low subspace strictly below tau.
If L=0 the necessity is simply m>=0. Values of Phi away from its neighborhood
are irrelevant. Evaluating (2) at0 and its local upper bound also forces
Phi(0)=0. Even for negative K, K||C(tv)||^2/t^2 tends to0, so the proof
does not quietly require K>=0.

Sufficiency: choose actual constant weights w(p)=M. Then
Q=(1+M)q. Choose an orthonormal real basis of L, let C be its coefficient
map (extended to the full ambient space by orthogonal projection), and let
Phi(y)=c||y||^2. For x in S write x=x_low+x_high. Orthogonality and the
spectral decomposition imply

    Q(x)+Phi(Cx)
      =(1+M)q(x_low)+c||x_low||^2+(1+M)q(x_high)
      >= c||x_low||^2+c||x_high||^2.

This is global coercivity and uses exactly dim L coordinates. The threshold
is strict: an eigenvalue equal to tau already supplies coefficient c and
requires no observation. This removes a potential off-by-one spectral error.
The norm on the chosen output is Euclidean. Necessity allowed any norm on F.

## 4. Compute that dimension for the actual flat divergence sector

Use normalized characters chi_k(x)=n^(-D/2) exp(2*pi*i*k.x/n).
Each forward difference multiplies by exp(2*pi*i*k_j/n)-1, so

    lambda_n(k)=4 sum_(j=1)^D sin^2(pi*k_j/n).                 (7)

The actual identity q=||G||^2, polarization and Fourier orthogonality make
H scalar multiplication by lambda_n(k) on every bond/internal component.
The divergence symbol is the nonzero row (1-exp(-2*pi*i*k_j/n))_j for k!=0.
Its rank is1 for each internal coordinate, so its kernel has complex
dimension a(D-1); at k=0 the row vanishes and dimension is aD. This derives
the constraint rank frequency by frequency rather than pretending the full
divergence has bounded codimension.

Let N_n(tau)=#{k in(Z/nZ)^D:lambda_n(k)<tau}. Since tau>0, zero is included.
Then

    b_n(c,M)=a*((D-1)*N_n(c/(1+M))+1).                       (8)

Here N counts all residues, not conjugate pairs. The complex low subspace
is stable under conjugation; complexifying its real fixed space recovers
it, hence its complex dimension equals the real dimension of that real
space. Conjugate pairs and self-conjugate Nyquist frequencies are therefore
counted correctly without inserting another factor2. The constant mode has
multiplicity aD, not a(D-1). The formula also handles n=1: N=1 and b=aD.
Equation (7) uses the actual difference operator, including n=2; it does
not silently switch to a simple-graph convention with collapsed edges.

## 5. Matching growth and the actual boundary

Take centered integer frequency representatives r_j with |r_j|<=n/2,
choosing exactly one representative at each even-n Nyquist endpoint. Since
2u/pi<=sin u<=u for0<=u<=pi/2,

    16|r|^2/n^2 <= lambda_n(r) <= 4*pi^2|r|^2/n^2.            (9)

Thus only |r|<n*sqrt(tau)/4 can occur below tau, while every centered
|r|<n*sqrt(tau)/(2*pi) is below tau. Cube counting shows
N_n(tau)<=min(n^D,(1+n*sqrt(tau)/2)^D), with the integer count interpreted
as the count of points in that open coordinate cube. The displayed real
bound follows because an interval of length2B centered at0 contains at
most1+2B integers. Constants may safely be enlarged; no equality is claimed.
Together with (5) and (8), this gives matching order

    b_n(c,M_n) ~_constants max(1, n^D/(1+M_n)^(D/2))          (10)

for fixed D>=2,Nc>=2,c>0, uniformly over n and M_n>=0; constants depend
on those three fixed parameters. Proof of the lower comparison when
alpha_n*n<2: the constant-mode bound b>=aD suffices, because the right
side in (10) is then bounded by a parameter-dependent constant. When
alpha_n*n>=2 use (5). The upper comparison follows from the preceding
cube count with tau=c/(1+M_n), (8), and
(1+x)^D<=2^(D-1)*(1+x^D).

For M_n->infinity with M_n=o(n^2), a sharper equivalent is

    b_n(c,M_n) ~ a(D-1)*omega_D/(2*pi)^D *
                      c^(D/2)*n^D/(1+M_n)^(D/2).            (11)

To justify this instead of merely invoking a continuum analogy, set
rho_n=n*sqrt(tau_n)/(2*pi)->infinity. Bound (9) confines every low mode
to |r|/n<=sqrt(tau_n)/4->0. Uniformly there, sin u/u->1, so the low set
is squeezed between integer Euclidean balls of radii rho_n and
(1+o(1))*rho_n; for small tau these balls avoid Nyquist endpoints. Unit
cubes centered at integer points squeeze ball counts between volumes of
balls of radii R-sqrt(D)/2 and R+sqrt(D)/2. Their ratio tends to1 as
R->infinity. Therefore N_n(tau_n)~omega_D*rho_n^D, which proves (11).
The +a in (8) is negligible here. Fixed tau does not justify this small-
frequency asymptotic; (11) is not claimed when M_n remains bounded.

At M_n=beta*n^2, beta>0, (10) yields bounded achievable output dimensions.
For M_n/n^2->infinity, the smallest nonzero eigenvalue is
4 sin^2(pi/n)>=16/n^2 for n>=2. Eventually every nonconstant mode is above
tau_n, and the optimum is exactly aD: normalized constant-mode observation
is sufficient and necessary. In particular w_n=n^2 and that observation
give global coefficient1, as recorded in unit040. These are actual
constructed repairs, so quadratic growth really defeats the fixed-output
no-go. A threshold-resonance count at exact quadratic scaling requires
the strict inequality in (8); replacing it with a limiting closed ball
without a boundary analysis is not justified.

## 6. Primary-source check, novelty and relevance

The classical discrete-torus spectrum (7) is independently present as
2D-2 sum cos(2*pi*k_j/n) in G. Chinta, J. Jorgenson and A. Karlsson,
*Zeta functions, heat kernels and spectral asymptotics on degenerating
families of discrete tori*, arXiv:0806.2014v1, section2.1, printedp5
(PDF page index4):
https://chinta.ccny.cuny.edu/publ/cjk_tori_final.pdf .
Only the explicit spectral formula/normalization and surrounding definition
were checked here; this source is not claimed to prove our observation
classification. Its authors already study large discrete-torus spectra,
so the Fourier mechanism and spectral counting are not new discoveries.

Equations (6)-(8) are the preparing agent's classical spectral/rank argument
in this coordinate model, not an established priority claim. No exhaustive
literature or n-width/minimax priority search was performed. The practical
gain over the checked selected-band theorem is a sharp attainable budget,
the all-n family implication and the optimal-order quadratic growth boundary.
This consolidates and bounds the existing route; it does not support another
paper consisting of these corollaries alone.

Formal correctness, originality and physical relevance stay separate:
the new analytic arguments have no Lean compilation record yet; originality
is unestablished; scope is finite, flat, unit spacing. Physical spacing1/n
inserts n^2 into the operator and changes the obstruction. No interacting
producer, Wilson estimate, hRpoly hypothesis or continuum mass gap is proved.
PR29 remains20/41 and TermSource=0. No external model assessed this note.

## 7. Next single formal task and abandonment condition

Keep one active route: formalize the family budget deduction from the
actual finite coexact endpoint, starting with fixed R and subquadratic caps
for bounded outputs; then the integer-dilation positive-density bound.
Do not encode the desired cutoffs, spectral count, divergence rank or Hodge
comparison as assumed structure fields. The sharper spectral optimality
proof is a related analytic target, not a second concurrently active route.

The first formal endpoint should quantify actual w_n, C_n, derivatives,
Phi_n and positive local radii, retain the actual local quadratic bound,
and derive the contradiction from (1+M_n)/n^2->0 and bounded dimF_n.
Only new owned Linux Colab evidence may upgrade that endpoint to verified.
Three substantive units without mathematical progress require preserving
failures and either an exact normalization/type/cutoff blocker or a route
change. A coercive example with truly subquadratic caps and bounded outputs
under all retained hypotheses would falsify the proposed result.
