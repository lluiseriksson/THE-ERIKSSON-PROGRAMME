# Nonlinear observations of the actual finite-flat band

Analytic research note, unit031, 30 October 2026. This extends the same grouped
flat obstruction/derivative-repair dossier; it is not a separate paper, a change
to frozen PDF b37f, or a new Lean-verified result. The mathematical mechanisms
are classical. No priority, independent review or physical Yang-Mills claim is
made.

## Fixed conventions and concrete inputs

Use the counting Hilbert space of physical one-cochains E_n on (Z/nZ)^d, d>=1,
Nc>=2, with the actual trivial-background K0 and componentwise forward derivative
G. Weights w_n are fixed independently of the field A. Construct
V_wn=G*W_nG, not a structure carrying an assumed comparison. Suppose w_n<=M_n
pointwise with M_n>=0, and write Q_n(A)=<A,(K0+V_wn)A>.

At source c454346d873385e3a03e38e0f85f4f1439a032c7 the inputs are:

* physicalCenteredFourierBand_finrank in PhysicalFourierRankObstruction: for 2R<n,
  the actual real physical band S_R,n has dimension D_R=2(2R+1)^d.
* physicalCenteredFourierBand_hodge_le: on S_R,n,
  <A,K0 A> <= a_R/n^2 ||A||^2, where a_R=4*pi^2*d*R^2.
* ComponentwiseFlatHodge.componentwiseWeightedRepair_le_hodge: on all E_n,
  <A,V_wn A> <= M_n<A,K0 A>.

These are previously checked formal inputs, not fresh formal verification of
this note. Consequently, with epsilon_n=(1+M_n)*a_R/n^2,

    Q_n(A) <= epsilon_n ||A||^2  for every A in S_R,n.       (1)

Q_n(tA)=t^2 Q_n(A). No lower weight bound is needed for (1); nonnegative repair
weights are an additional option. The counterexamples below use w_n=0.

Fix a real finite-dimensional observation space F of dimension h, with any fixed
norm. Choose a
single positive integer R with D_R>h, e.g. R=h+1. Along any n->infinity with
(1+M_n)/n^2->0, epsilon_n->0. This includes a subsequence of the existing
n_L=(L+1)Nprime family, Nprime>0. All assertions below concern sufficiently
large n with 2R<n. They allow a positive neighborhood radius r_n depending on n.

## A. Odd continuous observations: exact zeros, arbitrary penalty

Suppose C_n maps the closed radius-r_n ball in E_n to F, is continuous and odd,
and Phi_n:F->R is finite-valued with Phi_n(0)=0. It need not be continuous or
quadratic. If one positive c satisfies

    c||A||^2 <= Q_n(A)+Phi_n(C_n(A))                        (2)

for every A in that ball, then c<=epsilon_n. Thus (2) cannot hold uniformly
along the above subsequence. Global coercivity is a special case.

Proof. Since D_R>h, choose an (h+1)-dimensional real subspace U of the actual
S_R,n. Identify its radius-r_n/2 sphere with the standard sphere S^h and F with
R^h. These coordinate identifications are linear and continuous. Borsuk-Ulam
gives x on this sphere with C_n(x)=C_n(-x); oddness gives C_n(x)=0. For h=0 the
target is the zero space and any sphere point suffices, without topology.
Insert x into (2) and (1), use Phi_n(0)=0, and divide by ||x||^2>0.

The zero is obtained on every positive sufficiently small sphere; homogeneity
of C_n is not assumed. The integer inequality is D_R>=h+1, not D_R>=h. For a
D-dimensional domain, the inclusion S^(D-1)->R^D has no zero, so replacing the
strict dimension condition in this topological step would be false.

This actually removes global linearity of the observation in the analytic
obstruction, replacing it by the weaker continuous-odd condition, while keeping
the original arbitrary finite Phi_n with Phi_n(0)=0. It does not remove a
physical input, and no Borsuk-Ulam axiom is introduced into Lean.

## B. Differentiable observations without oddness: a tangent obstruction

There is another route, with a different penalty hypothesis. Suppose C_n(0)=0
and C_n restricted to S_R,n is Frechet differentiable at 0 with real derivative
L_n:S_R,n->F. It need not be odd. Suppose there are finite K_n>=0 and delta_n>0
such that

    Phi_n(y) <= K_n||y||^2  whenever ||y||<=delta_n,
    Phi_n(0)=0.                                            (3)

No uniform bound on K_n, delta_n, the derivative, its remainder or r_n is
required. If (2) holds on its radius-r_n ball, again c<=epsilon_n.

Proof. Rank-nullity for the actual derivative L_n, with D_R>h, supplies a unit
v in S_R,n with L_n(v)=0. Differentiability and C_n(0)=0 give
C_n(tv)=o(|t|) as t->0. For each fixed n, choose t>0 tending to zero with
t<r_n and ||C_n(tv)||<=delta_n. Dividing (2) by t^2 and using (3),

    c <= Q_n(v) + K_n ||C_n(tv)/t||^2.

The final term tends to zero. Hence c<=Q_n(v)<=epsilon_n. Take the small-field
limit for EACH FIXED n before taking n->infinity. No interchange of limits or
uniform remainder estimate is hidden in the argument.

Only an upper quadratic bound is required of Phi_n, not differentiability or
positivity. For example, a twice continuously differentiable Phi_n with value
and derivative zero at 0 has such a local upper bound, by the ordinary Taylor
estimate. Unlike part A, part B adds (3); it is a trade of hypotheses, not a
removal of linearity for every penalty allowed in the old theorem.

## C. Explicit escapes and failed weakenings

Continuity, smoothness of the observation, or a fixed number of outputs alone
cannot extend the old linear rank obstruction to arbitrary nonlinear C.
For every actual E_n take F=R, w_n=0 and

    C_n(A)=||A||^2,   Phi_n(y)=y.

Then C_n is a smooth polynomial, C_n(0)=0, and Phi_n is smooth, with
Phi_n(C_n(A))=||A||^2. Since the actual K0 is nonnegative,

    Q_n(A)+Phi_n(C_n(A)) >= ||A||^2                        (4)

for all n,A, with c=1 and no repair. This uses the actual physical norm, not an
abstract positive-form assumption. Phi_n is nonnegative on the image of C_n;
if global nonnegativity is required, use Phi_n(y)=|y| with the same identity.
C_n is even rather than odd, and these penalties violate (3).

Conversely C_n(A)=||A||, Phi_n(y)=y^2 gives (4), with a globally 1-Lipschitz
observation and a quadratic smooth nonnegative penalty. Here C_n is not
differentiable at 0. Thus (3) plus mere Lipschitz continuity does not imply B.

A stronger boundary example keeps BOTH maps C^1, both derivatives at 0 equal
to zero, and the penalty globally nonnegative. Fix 1<alpha<2, beta=2/alpha:

    C_n(A)=||A||^alpha,   Phi_n(y)=|y|^beta.

Their composition is exactly ||A||^2, so (4) still holds. For A!=0,
DC_n(A)[H]=alpha*||A||^(alpha-2)<A,H>, and its operator norm is
alpha*||A||^(alpha-1)->0. The derivative at 0 is zero since alpha>1. Similarly
Phi_n'(y)=beta*sign(y)*|y|^(beta-1) tends to zero at 0 since beta>1. This proves
the asserted C^1 regularity, rather than assuming it. But
Phi_n(y)/y^2=|y|^(beta-2) is unbounded near zero. Thus even C^1 and stationary
penalties cannot replace the actual quadratic upper bound in B. Along a ray
the two powers have product alpha*beta=2, exactly the coercive order.

The scalar output here is an energy sensor, not reconstruction of all fields.
There is no conflict with nonlinear approximation lower bounds requiring a
decoder to recover an entire field. Every nonzero field has nonzero C_n(A) in
these examples; the zero needed in A is genuinely absent.

## Sources, validation and scope

Primary research source read: M. C. Crabb, A Borsuk-Ulam theorem for well
separated maps, arXiv:2401.02209v1 (2024), abstract and opening statement:
https://arxiv.org/html/2401.02209v1 . Its baseline is the classical common-zero
statement for m continuous odd functions on S^m, which is the only topological
input used here; no well-separated-map generalization is needed.

Also read H. Hadwiger and P. Mani, Continuous functions on the sphere and
isometries, Canadian Mathematical Bulletin12 (1969),753-757, introduction and
Proposition1, publisher PDF:
https://doi.org/10.4153/CMB-1969-097-4 . It explicitly uses the same classical
common-zero theorem. This is antecedent context, not a claim that their more
general isometry problem is our coercivity problem.

The original Borsuk1933 publisher record was verified, but its full text was
not recovered: EuDML returned403. Matousek's author page links chapter2 as
PostScript gzip, unsupported by the web reader; an Edinburgh PDF fetch failed.
No proof of novelty or absence follows from these access failures.

Nonlinear-width antecedents were checked through Ronald DeVore's own1998
survey, https://people.math.sc.edu/devore/publications/nlacta.pdf , and the
original authors' paper Cohen-DeVore-Petrova-Wojtaszczyk,
https://arxiv.org/html/2009.09907 . They concern approximation/recovery. No
identification with the penalty-only problem, exact priority claim or exhaustive
literature search is asserted. Both the topological and tangent mechanisms are
classical; the contribution to this programme is the explicit scoped transfer
and counterexamples closing an otherwise unjustified nonlinear extension.

Validation is an explicit same-agent analytic derivation: strict dimensions,
nonzero sphere radius, h=0, small-field limit order, actual physical positivity,
and the C^1 counterexample derivatives are checked above. It is not Lean
verification or independent scientific assessment. No runtime was opened for
this analytic unit and no Windows Lean/Lake/oracle was run. Previous formal
inputs retain their own exact-SHA evidence; they do not certify these nonlinear
conclusions. No new score, external-model review or PDF assessment is inherited.

No Wilson Hessian, hRpoly producer, interacting estimate, continuum limit or
physical mass gap is supplied. PR29 remains20/41 and TermSource=0. The frozen
reviewed PDF, its publication permissions and its outstanding human confirmation
are unchanged. Keep this result with the existing flat/weighted-repair dossier.
