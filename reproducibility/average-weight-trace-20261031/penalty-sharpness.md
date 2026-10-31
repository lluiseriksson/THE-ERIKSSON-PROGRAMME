# Why the nonlinear penalty hypothesis cannot simply be dropped

Unit050, 2026-10-31. Complete mathematical counterexamples and a regularity
tradeoff, checked on paper. NOT Lean-verified, independently reviewed, or
published. Definition context: 41530cd67e67e2b9b6d749b811a7d13e0f568ecf.
This belongs to the existing coarse-information dossier, not a separate paper.

## The proposed weakening that is false

The existing local tangent argument assumes C(0)=0, differentiability of C
at zero, and a local upper bound Phi(y)<=K||y||^2. A tempting replacement
is to require only a nonnegative continuous, Lipschitz, or C1 penalty.
None of those replacements works with merely C1 observations. In particular,
small output dimension or a zero derivative does not by itself mean that
Phi(C(A)) is negligible compared with ||A||^2.

The examples below retain fixed output F=R, C(0)=0, and DC(0)=0. They
satisfy the coercivity inequality globally, on every subspace, and thus on
the actual divergence-free physical subspace. They do not contradict the
current formal theorems, whose quadratic upper hypothesis they violate.

## A. Polynomial observation, globally Lipschitz penalty

Let E be any nonzero finite real inner-product space, let c>0, and set

    C(x) = ||x||^2 in R,       Phi(y) = c|y|.

C is a quadratic polynomial: C(x)=<x,x>, hence infinitely differentiable.
Its derivative is DC(x)h=2<x,h>. At zero the derivative is the zero linear
map. Directly, its Frechet remainder quotient is

    |C(h)-C(0)-0(h)| / ||h|| = ||h|| -> 0   (h!=0).

Phi is nonnegative, continuous, and globally c-Lipschitz; Phi(0)=0.
Nevertheless, for every x,

    Phi(C(x)) = c||x||^2.                                  (A1)

If Q(x)>=0 is any quadratic energy, then

    c||x||^2 <= Q(x)+Phi(C(x))                              (A2)

holds globally. This includes Q=0, and also the actual finite flat Hodge
energy plus the actual G*WG repair with nonnegative weights. Restricting
to any divergence-free subspace preserves (A1)-(A2). Neither the ambient
dimension nor the subspace dimension affects the one-dimensional output.

Yet ker DC(0)=E. With Q=0, the proposed tangent conclusion
c||v||^2<=Q(v) fails for every nonzero v. The exact failed inference is

    C(tv)=t^2||v||^2=o(|t|),
    Phi(C(tv))/t^2=c||v||^2,   not o(1).                    (A3)

There is no finite local quadratic upper constant for Phi: for y>0,
Phi(y)/y^2=c/y -> infinity. Thus this example cannot be admitted by
changing a constant or neighbourhood in the existing hypothesis.

## B. Even C1 regularity of BOTH maps is insufficient

For any fixed 1<p<2 let beta=2/p>1 and define

    C_p(x)=||x||^beta,       Phi_p(y)=c|y|^p.

For x!=0 the derivative of C_p is

    DC_p(x)h=beta*||x||^(beta-2)*<x,h>.

Its operator norm is beta*||x||^(beta-1), which tends to zero at zero.
The derivative at zero is zero because the remainder quotient equals
||h||^(beta-1)->0. Away from zero the displayed formula is continuous;
together these statements prove that C_p is C1 on E.

For y!=0, Phi_p'(y)=cp*sign(y)*|y|^(p-1). At zero its derivative is zero,
since |Phi_p(y)|/|y|=c|y|^(p-1)->0. The derivative is continuous at zero.
Thus Phi_p is also C1, nonnegative, and has a minimum at zero. Still,

    Phi_p(C_p(x))=c||x||^(beta*p)=c||x||^2.                 (B1)

The quadratic upper ratio is c|y|^(p-2)->infinity. A particularly concrete
choice is p=4/3, beta=3/2. Both first derivatives vanish at zero, but the
composition is exactly a positive quadratic form. Derivative rank zero
and output dimension one cannot yield a rank obstruction in this class.

For every 0<p<2, the same power formula remains differentiable at zero
with DC_p(0)=0 and satisfies (B1); C1 of Phi_p is claimed only for p>1.
For p=1, part A supplies a polynomial observation and Lipschitz penalty.

## C. Exact scaling test and a genuine regularity tradeoff

Along a derivative-kernel direction v the existing differentiability
hypothesis gives ||C(tv)||=o(|t|), not a prescribed faster rate. Under
Phi(y)<=K||y||^p near zero, the normalized upper estimate is

    Phi(C(tv))/t^2 <= K (||C(tv)||/|t|)^p |t|^(p-2).

For p=2 this tends to zero. For p>2 it also does; indeed the power upper
bound already implies a quadratic upper bound on a sufficiently small
ball. For p<2, the last factor diverges and the first factor need not
compensate: (B1) supplies the exact balancing example beta*p=2. This is
a falsification of a weakening, not a new hypothesis-elimination theorem.

There is a different sufficient route. Suppose, on each fixed direction
v in ker DC(0), the observation has a second-order expansion

    C(tv)=t^2 H_v + o(t^2),

with H_v in the finite output space. Such an expansion follows, for
example, from C being twice continuously Frechet differentiable near zero.
Suppose Phi is Frechet differentiable at zero, Phi(0)=0 and D Phi(0)=0.
Then Phi(y)=o(||y||), so

    Phi(C(tv))=o(t^2).                                    (C1)

Proof with zeros included: ||C(tv)||/t^2 is bounded near zero; for every
epsilon>0, differentiability of Phi gives |Phi(y)|<=epsilon||y|| near
zero. As C(tv)->0, the absolute value of the quotient in (C1) is bounded
by epsilon times that fixed bound, including times when C(tv)=0. Let
epsilon decrease to zero. No division by ||C(tv)|| is needed.

If Phi>=0 near zero and Phi(0)=0, differentiability already forces
D Phi(0)=0: apply the directional derivative to both h and -h at the
local minimum. Consequently a nonnegative C1 penalty and a C2 observation
suffice for the same kernel coercivity step. The penalty need not have a
quadratic upper bound, e.g. |y|^(4/3). This is a TRADEOFF: stronger
observation regularity replaces the quadratic penalty bound. It is not
a weakening for the existing merely differentiable observation class,
and no actual observation's C2 property has been proved here.

For a quadratic Q, local coercivity at tv, divided by t^2 and followed by
(C1), yields c||v||^2<=Q(v). Positivity and the finite trace/rank argument
can then be applied on a finite test space, as in the original route.
That remaining Lean composition is not discharged by this note.

## Verification, sources, relevance and limits

Verification here is a direct algebraic and limiting proof: exponent
beta*p=2; exact remainder quotients; explicit derivatives and their norms;
the same scalar output in all dimensions; exact failure on ker DC(0);
and explicit proof that no local quadratic constant exists. No numerical
sampling, compilation, oracle, model review, or inherited verdict is used.
The actual physical applicability uses only its finite real inner-product
structure and nonnegative Q. Taking Q=0 already proves the refutation
without relying on any unverified physical operator identity.

Primary background consulted 2026-10-31:

- Mathlib, Analysis.InnerProductSpace.Calculus:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Calculus.html
  (`hasStrictFDerivAt_norm_sq`, `contDiff_norm_sq`).
- Mathlib, Analysis.SpecialFunctions.Pow.Deriv:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.html
  (real-power differentiation away from zero; derivatives at zero in this
  note are proved explicitly by the remainder quotients).

These are primary background sources, not compilation receipts or evidence
of novelty. Their live documentation is not the pinned repository toolchain.
The norm and power mechanisms are classical; no original-priority claim is
made. The value here is to rule out a specific extension of this programme's
nonlinear rank argument before it is used. The full average-weight trace/rank
formalization remains open. No physical/interacting/continuum Yang-Mills
hypothesis is eliminated. PR29 stays20/41, TermSource=0. AIRR v3 is unchanged.

Single next question: complete the positive compressed-trace/rank theorem
with the existing quadratic penalty hypothesis and actual normalized strip.
Do not replace that hypothesis with continuity, Lipschitz continuity or C1
regularity alone. Retain this counterexample in any consolidated manuscript.
