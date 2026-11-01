# Only the occupied two components need spatial mean upper bounds

Analytic refinement, 1 November 2026. This is a grouped supplement to the
existing mean-weight rank-density argument, not a separate paper. Its refined
two-component hypothesis is **not** a Lean endpoint of the current eight-name
weighted-energy oracle: that source still states bounds for every component.

Fix spatial dimension D >= 2, Nc >= 2, positive lattice side n and V = n^D.
Use the actual flat cochain space, backward divergence and componentwise
forward-gradient repair from the existing dossier. Write

    Q(A) = <A,K0 A> + sum_(i,x,l) w(i,x,l) ||A_l(x+e_i)-A_l(x)||^2.

Assume w(i,x,l) >= 0 everywhere. Replace the previous spatial-mean upper
assumptions for all D field components by just

    V^-1 sum_x w(i,x,0) <= M,
    V^-1 sum_x w(i,x,1) <= M             for every gradient direction i,

where M >= 0 is independent of n. No spatial-mean or pointwise upper bound is
needed for components l outside {0,1}. Both diagonal pairs (i,l)=(0,0),(1,1)
are retained; this is not an off-diagonal-only assumption.

Keep the original observation and penalty hypotheses: a finite-dimensional
real normed output F; C differentiable at zero, C(0)=0, derivative L; a finite
K and delta0>0 with Phi(y)<=K||y||^2 for ||y||<delta0; and r,c>0 such that

    c||A||^2 <= Q(A)+Phi(C(A))   for divergence-free A with ||A||<r.

For integer R>=1 with 2R<n, put

    H = 2R(2R+1)^(D-1),     B = 4*pi^2*D*R^2/n^2.

Then the same conclusion holds:

    dim_R F >= H * (1-(1+M)*B/c).

In particular, with

    alpha = min(1/4, sqrt(c/(8*pi^2*D*(1+M)))),
    rho = alpha^D/2,

every integer n>=2/alpha satisfies dim_R F >= rho*n^D. For a family, only
D,Nc,M,c need be fixed; the local neighbourhoods, derivative remainder,
observation/penalty data and nonnegative weights may vary with n.

## Proof of the removed upper-bound hypotheses

For the same actual positive-first-frequency packet as in
`spatial-mean-volume-density-20261031/083-proof.md` (analytic source
e6b603252e63ee7ebfa2c5507023ad49acdd40c8), let chi_k be a character,
s_i=chi_k(e_i)-1 and t_i=1-chi_k(-e_i). Its normalized complex polarization is

    h_k^2 = |t_0|^2+|t_1|^2 > 0,
    p_0 = t_1/h_k,    p_1 = -t_0/h_k,    p_l = 0 otherwise,
    U_k,l(x) = V^-1/2 p_l chi_k(x).

Positive first frequency gives t_0!=0. Thus sum_l |p_l|^2=1, and the actual
backward divergence cancels t_0*p_0+t_1*p_1=0. Use the two actual internal
real quadratures J(U_k), J(i U_k). The constructed finite-character Gram
gives an orthonormal family spanning its actual H-dimensional image S.
These are conclusions of the construction, not assumed certificates.

Every field in S is identically zero at components l outside {0,1}.
The componentwise forward gradient preserves the field-component index:
its (i,x,l) entry is exactly A_l(x+e_i)-A_l(x). Hence these gradient entries
are also identically zero outside {0,1}, for every vector in S. Consequently
the entire quadratic form restricted to S is unchanged by any modification
of weights on the other components. This is a pointwise support identity,
not a comparison or an assumed trace bound.

For either actual quadrature, its squared gradient entry is exactly

    V^-1 |s_i|^2 |p_l|^2.

Writing b(i,l)=V^-1 sum_x w(i,x,l), its weighted energy is therefore

    sum_i |s_i|^2 (|p_0|^2 b(i,0) + |p_1|^2 b(i,1))
      <= M * sum_i |s_i|^2.

Only the two displayed mean assumptions were used. The Hodge part is
lambda(k)=sum_i |s_i|^2, and lambda(k)<=B. Sum over the actual orthonormal
packet to obtain the genuine compression trace bound tr_S Q<=H(1+M)B.
This does not require S to be invariant under the weighted operator and
does not assert a pointwise Rayleigh bound for arbitrary superpositions.

For v in S intersect ker L, differentiability and the local quadratic
penalty imply C(tv)=o(t) and c||v||^2<=Q(v) after division by t^2 and passage
to the limit. Let f=dim_R F and U=S intersect ker L. Rank-nullity yields
dim U>=H-f. Extend an orthonormal basis of U to S. Its U-diagonal entries
are at least c; the other entries are nonnegative because K0 and the actual
componentwise repair with w>=0 are positive semidefinite on the whole space.
Thus c(H-f)<=tr_S Q<=H(1+M)B, proving the finite-side bound.

For n>=2/alpha choose R=floor(alpha*n). Then R>=alpha*n/2>=1 and 2R<n;
(1+M)B<=c/2. Hence f>=H/2=R(2R+1)^(D-1)>=alpha^D*n^D/2, proving density.
No upper bound on the other components occurs in this argument. Their
nonnegativity is still used for the global complementary-trace step.

## Strict weakening and limits

For D>=3, set the two occupied-component weight families equal to zero and
set w(i,x,l)=n^(2D) for every other component. These weights are nonnegative
and satisfy the refined assumptions with M=0 for every n, while no fixed
uniform upper bound on all component means holds along the family. This
example separates the weight hypotheses; it does not assert that any
particular low-dimensional observation satisfies the coercivity hypothesis.
For D=2 there are no other components, so this refinement removes no bound.

The refinement needs the actual componentwise repair and the actual
two-component support. A quadratic repair coupling different field
components would need a separate proof. Positivity, diagonal-pair means
within the two occupied components, original local observation/penalty
assumptions and c>0 remain. There is no physical/interacting/continuum gap
claim. Coordinate support, finite Fourier and trace/rank mechanisms are
classical; exact priority of this combined sufficient-hypothesis statement
is unestablished. It is not independent scientific review or formal closure
of the operator-trace/density endpoint.

## Model assessments and review context

Same preparing Codex agent and continuing programme context, 1 November
2026. Actual backend model/effort unexposed; no blind, independent, external
model or human review, no score. Source inspection and symbolic argument
only for this refinement; no numerical test is presented as universal proof.
The exact current Lean source's all-component means are not silently
relabelled as a formal two-component theorem. Preserve the complete proof
and the scope/positivity objections with the consolidated dossier.
