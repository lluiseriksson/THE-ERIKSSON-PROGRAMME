# Signed occupied weights by the actual total-gradient identity

Analytic refinement, 1 November 2026. Source context: merged main75308f169c121ae2f3505d3a42381ebad62c5c74. Group with the existing coarse-information dossier; no new paper, PDF, deposit or Lean endpoint.

## Statement

Use exactly the finite flat unit-spacing counting-space setting, actual two-component coexact packet, local observation hypotheses and notation of restricted-support-positivity-20261101/proof.md. In particular D>=2, Nc>=2, c>0, M>=0, V=n^D; differentiable C:E->F with C(0)=0, finite-dimensional real F, local Phi(y)<=K||y||^2 and local repaired coercivity on the actual divergence-free sector. For every gradient direction i and occupied field component l in{0,1}, require only

 w(i,x,l)>=-1 for all x, and V^-1 sum_x w(i,x,l)<=M.

No condition is imposed on weights in the remaining components. Replace the previous occupied sign condition w>=0 by w>=-1. Then for R>=1 and2R<n, H=2R(2R+1)^(D-1), B=4*pi^2*D*R^2/n^2, the SAME bound holds:

 dim_R F >= H*(1-(1+M)*B/c).

The same alpha=min(1/4,sqrt(c/(8*pi^2*D*(1+M)))) and n>=2/alpha give dim_R F>=alpha^D*n^D/2. This removes the nonnegativity assumption on occupied repair weights, not every lower bound. The lower bound is explicitly retained and is strictly weaker, including D=2.

## Derivation in the actual quadratic form

Write G_i A_l(x)=A_l(x+e_i)-A_l(x), and

 Q_w(A)=<A,K0 A>+sum_(i,x,l) w(i,x,l)||G_i A_l(x)||^2.

The source theorem componentwiseFlatGradient_eq_hodge in YangMills/RG/ComponentwiseFlatHodge.lean identifies the ACTUAL flat Hodge quadratic form with the sum of ALL componentwise gradient squares, using unordered plaquettes, the actual counting norm, and the actual divergence term. It holds for every cochain A, not merely divergence-free ones. Together with componentwiseFlatGradient_energy and componentwiseWeightedRepair_energy, it proves by adding the finite sums

 Q_w(A)=sum_(i,x,l) (1+w(i,x,l))||G_i A_l(x)||^2.       (1)

This is an equality of the original quadratic form, not a new assumed form or a certificate of positivity. It uses unit spacing and the actual normalization of K0: an arbitrary comparison constant cannot replace the coefficient1.

For every vector A in the actual packet span S, all unoccupied components and their componentwise differences vanish. Hence(1) restricts to l=0,1. The retained lower bound w>=-1 makes each remaining coefficient nonnegative, and therefore proves Q_w(A)>=0 on the whole S. No invariance of S under the ambient operator, ambient positivity or full divergence-free positivity is assumed. The total weight1+w is a notation in a proved identity; the required conclusion is not supplied as structure data.

For each actual normalized real quadrature b_k,q, the already checked diagonal formula is

 ||G_i b_k,q,l(x)||^2=V^-1 |chi_k(e_i)-1|^2 |p_k,l|^2,
 sum_l |p_k,l|^2=1.

Consequently (1) and the occupied mean upper bounds give

 Q_w(b_k,q)<=sum_i |chi_k(e_i)-1|^2 sum_(l=0,1)|p_k,l|^2*(1+M)
            =(1+M)*lambda(k)<=(1+M)*B.

Multiplication by |p|^2*|chi-1|^2 is order preserving regardless of the sign of w; no individual nonnegativity of w was used. Both real quadratures have this diagonal, and summing the H orthonormal packet elements gives tr(P_S T inclusion_S)<=H*(1+M)*B, where T is the actual self-adjoint operator representing Q_w. This is genuine compression trace, not a defined diagonal surrogate.

Let U=S intersect ker DC(0). Original local coercivity along tv and C(tv)=o(t) imply c||v||^2<=Q_w(v) for v in U. The finite upper penalty constant may depend on n and may be negative; its absolute value controls the vanishing upper remainder. Extend an orthonormal basis of U inside S. The proved Q_w>=0 on every complementary vector and rank-nullity yield

 c*(H-dim F)<=c*dim U<=tr(P_S T inclusion_S)<=H*(1+M)*B.

Rearrange to obtain the stated bound, including dim F>H. The unchanged cutoff/floor calculation in the preceding proof yields density. No condition outside occupied components entered, and no occupied diagonal gradient direction was dropped.

## Strictness with all retained hypotheses satisfied

Take w=-1/2 on occupied components and0 elsewhere. These weights violate the former occupied nonnegativity condition for every D>=2, but satisfy the new bound and means with M=0. Formula(1) proves Q_w>=0 on ALL E. Let F=E, C=id, Phi(y)=c||y||^2 for any c>0. Then every retained local hypothesis holds globally, including repaired coercivity. This is a full-hypothesis witness of strict weakening, not a low-output construction or a sharpness witness for the rank constant. The old theorem remains valid on its smaller domain.

## Boundary of the coefficient argument

For any epsilon>0, put w=-1-epsilon on EVERY component, direction and site. Equation(1) gives Q_w=-epsilon*<A,K0 A>. For n>=3 an occupied component1 wave of frequency1 in coordinate0 is actual divergence-free and has lambda=4sin^2(pi/n)>0; it belongs to the R=1 packet span by choosing the frequency with all other labels0. Thus Q_w<0 on a nonzero vector in S. All means remain <=0. Nevertheless all retained observation/coercivity conditions are compatible: translation is an isometry and sum_(i,l,x)||G_i A_l(x)||^2<=4D||A||^2, so C=id, F=E and Phi(y)=(c+4D*epsilon)||y||^2 restore coercivity globally.

Therefore allowing a constant below-1 weight without another restriction invalidates the specific complementary-positivity proof even under the original local observation hypotheses. The threshold-1 is exact for the universal scalar-coefficient guarantee Q_w>=0; it is NOT a necessary condition for positivity of every variable-weight form, nor a counterexample to the rank inequality itself. Mean upper bounds alone do not repair the failed positivity argument. A different argument for more general signed occupied weights remains open.

## Verification, novelty and limits

This proof was checked symbolically against the actual three source identities and the preceding packet/rank argument. No new Lean theorem or independent full rebuild is claimed. Coefficient absorption is an elementary consequence of the established flat Hodge identity; no original-priority claim. The primary library trace documentation confirms basis-independent trace, not novelty of this refinement: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Trace.html . Source identities are pinned to main75308f16 above. The exact combined priority is unestablished. No interacting/continuum mass gap, physical hypothesis removal or new paper. PR29 stays20/41;TermSource=0.

## Model assessments and review context

Same preparing Codex agent, continuing author context; actual backend and effort unexposed. No blind, independent, external-model or human review. This exact source receives its own first numerical assessment in assessment.md, bound by SHA256. No grade from an earlier note or frozen PDF applies here. The public v4 PDF and its7/10 assessment are unchanged.
