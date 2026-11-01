# Rank density with arbitrary signed weights outside the actual packet support

Analytic theorem,1 November2026; grouped refinement of the existing coarse-information dossier. Not a new paper or a Lean-verified endpoint. Base formal source218ae50be26c491a1d18a39fac5fbc5213df42ee checks actual normalized packet amplitudes and signed-weight energy identities; the following support/rank transport is a written analytic proof.

## Exact statement

Fix spatial dimension D>=2, Nc>=2 and the actual flat lattice one-cochain space E on X=(Z/nZ)^D, with counting Euclidean norm. Let K0 be the actual nonnegative flat Hodge operator and use the componentwise forward gradient G_i A_l(x)=A_l(x+e_i)-A_l(x). Let w(i,x,l) be arbitrary finite real weights and

 Q_w(A)=<A,K0 A>+sum_(i,x,l) w(i,x,l)||G_i A_l(x)||^2.

For l=0,1 assume w(i,x,l)>=0 and V^-1 sum_x w(i,x,l)<=M for EVERY gradient direction i, where V=n^D and M>=0. For l outside{0,1} impose NO sign, lower, upper, mean, or size condition. Weights may depend on n and need not have uniform magnitude there. Retain the original differentiable observation C:E->F with C(0)=0, finite-dimensional real normed F, local upper bound Phi(y)<=K||y||^2, and local repaired coercivity

 c||A||^2 <= Q_w(A)+Phi(C(A))

for sufficiently small actual divergence-free A, with c>0. All other local hypotheses are as in083-proof.md, and may vary with n except the fixed family parameters D,Nc,M,c.

For R>=1 and2R<n, H=2R(2R+1)^(D-1), B=4*pi^2*D*R^2/n^2,

 dim_R F >= H(1-(1+M)B/c).

For alpha=min(1/4,sqrt(c/(8*pi^2*D*(1+M)))) and n>=2/alpha this implies dim_R F>=alpha^D*n^D/2. The removed hypotheses are global nonnegativity and all bounds on unoccupied-component weights, not the two occupied components' nonnegativity or mean upper bounds. For D=2 there is no unoccupied component, hence no weakening.

## Construction and proof

Use the actual positive-first-frequency normalized coexact packet from083-proof.md and the unit066 supplement. For each k in{1,...,R}x{-R,...,R}^(D-1), chi_k(x)=exp(2*pi*i*k.x/n), t_i=1-chi_k(-e_i), h=(|t_0|^2+|t_1|^2)^(1/2)>0. The actual amplitudes are p_0=t_1/h, p_1=-t_0/h, p_l=0 otherwise. Let U_k,l=V^(-1/2)p_l chi_k. J embeds the complex plane into two actual orthonormal internal coordinates. Both real quadratures J(U_k),J(i U_k) have the checked normalized real Gram. They span an actual H-dimensional divergence-free subspace S, supported in components0,1.

For EVERY A in S, G_i A_l=0 when l is outside{0,1}, because both values in the componentwise difference vanish. Set w_hat=w on occupied components and0 elsewhere. Directly in the original finite quadratic sum,

 Q_w(A)=Q_w_hat(A)  for every A in S.                 (1)

No comparison-field or positivity certificate is assumed. The identity is derived from the actual support and actual componentwise operator; it is valid regardless of the signs or magnitudes of discarded weights. Since w_hat>=0 globally and K0>=0,

 Q_w(A)=<A,K0 A>+sum_(i,x,l in{0,1}) w(i,x,l)||G_i A_l(x)||^2 >=0  (A in S).  (2)

This proves the ONLY positivity needed below. It does not assert Q_w>=0 on E or on the full divergence-free sector. The removed global positivity hypothesis is not relocated into an assumed compressed-positivity structure.

For either quadrature at frequency k, ||G_i A_l(x)||^2=V^-1 |chi_k(e_i)-1|^2 |p_l|^2. Thus its repair diagonal is <=M*sum_i |chi_k(e_i)-1|^2, using only occupied-component means and sum_l |p_l|^2=1. Its Hodge diagonal is lambda(k)=sum_i |chi_k(e_i)-1|^2<=B. Consequently, for this actual orthonormal basis b of S,

 sum_b Q_w(b) <= H(1+M)B.                            (3)

For precision, let T be the self-adjoint matrix on E representing the displayed actual quadratic form, P_S the orthogonal projection and T_S=P_S T inclusion_S. For A,B in S, <A,T_S B>=<A,T B>. Therefore the genuine trace of T_S equals sum_b <b,T_S b>=sum_b Q_w(b) by trace in an orthonormal basis. This constructs the actual compression; it does not define trace to equal the desired bound or require S to be invariant under T.

Let L=DC(0) and U=S intersect ker L. Differentiability yields C(tv)=o(t) for v in U. Divide local coercivity along tv by t^2 and use the finite local upper penalty bound to get c||v||^2<=Q_w(v). This argument also works for a finite negative K by bounding Phi(C(tv))/t^2 above by |K| ||C(tv)||^2/t^2. Rank-nullity gives dim U>=H-dim F. Extend an orthonormal basis of U to one of S. The U entries have Q_w>=c and EVERY remaining entry is nonnegative by the PROVED restricted positivity(2). Basis invariance of the genuine compression trace and(3) give

 c(H-dim F) <= c dim U <= tr(T_S) <= H(1+M)B.

If dim F>H the first inequality still holds, since its left side is negative. Rearrange for the finite-side statement. With R=floor(alpha*n), R>=alpha*n/2>=1,2R<n and (1+M)B<=c/2. Thus dim F>=H/2=R(2R+1)^(D-1)>=alpha^D*n^D/2. No bound or sign outside the occupied pair has been used.

## Full-hypothesis example: ambient and divergence-free positivity can fail

For D>=3,n>=3 let occupied weights equal0 and every other component weight equal -n^(2D), for all i,x. Occupied mean bound holds with M=0. Translation is an isometry in counting norm and ||shift_i A_l-A_l||^2<=4||A_l||^2 by the triangle inequality. Summing gives

 Q_w(A) >= -4D n^(2D)||A||^2  for ALL A in E,

since K0>=0. Take F=E,C=identity and Phi(y)=(c+4D n^(2D))||y||^2, with any fixed c>0. Then ALL retained local observation/penalty/coercivity hypotheses hold globally, with derivative identity and a finite n-dependent K. The theorem permits that dependence. This is not a low-output construction or a sharpness assertion for the rank bound.

Moreover take a nonzero plane-wave field only in component l=2, varying in coordinate0 with frequency1. Its backward divergence vanishes because its component2 is independent of coordinate2. Its Hodge eigenvalue is lambda=4 sin^2(pi/n)>0; its weighted repair is -n^(2D)lambda||A||^2. Hence

 Q_w(A)=(1-n^(2D))lambda||A||^2<0.

This explicitly satisfies the FULL theorem assumptions while violating positivity even on the full divergence-free sector. The permitted high-dimensional observation repairs that negative direction. Global positivity is therefore not necessary for this rank-density conclusion under the retained local repair hypotheses. For D=2 this example and the proposed weakening are unavailable.

## Boundaries and provenance

All gradient directions and diagonal pairs within occupied components remain. Signed weights ON the occupied pair are not covered: their mean upper bounds alone do not prove(2). A repair coupling different field components, a differently supported packet or a claim about the whole divergence-free sector requires another argument. No physical, interacting or continuum mass-gap claim. This is a sufficient theorem and strict full-hypothesis example, not a necessary-and-sufficient characterization.

The earlier unit066 theorem remains true with its stronger all-weight nonnegativity premise. Its global positivity was sufficient and unnecessarily strong, as its final assessment explicitly allowed; no previous Lean theorem is refuted or relabelled. Current Lean endpoints still have all-component means and do not prove this analytic refinement or actual operator-trace transport.

Primary mathematical-library reference checked1November2026: Mathlib.LinearAlgebra.Trace, LinearMap.trace_eq_matrix_trace, https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Trace.html . This supports basis invariance/diagonal computation; it is not evidence of originality or a compiled proof of this refinement. The finite Fourier, support and trace/rank mechanisms are classical; priority of the precise combined statement is unestablished.

## Model assessments and review context

Prepared and assessed by the same continuing Codex programme agent with prior context. Actual backend model and effort are not exposed. No independent/blind/external-model/human review, score, target grade or inherited PDF verdict. Complete objections and separate disposition are recorded in source-assessment.md. This exact note has a symbolic proof review only; no Lean build or numerical experiment is claimed.