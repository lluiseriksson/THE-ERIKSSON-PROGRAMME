# Frozen local signed stability does not localize: an extensive actual negative band

Supporting counterexample156, grouped with signed-diagonal155 in the existing flat-coarse-rank dossier. Analytic construction, not Lean verified or an independently reviewed/priority-certified result. The already reviewed46-page PDF and its7.6AI report are unchanged and do not assess this note.

## Closed bounded question and mechanism

Can the global constants a>kappa in result155 be replaced by a positive pointwise compensation margin eta(x)=a(x)-kappa(x), even with a(x)=2eta(x),kappa(x)=eta(x), a uniformly good inverse-moment/mean profile, and uniformly coercive frozen physical forms? Answer:NO. The actual signed variable-coefficient form can have a negative subspace of positive dimension density. This is a refutation of that SIGNED localization mechanism, NOT of result155 or the original POSITIVE-scalar critical rectangular conjecture. The auxiliary question is closed here; the original single active rectangular question stays open and common-refinement stays STOPPED3.

Hypotheses tested: actual periodic cochains, pointwise2:1 compensation, positive margin1<=eta<=2mean(eta), all normalized inverse moments bounded uniformly in lattice side, and uniform frozen physical coercivity. Proposed mechanism: multiply the unweighted Korn identity by a spatial coefficient and use the local margin as if it were a positive scalar Hodge coefficient. Falsifier: an actual divergence-zero negative-energy subspace too large to be removed by bounded information/repair rank. Abandon the proposed localization upon that falsifier; do not replace its conclusion by a supplied certificate.

## Actual lattice, coefficients and frozen positive control

Fix D>=2,m>=1 and n=6s with s>=1. The programme case D>=3,m=Nc^2-1 is included. Let X=(Z/nZ)^D, N=n^D, with counting norms and literal periodic D_i^+,D_i^- and delta A=sum_i D_i^- A_i. All nonzero cochains below lie in one fixed real unit internal coordinate T0.

Use tile origins t=6k, k in{0,...,s-1}^D, and envelopes E_t=t+{0,1,2,3}^D. Put
q_D=(120D-32)*2^(D-2), R_D=q_D/2+2=(60D-16)*2^(D-2)+2.
Set rho=1 inside each E_t except its point p_t=t+(1,...,1), and rho=R_D at p_t and everywhere outside the envelopes. Define eta_n(x)=n^2*rho(x). The ACTUAL total gradient coefficients are
alpha_i,j(x)=2eta_n(x) if i!=j; alpha_i,i(x)=-eta_n(x).
They are not all positive. The form is the original flat Hodge H0 plus G*W G with W=alpha-1; unweighted flat cancellation gives H0=sum|D_i^+ A_j|^2 before W is added.

The margin profile eta is positive and has exactly
bar(rho)=[R_D*(6^D-4^D+1)+(4^D-1)]/6^D, mu_n=n^2*bar(rho).
Since bar(rho)>=R_D*[1-(2/3)^D]>=5R_D/9,
1<=eta_n<=n^2R_D<2mu_n, mean(eta_n)=mu_n.
For EVERY fixed r>0,
mean((mu_n/eta_n)^r)=mean((bar(rho)/rho)^r)<=R_D^r.
Thus the critical r=D/2 moment and even every higher fixed inverse moment are uniformly bounded; mu_n>=n^2, so max{1,(n/sqrt(1+mu_n))^D}=1.

Each coefficient field FROZEN at one site x has off-diagonal value2eta_n(x) and diagonal value-eta_n(x), constant across the comparison torus. To see its physical stability directly, write L=sum_i|D_i^+ A_i|^2, O=sum_i!=j|D_i^+ A_j|^2, V=|delta A|^2 and S=sum_i<j|D_i^+ A_j+D_j^+ A_i|^2. Periodic unweighted adjointness gives S=O+V-L. The finite Fourier support split in155 gives O+V>=lambda_n*|A-mean A|^2,lambda_n=4sin(pi/n)^2. Therefore the frozen form plus2eta_n(x)V equals eta_n(x)*(S+O+V)>=eta_n(x)*lambda_n*|A-mean A|^2. On delta A=0 the divergence term vanishes. Since n^2lambda_n>=16, every frozen form has physical coercivity>=16 modulo constants; normalized global means with penalty16 complete that frozen estimate. This is a derived frozen fact, not an assumed data field.

## Compact actual negative packets

On a six-site line take b=(0,1,2,0,0,0), chi=(0,1,1,0,0,0), extended by zero outside their two nonzero sites in each tile. Define
psi_t(x)=b(x1-t1)*b(x2-t2)*product_(j>=3) chi(xj-tj),
A_t,1=D_2^-psi_t*T0, A_t,2=-D_1^-psi_t*T0, other components zero.
All shifts here are the actual n-periodic shifts, not a smaller artificial torus. Commuting backward shifts proves delta A_t=0 identically. Telescoping proves every component has zero mean. Its field support lies inside t+{1,2,3}^2*{1,2}^{D-2}; all its forward-gradient START sites lie inside E_t. No derivative wraps between tiles: coordinate4 and5 are empty buffers.

The exact one-dimensional square sums are
sum b^2=5; sum(D^-b)^2=sum(D^+b)^2=6;
sum(D^+D^-b)^2=14; sum chi^2=sum(D^+chi)^2=2.
Product factorization therefore gives, on each actual packet,
|A_t|^2=60*2^(D-2), L=72*2^(D-2), O=(60D+20)*2^(D-2),
and 2O-L=q_D.
At p_t the only nonzero forward derivatives are D_1^+A_t,1=T0 and D_2^+A_t,2=-T0. Hence its local L-density is2 and its O-density is0 (also in the extra directions, because chi is constant from1to2). The high coefficient outside E_t sees no gradient, and every other tile's peak sees no gradient of A_t. Thus the actual variable form is exactly
Q_n(A_t)=n^2*[q_D-2(R_D-1)]=-2n^2<0.              (1)
The weighted diagonal/off-diagonal identity cannot be obtained by multiplying the unweighted identity by eta: the coefficient must remain inside the sums. No weighted cancellation was asserted in the calculation.

The choice R_D-1 instead gives zero energy for this packet, and R_D gives the first integer value above that packet's threshold. This is a sharp threshold for this chosen packet, not a claim of the smallest destabilizing contrast over every physical field.

## Extensive obstruction for arbitrary linear observations and finite-rank repairs

The envelopes E_t are disjoint. Hence the entire forward-gradient stencils, and the actual field supports, of distinct A_t are disjoint. For every real coefficient family u_t,
Q_n(sum_t u_t A_t)=-2n^2*sum_t u_t^2,
|sum_t u_t A_t|^2=60*2^(D-2)*sum_t u_t^2.
Consequently W_n=span_R{A_t} is an actual divergence-zero negative-definite subspace of dimension J=s^D=(n/6)^D, with Rayleigh quotient -n^2/[30*2^(D-2)]. This is a negative-index lower bound, not a continuum eigenvalue claim.

Let C_n:E_n->F_n and V_n:E_n->E_n be ANY actual real linear maps, and let Phi_n(0)=0, with no other penalty restriction. If dim F_n+rank V_n<J, the restricted map(C_n,V_n)|W_n has a nonzero kernel vector. For that actual physical field A, Q_n(A)<0, C_nA=V_nA=0. Therefore
c|A|^2<=Q_n(A)+Phi_n(C_nA)+<A,V_nA>
is impossible for every c>0. Any such coercivity claim requires dim F_n+rank V_n>=(n/6)^D. In particular, no bounded-rank observation/repair has the proposed O(1) mean-budget order, even though every frozen form is uniformly stable and the positive compensation-margin profile meets the cap/mean/inverse-moment conditions.

For comparison the SAME positive margin eta_n used on ALL gradient channels gives Q_eta>=n^2H0, so Q_eta+16|C_mean A|^2>=16|A|^2 on all cochains. The failure is specifically the signed, spatially varying compensation, not a counterexample to positive scalar Hodge sufficiency or to all rectangular partitions for that positive form.

Result155 is intact: its single global lower bound a=2n^2 and global negative-diagonal bound kappa=n^2R_D do NOT satisfy a>kappa. The false proposed extension uses the pointwise pair(2eta(x),eta(x)) instead, for which the global unweighted proof is invalid.

## Verification, attribution and publication limits

This is an explicit finite-difference/negative-packet adaptation, not an original general theory of failure of ellipticity localization. A primary-source comparison read Gloria/Ruf, arXiv:1805.05150v2, abstract and introduction: strong ellipticity and global coercivity/homogenization are distinct in classical elasticity. Our signed periodic cochain form, divergence constraint, compact stencil and rank lower bound are not identified with their continuum material theorem. No theorem is imported from that paper, no exhaustive priority search is claimed, and no independent scientific review is attributed.
https://arxiv.org/abs/1805.05150v2
https://arxiv.org/html/1805.05150

Prepared exact finite diagnostics compute actual integer fields, periodic derivatives, coefficient profiles, disjoint stencils and Gram identities with actual execution status recorded separately from this proof. Their finite execution scope is not an all-n Lean proof. This supporting negative result stays grouped with155; it receives neither a standalone paper nor the frozen main PDF's7.6assessment. No PR29 hypothesis, positive-profile rectangular hypothesis, interacting gap or continuum obligation is removed. Pending exact author permission is not repeated or bypassed.