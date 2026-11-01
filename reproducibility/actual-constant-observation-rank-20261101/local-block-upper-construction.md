# An explicit local-block observation also attains the analytic rank order

Analytic construction only. This supplements the same unit080 mean-budget order question, not a new paper or Lean endpoint. Frozen PDF97bd... and all its version-specific assessments remain unchanged. Classical path/Poincare mechanism; no new general principle or priority claim.

Use D>=2,Nc>=2,c>0,m>=0,n>=1, h=D(Nc^2-1) and x=n/sqrt(1+m). Set the actual scalar gradient weights everywhere to w=m-1, so actual Q_w=m sum of squared forward differences and every required positiveTOTAL mean equalsm.

For m<cD use singleton blocks. For m>=cD let t=sqrt(m/(cD)), l=min(n,floor(t)); t>=1 and l>=1. Partition each cyclic coordinate represented by0,...,n-1 into consecutive intervals of lengthl except a final shorter nonempty interval. Product these intervals into disjoint boxesB. They cover all sites; each side lengthL_i(B)<=l. There are exactly ceil(n/l)^D boxes. No wrap edge is needed inside a box, and every internal forward edge is an actual torus forward edge with nonnegative energy in Q_w.

Define mu_B(A)=|B|^{-1} sum_(x in B) A(x), including allh field/internal real coordinates. The actual real-linear observationC lists sqrt(|B|)*mu_B(A) over the boxes, with real Euclidean codomain of dimensionh*ceil(n/l)^D. It is continuous, C(0)=0 and DC(0)=C. Set Phi(y)=c||y||^2, K=c and arbitrary positive delta,r. Thus no penalty or derivative certificate is assumed.

For a finite Hilbert-valued functionf on B, the exact variance identity is

 sum_(x in B)||f(x)-mu_B||^2=(2|B|)^{-1} sum_(u,v in B)||f(u)-f(v)||^2.

For each ordered pair, change coordinates in a fixed order along the ordinary rectangular grid. The path has length at mostDl. Cauchy-Schwarz bounds its squared increment byDl times the sum of squared edge increments. For a fixed internal edge in directioni, the ordered pairs traversing it number at most|B|*L_i<=|B|l: the free coordinates offi contribute|B|/L_i, and ordered coordinate endpoints contribute at mostL_i^2. This remains true for any final shorter side. Summing over pairs and dividing by2|B| therefore gives the safe bound

 sum_B ||f-mu_B||^2 <= D*l^2 sum_(internal edges)||df||^2.

All constants are derived here; the smaller unused factor1/2 is discarded deliberately. If l=1 variance is identically zero. The ordinary orthogonal mean decomposition gives

 ||A||^2=sum_boxes(sum_sites||A-mu_B||^2+|B|*||mu_B||^2).

When m>=cD, cD*l^2<=m. Consequently on ALL actual cochains,

 c||A||^2 <= m sum_actual_edges||dA||^2+c||C(A)||^2
           =Q_w(A)+Phi(C(A)).

The singleton case is the identity observation and proves the same statement for m<cD, even m=0. Thus the original divergence-free local coercivity and all differentiability/penalty hypotheses hold globally. Mean budgets are exactly the requestedm; no interaction/background or continuum identification is introduced.

Rank count: if l=n, q=h. Otherwise floor(t)<n and floor(t)>=t/2 for t>=1, whence

 ceil(n/l)<=1+2n/t=1+2sqrt(cD)*n/sqrt(m)
           <=1+2sqrt(1+cD)*x  (m>=cD).

Therefore q<=h*(1+2sqrt(1+cD))^D*max(1,x^D). For m<cD, q=h n^D<=h*(1+cD)^(D/2)*x^D, bounded by the same displayed constant. This matches the universal lower order from unit080 while requiring only actual local block averages, with translation-invariant constant repair weights. The observation need not be Fourier/global or translation-equivariant; it is explicitly local to each disjoint block. No sharp constant or claim about every nonconstant weight profile follows.

Boundary checks: n=1, m=0, m=cD, l=1, l=n, a nondivisible last coordinate interval, arbitrary rectangular products, even/odd torus periods. Each box has positive integer size, so averages and square-root weights are defined. The local path ignores wrap edges; this can only decrease the nonnegative gradient sum. No aliasing or complex-conjugacy argument is needed.

Assessment context: same preparing Codex agent; served backend/effort unexposed; no independent or human review. First qualitative source assessment6/10 for this local construction. Objections: O1 all-block adapter is analytic, not compiled/formalized; O2 path/Poincare and block means are classical, priority unestablished; O3 constants are loose, no exact minimizer; O4 linear block maps must eventually be instantiated with the actual finite partitions and counting norm in Lean, not certificate fields; O5 observation is not translation-equivariant, and the construction is a constant-weight witness rather than sufficiency for all admissible weights; O6 no interacting/continuum physical gap; O7 no grade inheritance, frozen-PDF change or separate paper. Preserve this note even if formalization is abandoned.