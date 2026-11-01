# Tensorized local observation upper witness

Analytic refinement of unit082, same mean-budget order question; no Lean endpoint or PDF change. Base41a9cd8a7a7742b5687560e65082484525bb2066. This note concerns an explicitly chosen constant repair, not all fixed heterogeneous profiles; see concentrated-repair-quantifier-counterexample.md.

Let u_0,...,u_(l-1) be vectors in a finite real Hilbert space. The actual counting variance is

 sum_a||u_a-mean(u)||²=(1/l)sum_(a<b)||u_b-u_a||².

Telescoping and Cauchy-Schwarz give ||u_b-u_a||²<=(b-a)sum_(a<=s<b)||u_(s+1)-u_s||². For a fixed edge between positionsp-1 andp, 1<=p<=l-1, the exact coefficient is

 (1/l)sum_(a<p<=b)(b-a)=p*(l-p)/2.

Indeed there arep left positions andl-p right positions, and their average distance isl/2. Therefore the counting variance is bounded by

 C_l*sum_s||u_(s+1)-u_s||², C_l=floor(l²/4)/2<=l²/8.

Forl=1, C_l=0 and no edge is required. Forl=2, C_l=1/2 and the inequality is an equality for everyu; this checks normalization.

For a rectangular product B with side lengthsl_i, uniform independent coordinates give the finite tensorization inequality Var_B(f)<=sum_i E_(othercoordinates) Var_(coordinatei)(f). One direct proof uses induction: split total variance into expected conditional variance in one coordinate plus variance of its conditional mean; apply the inductive inequality to that mean, and Jensen to the differences under the remaining average. Apply the scalar proof to each Hilbert coordinate and sum. Multiplying the normalized inequality by|B| and applying the one-dimensional bound on every fibre yields

 sum_(x inB)||f(x)-mean_B f||²
 <=sum_i C_(l_i)*sum_(internal i-edges inB)||diff_i f||²
 <=(l²/8)*sum_(all internal edges inB)||diff f||²

when everyl_i<=l. Unlike the earlier direct whole-path boundD*l², this coefficient has no extraD factor. No periodic wrap edges occur inside the boxes. Short final intervals and arbitrary rectangular side lengths satisfy the same bound.

Partition the actual torus coordinates into consecutive intervals of length at mostl and use their products. For every actual field component and Lie coordinate let C(A)_(B,j)=sqrt(|B|)*mean_B(A_j), with real Euclidean codomain dimension q=h*ceil(n/l)^D, h=D*(Nc²-1). Exact orthogonal decomposition gives ||A||²=sum_B residual_B²+||C(A)||². The actual constant repairw=m-1 has total energy Q_w(A)=m*sum_actual_forward_edges||diff A||² on every cochain. Thus c*l²/8<=m implies c||A||²<=Q_w(A)+c||C(A)||² globally; the original local nonlinear hypotheses hold with linearC, Phi=c||y||² andK=c. Forl=1 residual=0, so this is true evenm=0.

For m<c/8 take singletons. For m>=c/8 take l=min(n,floor(sqrt(8*m/c)))>=1. If l=n, q=h. Otherwise floor(t)>=t/2 fort>=1 and ceil(n/l)<=1+2n/t. Withx=n/sqrt(1+m),

 2n/t=sqrt(c*(1+m)/(2m))*x<=sqrt(4+c/2)*x.

Hence in every case

 q<=h*(1+sqrt(4+c/2))^D*max(1,x^D).

In the singleton smallm case, q=h*(1+m)^(D/2)*x^D and (1+m)^(1/2)<=sqrt(1+c/8)<=1+sqrt(4+c/2), which verifies the same bound. This remains an attainable witness for the infimum over repairs; it does not contradict the concentrated-profile necessity.

Primary-source novelty check: Chihao Zhang, AA2025 Lecture8, instructed by Chihao Zhang and scribed by Xuanxuan Liu/Yuchen He, Theorem1 and its martingale/Jensen proof explicitly give classical variance tensorization. Read directly at https://chihaozhang.com/teaching/AA2025/lectures/lec8/lec8.html . This note's finite counting normalization, edge coefficient and adapter are derived above. No originality claim for tensorization/Poincare. An author-hosted Tropp PDF was found but direct retrieval timed out; no claim that its full contents were inspected.

Model assessments and review context: first exact-note source6/10, same preparing Codex agent, actual served backend/effort unexposed, no independence/human review or editorial acceptance. O1 not Lean-compiled; O2 tensorization and paths are classical, priority unestablished; O3 coefficientl²/8 is not the sharp path spectral constant; O4 finite partition/counting adapter remains to formalize, not a certificate assumption; O5 only an explicit constant-repair witness, no universal heterogeneous upper guarantee; O6 no physical/continuum gap; O7 no PDF edit or inherited grade. Boundary checks includel=1,2, n=1, m=0,c/8, nondivisible final intervals andl=n.
