Terminal analytical source audit323A

Verdict: ACCEPT for the exact frozen analytical source, with the cited homogeneous moment theorem as external input. All twelve preregistered checks C1-C12 pass on the stated fixed-rho, dimension-independent critical Ls-budget hypotheses. No blocking mathematical defect or counterexample was found. This accepts the sufficient rate and its operator/spectral consequence, not a sharp transition, novelty, formal certification, publication readiness or a numerical review score. The existing source321C comparison is substantive: the new quadratic expansion supplies precisely the endpoint information its compactness-only argument did not supply.

Frozen identities and method

Repository lluiseriksson/THE-ERIKSSON-PROGRAMME; PR270 https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/270. Exact head c4377edace1f883a2061fe9b2c0ebfe40ce02f9d; base e75c4d9a8beb2e0cdb28bebc5229a3c8b7bb513f. Subject research/quadratic-deficit323/source323A.txt is 8,749 raw Git UTF-8/LF bytes, SHA-256 2de9fb0027e02ade7e3920352a5a3593154778c8cd478d5bb7fecd066bac0bfc. It is the only tracked path changed by this PR. The stored raw Git file matches the assignment hash; no checkout normalization is silently substituted for it.

Body capture uses gh pr view 270 --repo lluiseriksson/THE-ERIKSSON-PROGRAMME --json body,headRefOid,baseRefOid. Decode JSON body, replace CRLF with LF, apply TrimEnd() to trailing whitespace, append one LF, encode UTF-8 without BOM. The assigned and observed normalized body is 980 bytes with SHA-256 2626f1e497bc032f68f14e315a945eb742fb9b85a00da8b8855a713892e3cb54. This is the assignment's TrimEnd normalization, not the terminal-LF-only rule of some earlier audits. Initial/final raw PR captures, normalized bodies and state observations are retained. Both endpoint comparisons passed: initial 2026-11-13T20:07:14.1188627Z, final 2026-11-13T20:13:43.0756328Z. final-state.json records all five successful head/base/body/source/status comparisons. These are endpoint observations, not continuous monitoring. No branch or body edits were made.

Primary-source scope

The exact upper moment inequality applies to real p>=2 and integer homogeneous degree from zero through half the dimension, with probability expectations. Taking its p-th root gives precisely the factor used by the candidate. The parameterization, zero value and derivative/concavity are the cited published inputs. They were checked directly in [Kirshner and Samorodnitsky, Theorem1.3 and Propositions2.6/2.7](https://arxiv.org/html/1909.11929v1). The paper's complete upper-moment proof is not independently recertified here. The source text candidly treats it as an external theorem; this audit does likewise.

One nonblocking source observation is preserved: the primary HTML's intermediate derivative-at-zero display, math id S5.Ex227.m1, switches a minus to a plus in front of the same limiting logarithm. The subsequent final derivative display has the correct positive value. The candidate uses that correct value, and its direct expansion below verifies the sign without importing the inconsistent intermediate equality. This is an observed typographic inconsistency in the cited v1 rendering, not a defect newly introduced by source323A and not a claim about other versions. The raw HTML retains both displays.

C1 — Probability normalization and exponents: PASS.

All expectations and Lq norms use uniform probability on the cube. Walsh characters therefore have L2 norm one and distinct characters are orthogonal. The {0,1} versus {-1,1} notation changes no probability normalization or Fourier degrees. With s=(1+rho)/(1-rho), s-1=2rho/(1-rho), hence p=2s/(s-1)=(1+rho)/rho=1+1/rho. Consequently 1/s+2/p=1 and rho=1/(p-1). For fixed 0<rho<1 this is a fixed finite p>2, exactly in the cited theorem's real-exponent range. Q=P_sqrt(rho) has the degree-j multiplier rho^(j/2). Ordinary Boolean hypercontractivity at equality gives ||Q||_(2->p)<=1. The two uses of the letter s, for a degree in the external paper and for the moment exponent here, are not confused. The degree-zero input has norm ratio one and psi(p,0)=0.

C2 — Substitution, factor two and logarithm conversion: PASS.

Set delta=(1-z)/2 and A=((1+z)^p+(1-z)^p)/2. Then (1-delta)^p+delta^p=2^(1-p) A, so the external constant (p-1) cancels exactly against log2(2^(1-p)). Also A'=(p/2)((1+z)^(p-1)-(1-z)^(p-1)). Substitution in the parameter x gives x=z A'/(p A); the factor 1/2 from 1/2-delta is canceled by the relative powers of two in numerator and denominator. Multiplying the formula for psi by ln2 gives F(x):=ln2 psi=ln A-(p/2)h(x)-p x ln z. In the positive branch z>0, v=z^2, so the last term is -(p/2)x ln v. This second factor 1/2 is essential and is handled correctly. No binary/natural logarithm factor remains missing.

C3 — Real-p analyticity and quartic coefficient: PASS.

For any fixed real p>2, (1+z)^p and (1-z)^p have convergent real analytic binomial expansions for |z|<1. Their average is even with A(0)=1; near zero it is positive and ln A is even analytic. In particular A=1+a2 z^2+a4 z^4+O(z^6), where a2=p(p-1)/2 and a4=p(p-1)(p-2)(p-3)/24. Taking the logarithm gives b4=a4-a2^2/2. Factoring p(p-1)/24 leaves (p-2)(p-3)-3p(p-1)=-2(p^2+p-3). Thus b4=-p(p-1)(p^2+p-3)/12, exactly as in the candidate. Nothing here requires integral or even p. The sign changes of individual binomial coefficients for 2<p<3 do not invalidate the convergent analytic expansion.

C4 — Inverse and remainders: PASS.

Even analyticity means ln A can be viewed as an analytic function of v, not as an unjustified analytic inverse in z. Its logarithmic derivative yields x=2v(d/dv ln A)/p=(p-1)v+(4b4/p)v^2+O(v^3). Let a=p-1>0, b=4b4/p. The inverse function theorem at v=0 applies because dx/dv=a is nonzero, giving v=x/a-bx^2/a^3+O(x^3). For small positive x, v>0. Factoring x/a before taking logs gives ln v=ln x-ln a-bx/a^2+O(x^2), since the remaining factor is 1-bx/a^2+O(x^2). Multiplying this last remainder by x produces O(x^3); it does not produce an omitted O(x^2) or O(x^2 ln x).

Substituting the inverse into ln A gives a2(x/a-bx^2/a^3)+b4 x^2/a^2+O(x^3)=(p/2)x-b4 x^2/a^2+O(x^3). The entropy expansion h=-x ln x+x-x^2/2+O(x^3) is valid as x decreases to zero. The only nonanalytic term is the explicitly displayed x ln x; it cancels exactly. All constants and neighborhoods in the O terms may depend on the fixed p. No uniform real-p remainder assertion is made.

C5 — Quadratic coefficient and endpoint: PASS.

In F=ln A-(p/2)h-(p/2)x ln v, the linear x terms cancel, the x ln x terms cancel, and the logarithmic linear term is (p/2)ln a times x. The quadratic coefficient is -b4/a^2+p/4+(p b)/(2a^2)=p/4+b4/a^2. Replacing b4 and a gives
p/4+b4/(p-1)^2 = [3p(p-1)-p(p^2+p-3)]/[12(p-1)] = -p^2(p-2)/[12(p-1)].
Thus subtracting F/p from x ln(p-1)/2 yields
Delta_p(x)=p(p-2)x^2/[12(p-1)]+O(x^3).
The sign and normalization in the central claim are correct.

As a separate hand derivation, differentiating F along x=z A'/(p A) cancels the derivative of ln A against the x v'/v term. It gives F'=(p/2)ln[x/((1-x)v)]. The inverse above implies F'=(p/2)ln a+(p/2)(1+b/a^2)x+O(x^2). Integration reproduces the same quadratic coefficient. This checks the sign by a second symbolic route; no software mathematics was run.

The limiting coefficient C_p=p(p-2)/(12(p-1)) is strictly positive only for p>2. At p=2, psi=0, ln(p-1)=0 and the entire deficit is zero, not merely its quadratic term. That excluded endpoint cannot support a positive c_p. For example, at rho=1 the noise is the identity and a nonconstant parity perturbation of the density need not disappear for k<L. This is an adverse endpoint check, not an extension of the theorem. Fixed rho is essential; c_p can tend to zero as p decreases to2. No uniformity near rho=0 or1 is certified.

C6 — Global positive quotient: PASS.

For 0<y<=1/2, strict concavity together with the finite tangent derivative at zero gives a strictly positive tangent deficit Delta_p(y). A concave differentiable graph lies below that tangent; equality at a positive point would force an affine segment, contradicting strict concavity. At zero the expansion supplies Delta_p(x)/x^2 -> C_p>0, which strict concavity alone would not supply.

Define y=min(x,1-x). The extension a_p(x)=Delta_p(y)+(x-y)ln(p-1)/2 is continuous at x=1/2, positive for every x>0, and has a_p(1)=ln(p-1)/2>0. Dividing by x^2 preserves continuity away from zero. Giving the quotient its limiting value C_p at zero makes it continuous and positive on the compact interval [0,1]. Its attained minimum c_p is positive and depends only on p. Consequently a_p(x)>=c_p x^2 on all of [0,1]. The candidate does not claim c_p=C_p or an explicit numerical lower bound. Indeed the local coefficient cannot simply be used globally for arbitrary p: C_p grows on the order of p whereas the quotient at x=1 is only ln(p-1)/2. The existence/minimum formulation avoids this invalid stronger claim.

C7 — All levels and parity: PASS.

For j<=L/2, multiply the homogeneous norm bound by rho^(j/2). Its natural logarithmic exponent is -j ln(p-1)/2+(L ln2/p)psi(p,j/L)=-L a_p(j/L), hence at most -c_p j^2/L. For j>L/2, multiplying a Walsh-level-j polynomial by total parity replaces every support A by its complement. This maps it exactly into level L-j and preserves absolute pointwise values and both relevant norms. The homogeneous bound can then be used at L-j, but the noise multiplier remains rho^(j/2), not rho^((L-j)/2). That retained multiplier gives precisely the same a_p(j/L). This argument does not commute parity through Q. At j=L the reduced function is constant and the multiplier remains rho^(L/2); a_p(1)=ln(p-1)/2 gives exact agreement. Both even-L middle degree and the two odd-L middle degrees are covered.

C8 — Tail estimate and prefactor: PASS.

For m=floor(k/2), the complementary projection has levels m+1 through L. Triangle inequality in Lp, the preceding per-level estimate and Cauchy-Schwarz give
||Q Hf||_p <= exp[-c_p(m+1)^2/L] sum_(j>m)||f_j||_2
<= sqrt(L-m) exp[-c_p(m+1)^2/L] (sum_(j>m)||f_j||_2^2)^(1/2)
<= sqrt(L+1) exp[-c_p(m+1)^2/L] ||f||_2.
The final factor is deliberately loose, but valid. Orthogonality is used only in L2, not falsely in Lp. The prefactor is not dropped. Also ||Q Pi||_(2->p)<=1 follows by applying the Q bound after the L2 contraction Pi; no Lp contraction of Pi is required.

C9 — Exact marginals, integer cutoffs, degree endpoints: PASS.

For the weighting law r u_L, exact uniformity on every subset of size at most k makes all nonconstant Fourier coefficients through k vanish. Mean-one gives the zero constant coefficient of h=r-1, including when k=0. The matrix entry between chi_A and chi_C in Q M_h Q is rho^((|A|+|C|)/2) hhat(A symmetric_difference C). If both supports have size at most m=floor(k/2), their symmetric difference has size at most2m<=k, so Pi D Pi=0 exactly. This is weighted-law information, not a statement about a Perron stationary distribution.

Since I=Pi+H, the exact identity D=HD+Pi D H follows after deleting Pi D Pi. It covers the H-H block once; no cross term is lost. For k=0, m=0 and the canceled block is the constant block. For k=L-1 the stated high-tail estimate still applies. For k=L all Fourier coefficients of h vanish, so r=1, D=0 and the exact conclusion follows without the tail argument. L>=1 avoids a zero denominator and supplies a second eigenvalue. For odd and even k, floor(k/2)+1>=k/2, so weakening the exponential to exp[-c_p k^2/(4L)] is legitimate. At k=L the weaker positive bound is trivially true because D=0.

C10 — Signed Holder, operator norm and actual spectra: PASS.

Minkowski gives ||h||_s<=B+1. Each unit-vector bilinear form for HD has h, QHu and Qv as factors; their Holder exponents are s,p,p and sum reciprocals to one. Signed h causes no issue because Holder bounds absolute values. The other block uses QPi u and QHv. Applying one high-tail bound and one unit hypercontractive bound in each block gives
||D|| <= 2(B+1)sqrt(L+1) exp[-c_p(floor(k/2)+1)^2/L].
This is an actual operator norm estimate by duality, not a Rayleigh quotient only. Real functions suffice because the finite matrices are real symmetric; their real and complex Hilbert-space operator norms agree. No hidden complex-polynomial extension of the cited theorem is required.

With A=Q M_sqrt(r), one has AA*=S and A*A=T. These are square matrices on the same 2^L-dimensional space, so their entire eigenvalue lists coincide, including multiplicities of zero. No inverse of r or positive density floor is needed. P_rho has first two ordered eigenvalues1 andrho for L>=1. Self-adjoint norm perturbation bounds each of the first two ordered eigenvalues of S within ||D|| of these values. Further <1,S1>=E r=1, so lambda1(S)>=1. The identical T spectrum proves the asserted actual top-two limits even if r vanishes on part of the cube. Dividing by the positive leading eigenvalue is justified; for example the normalized-gap error is at most (1+rho)||D|| once the same perturbation bound is used. The candidate does not infer these conclusions merely from two trial vectors.

C11 — Scale, necessity and unresolved window: PASS.

For fixed p and B the logarithm of the weaker bound is ln[2(B+1)]+(1/2)ln(L+1)-c_p k^2/(4L). If k^2/(L ln(L+1)) tends to infinity as L grows, its negative term dominates the retained logarithmic prefactor, proving norm convergence. A fixed positive linear marginal fraction satisfies this condition, so source323 genuinely strengthens source321C. Fixed powers k=floor(L^alpha) with alpha>1/2 and alpha<=1 also satisfy it. The separate source319A's collapse construction for alpha<1/2 has the same moment-budget framework; I read it for that comparison but do not issue a new full audit of its construction here.

The displayed bound alone does not tend to zero for k merely much larger than sqrt(L) if its squared ratio to L grows too slowly relative to ln L. In particular k comparable to sqrt(L) is not settled. Conversely, the sufficient condition is stronger than necessary for this numerical upper bound to decay: for a known sufficiently large fixed multiple of sqrt(L ln L), a fixed coefficient can already beat the square-root prefactor. The source calls its condition sufficient and does not claim necessity, so this is a scope observation rather than a flaw. No sharp square-root threshold, optimal logarithm, counterexample in the remaining window or uniform-in-rho result follows from this proof.

C12 — Attribution, novelty and programme scope: PASS with retained limits.

The homogeneous norm inequality and its strict deficit are credited to the primary authors; the candidate claims no original moment inequality. The quadratic expansion is an elementary consequence of their parameterization and is explicitly not advertised as independently novel. The targeted reading does not establish historical priority for the spectral application, and this audit makes no such claim. The note concerns arbitrary nonnegative densities on finite cubes, exact weighting-law marginals and fixed-noise transfer operators. It neither adds locality/physical hypotheses nor establishes a continuum or physical mass gap. It requires no uniform integrability, supercritical moment or positive floor beyond the stated assumptions; each estimate indeed uses only the critical norm bound, mean one, nonnegativity for the spectral factorization and exact Fourier cancellation. Grouping with319/321 in the322 manuscript remains the stated plan; no separate publication is authorized by this audit.

Residual findings and acceptance boundary

There are no candidate algebraic or functional-analytic blocking findings. The primary-source intermediate sign inconsistency is retained above and does not infect the independently checked expansion. The global constant remains existential; no numerical c_p was produced. The exact transition, logarithm necessity, priority and full external theorem proof remain outside this acceptance. Any change to the source, p/rho regime, B dependence, marginal interpretation, prefactor or degree cutoff requires renewed review. No old PDF rating transfers to this text, and this report creates no new score or reviewer-independence assertion.

Operational closure

Initial and final identities, raw source captures, prior source comparison, primary HTML, received assignment and actual context are bound by the packet manifest. The report and context disclose the earlier engineering involvement and shared filesystem. No inbound coordination, source mutation, numerical execution, runtime or publication occurred. Existing untracked files remain preserved. No worktree/clone was created. Required CI and unchanged-SHA integration remain separate parent gates; this source verdict is not a merge action. Evidence was staged in C and retained with raw hash verification under D:\Datos\the-eriksson-programme\autonomia\evidencia-323\source-audit323A. The manifest explicitly excludes only itself and its noncircular verification record.
