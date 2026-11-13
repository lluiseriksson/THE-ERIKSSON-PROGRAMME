Hash context: resumed final audit of exact commit `49705281f05ab18b71bd9ebc2da1985a0433340c`; candidate Git-blob/LF and separately captured actual-checkout/LF SHA-256 `00a0c712f9b929e3fb669356585c30f08bfd7a5218ea9d4a24121e5b26e00b03`.

# Unit299 resumed final analytical source audit

**New resumed verdict: ACCEPT against unchanged G1-G7 at the exact candidate commit and captured PR244 body.** This verdict is issued after rereading the complete candidate and all judges and re-evaluating the proof analytically during the resumed assignment. No acceptance is inherited from the interrupted attempt.

The preceding attempt ended without a delivered verdict because of a usage-limit interruption reported in the resumption assignment. Its full-report.md, judge-table.md and final-state.json were drafted evidence only, despite their filenames and proposed verdict text. They remain byte-for-byte unchanged. The interruption is recorded separately in interruption-and-resumption.txt; no unavailable literal provider message is invented. All 27 entries of the earlier raw-hashmanifest.json were rechecked with zero mismatches.

The resumed read confirms the same source SHA, unchanged preregistered gate blob, same branch/head, same two PR files and identical normalized complete PR body. The current capture adds the files field to the earlier JSON command. Body normalization remains UTF-8 without BOM, LF line endings, trailing LF removed and one LF appended: 827 bytes, SHA-256 f37b8bedb5470dac5e7c4cfe7ba4d56b321e7d285c276c3570d1f13609c63e61. Exact source and PR identity were checked again before issuing this report.

The proof establishes B*=2^(1/s) as the exact dimension-free moment-budget threshold at fixed 0<rho<1 and s=(1+rho)/(1-rho). It supplies a sufficient positive uniform gap below B*, and collapsing admissible sequences at B* and above with every fixed floor b in (0,1). The positive gap formula is not asserted optimal. The support/sign proof, both endpoint Holder estimates, analytic coefficient/remainder scales, interior moment limits, global cross-term bound, two-sided dilution definition and finite-prefix floor completion were each reconsidered in the resumed audit; none fails. The complete reasons are retained below, not replaced by a prior acceptance label.

No quota was purchased, no model/provider/account or billing setting was changed, and no limit-bypassing action was taken. Only existing authorized tools and model access were used. This remains analytical source acceptance, not a PDF assessment, numerical score, formal proof, human/provider-independent review or novelty certificate. The auditor is the same involved Codex/OpenAI subagent with prior298 and interrupted299 context retained. Technical isolation and the exact served backend are unverified. The resumption instruction starts this new active audit period; no further substantive audit message arrived while it ran.

## Frozen identity and PR boundary

- Worktree: `C:\Trabajo\the-eriksson-programme\prefix-rank290-20261113`.
- Branch: `codex/tep-critical-budget299-20261113`.
- Candidate HEAD: `49705281f05ab18b71bd9ebc2da1985a0433340c`.
- Gate registration: `bed6289e75510ac633ca3255bd5c4708343ce784`.
- Gate Git blob at registration and target: `5569c515b2aa8261da1a3225235b83c2b9b9d603`.
- Gate raw Git-blob/LF SHA-256 and separately measured checkout raw SHA-256: `d27ac6e5dc2b813643104b6d38f1de44b8ac5b47de784a1b264dfc8bb54e13c1`, 3799 bytes each.
- Candidate Git blob: `650f87caf3fc972eb55350d6ef43b2fa12f1f094`, 11309 bytes in each separately captured representation.

PR: [244](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/244).
Independent capture method: `gh pr view 244 --repo lluiseriksson/THE-ERIKSSON-PROGRAMME --json body,headRefOid,url,title,files`; raw stdout retained, JSON body decoded in the resumed capture.
Normalization: UTF-8 without BOM; CRLF and lone CR converted to LF; trailing LF characters removed; exactly one LF appended.
Normalized full body: **827 bytes**, SHA-256 **`f37b8bedb5470dac5e7c4cfe7ba4d56b321e7d285c276c3570d1f13609c63e61`**.
Captured head: **`49705281f05ab18b71bd9ebc2da1985a0433340c`**.
Title: “Candidate exact critical moment-budget threshold for Boolean transfer gaps”.

A separate read-only PR file snapshot confirms exactly two added files: `research/critical299/critical299A.txt` and `research/critical299/judges299.txt`. Its base is `aa633eb11bd4969013b6ee1f74476663784a5b01`. No preceding unit298 source or manuscript is changed. The captured body accurately describes the candidate, preregistration, pending pre-verdict review and withheld claims. This report does not authorize a different future body or head automatically.

The gate explicitly acknowledges preparatory reasoning predating registration. Its registration is not misrepresented as blind discovery. Registration precedes the candidate commit and its blob is unchanged. No failed gate was amended.

## G1 — sign budgets, support and multiplicity: ACCEPT

T_r is positive semidefinite because it is a congruence of the positive definite Boolean noise operator. The support A={r>0} is nonempty by E r=1. Outside A the rows and columns vanish. Inside A all entries are positive, since 0<rho<1 makes every noise transition positive and both square-root weights are positive there. Perron-Frobenius therefore gives a simple positive top eigenvalue and an eigenvector strictly positive on A.

The proof first separates lambda2=0. This includes rank one, so it never divides by a missing sign-part norm. If lambda2>0, its eigenvector vanishes off A because those rows are zero. A real second eigenvector is orthogonal to the unique positive Perron vector, so it must have both a positive and a negative part. Repeated lambda2 causes no difficulty: every vector in its eigenspace remains orthogonal to the top eigenspace. Orthogonality is to the Perron vector, not to the constant function; no base-measure mean-zero or balanced-sign assumption is made.

For f=f_+-f_-, pairing with f_+ gives lambda2||f_+||_2^2=<f_+,T_r f_+>-<f_+,T_r f_->. The cross term is nonnegative, so the same-sign Rayleigh quotient is at least lambda2. Pairing with f_- gives the identical statement for that part after changing the sign of both sides. Each nonzero sign part is supported on its own disjoint region. Applying the restricted bound in G2 yields lambda2^s<=E[r^s 1_{f>0}] and lambda2^s<=E[r^s 1_{f<0}]. Adding gives the exact factor two. Mass on {f=0} is harmless unused budget.

Refutation attempts: zero weights, one-point support, a repeated second eigenvalue, an arbitrarily small sign-part norm, unequal sign-region probabilities and nonzero mass on the nodal zero set do not invalidate any step. The source handles all of them without additional assumptions.

## G2 — endpoint exponents and normalized Rayleigh bound: ACCEPT

Put p=1+rho. Then 1<p<2 and p/(2-p)=(1+rho)/(1-rho)=s. The standard Boolean endpoint condition for Q=P_sqrt(rho) from Lp to L2 is sqrt(rho)<=sqrt(p-1), with equality here. For h supported on C,

    <h,T_r h> = ||Q(sqrt(r)h)||_2^2 <= ||sqrt(r)h||_p^2.

Holder applied before the 2/p power has conjugate exponents 2/(2-p) and 2/p. Its r exponent is p/(2-p)=s; after raising, the r-moment power is (2-p)/p=1/s and the h factor is ||h||_2^2. Thus equation (1) is exactly correct with E[r^s 1_C], without a support-probability or counting-measure factor. All norms use uniform probability throughout.

The Rayleigh vector sqrt(r) has norm one because E r=1. Its quotient equals <r,P_rho r>, whose constant Walsh contribution is one and other contributions are nonnegative. Hence lambda1>=1. Combining with G1 gives lambda2/lambda1<=lambda2<=B/2^(1/s), and therefore the stated positive gap below B*. This uses the actual T_r, not a generator, a different probability law or a proxy eigenvalue.

The dual endpoint q=2s/(s-1) also satisfies q-1=1/rho and 1/s+2/q=1. It is exactly the sandwich estimate used later in G6. No strictness beyond the classical endpoint is needed.

## G3 — threshold meaning, B=1 and fixed parameters: ACCEPT

The positive conclusion is dimension independent for each fixed rho and B<B*. It does not identify the best possible positive gap. At B=1, strict Jensen forces r=1, whose actual gap is 1-rho. There is no contradiction with the weaker estimate: for example log(rho)<=rho-1 gives rho^s<=exp(-(1+rho))<1/2, hence rho<2^(-1/s). This is an analytic consistency check, not a numerical test.

The infimum in the classification is over the allowed sequence of finite cube dimensions and densities. The source does not assert a zero finite-dimensional gap. The subclass with r>=b remains nonempty below threshold because r=1 is admissible for every b<1 and B>=1. The same lower bound applies to it. The counterexample below supplies the converse for each fixed b<1. The exclusion b=1 is essential and correct, since mean one and r>=1 force equality everywhere.

All constants are allowed to depend on fixed rho,s and, for finite-prefix completion, b. No uniformity as rho tends to 0 or 1, or b tends to 1, is claimed. No rate at B* is inferred. The theorem therefore has the stated exact budget boundary without overclaiming an optimal positive-gap value.

## G4 — the balanced298 family and actual top eigenvalues: ACCEPT

The definitions agree with the immutable unit298 source at `2d1d27c4ba5f677e7f51092c6479735ba9ba59fa` and balanced-tilt Theorem 12 in manuscript commit `45d91a667750b295ce096fd495863583ba56eced`. Both historical inputs were frozen again. Unlike unit298's all-L triangle budget, the new proof does not impose B>2: it needs only a sufficiently small fixed positive d for the analytic neighborhood, then establishes its own exact limiting moment and dilution. There is no hidden reuse of the former B>2 restriction.

On one sign bit, M_w has Walsh matrix n^-1[[1,delta],[delta,1]]. Thus H=Q_1 M_w Q_1 has the stated entries and positive determinant rho(1-delta^2)/n^2. The quadratic formula gives the printed kappa. For K=Q_1 H^(1/2), KK*=Q_1 H Q_1=n^-1[[1,rho delta],[rho delta,rho^2]], so ||K||^2 is the printed tau^2. The order of the noncommuting square roots is correct.

All relevant expressions have positive analytic bases on a small fixed interval, and their logarithms are even real analytic there. Averaging the two powers gives log n=(s-1)delta^2/2+O(delta^4). The numerator coefficients for kappa and tau^2 are rho/(1-rho) and rho^2/(1-rho^2). Thus log kappa has zero quadratic coefficient at criticality, and log tau has coefficient -rho/[2(1-rho^2)]. Fourth derivatives are bounded on a smaller closed interval, so the O(delta^4) statements are uniform in L after delta_L=d L^(-1/3) is substituted.

Specifically, L delta_L^4=d^4 L^(-1/3) tends to zero while L delta_L^2=d^2 L^(1/3) tends to infinity. Therefore a_L=exp(-L log kappa_L) tends to one. Since log m=-log n and s-1>0, m_L^L tends to zero and Z_L=1+a_L m_L^L tends to one. The negative coefficient in log tau gives eta_L=sqrt(a_L)tau_L^L tending to zero.

The unnormalized S_L=P_rho+a_L H^(tensor L) is the exact sandwich operator multiplied by Z_L. Both summands have top eigenvalue one, by Markov normalization and exact balancing. In the rectangular Gram comparison, each diagonal block has top eigenvalue one; the self-adjoint cross-block perturbation has norm eta_L. Consequently lambda1(S_L)<=1+eta_L and lambda2(S_L)>=1-eta_L. Also lambda1(S_L)>=1 and lambda2<=lambda1, so both tend to one. There are N positive eigenvalues and N added zeros in the 2N-dimensional Gram matrix; the source's sufficiently-large-L positivity argument safely transfers its second eigenvalue. Nothing requires a statement about a negative lower estimate at small L.

Dividing by Z_L tending to one gives both eigenvalues of Q M_r Q tending to one. Square X*X and XX*, X=M_sqrt(r)Q, have identical complete spectra, including multiplicity and zeros; hence these are the actual transfer eigenvalue limits. The normalized gap tends to zero. This is stronger than merely showing a small unnormalized difference with an uncontrolled leading scale.

## G5 — exact limiting moment and scalar cross terms: ACCEPT

E w_delta^s=1 exactly by definition, hence E R_L^s=1 by product probability. For any fixed t in (0,s), positivity of 1+/-delta ensures that the real power and logarithm are even analytic near zero. Subtracting t log n from log E(1+delta x)^t yields coefficient t(t-s)/2, strictly negative. Thus

    log E R_L^t = [t(t-s)d^2/2] L^(1/3) + O(d^4 L^(-1/3)) -> -infinity.

This proves the moment limit for each fixed t. It neither exchanges a limit with an integral nor incorrectly assumes uniformity as t approaches an endpoint.

The choice theta=min(1,s/2) places both theta and s-theta strictly inside (0,s), for 1<s<2 as well as s>=2. For y in [0,1], the mean-value bound on (1+y)^s-1 is s2^(s-1)y, and subtracting y^s only decreases it. Since theta<=1, y<=y^theta. For y>=1, the identity F(y)=y^s F(1/y), F(y)=(1+y)^s-1-y^s, yields the bound s2^(s-1)y^(s-1)<=s2^(s-1)y^(s-theta). The lower bound F>=0 follows by differentiating in y. Equation (4), including y=0 and y=1, is therefore globally valid with the stated constant.

Substituting y=a_L R_L includes the amplitude powers a_L^theta and a_L^(s-theta); these remain bounded and tend to one. The interior moments vanish, so the cross contribution vanishes. The surviving terms are exactly 1+a_L^s tending to two. Division by Z_L^s tending to one gives E r_L^s tending to two and B_L tending to B*. A triangle estimate would only give a weaker result; the source correctly proves the moment identity instead.

There is no contradiction between interior moments vanishing and the s-moment staying one: this family has rare growing peaks, and no uniform integrability at exponent s was assumed. A near-one pointwise floor also does not forbid those peaks. These were explicit attempted counterarguments and do not refute the construction.

## G6 — equality, dilution and the prescribed floor: ACCEPT

Each raw r_L is nonconstant because d>0, delta_L>0, a_L>0 and the product sign tilt is nonconstant. Hence B_L>1. More importantly, in the only case where the quotient is used, B_L>B*>1, so its denominator is unconditionally nonzero. If B_L<=B*, epsilon_L=0. Otherwise epsilon_L=(B_L-B*)/(B_L-1) lies in (0,1). Since B_L tends to the fixed number B*>1, epsilon_L tends to zero regardless of which side is approached or whether it crosses repeatedly.

The convex mixture tilde r=(1-epsilon)r+epsilon preserves positivity and exact mean one. Minkowski gives ||tilde r||_s <=(1-epsilon)B_L+epsilon, equal to B* in the upper-norm branch and no larger than B* in the other branch. The inequality need not be equality in the actual norm; the theorem only requires the upper budget. Also Z_L>1 and both r_L and 1 are at least 1/Z_L, so the floor is preserved by mixing.

It is crucial that the perturbation is estimated in Q M_r Q. Holder and the dual endpoint exponents give ||Q M_h Q||<=||h||_s for signed h, using arbitrary real unit test vectors. Therefore its difference for the diluted and raw densities is bounded by epsilon_L||1-r_L||_s<=epsilon_L(1+B_L), which tends to zero. No pointwise cap and no unproved continuity estimate for square-root multiplication are needed. Weyl applies within each finite-dimensional space with a norm bound tending to zero, even though the dimensions grow. Both leading actual transfer eigenvalues consequently still tend to one via the exact square Gram identity, and the gap tends to zero.

For fixed b in (0,1), Z_L tending to one yields one finite L0 such that 1/Z_L>=b for every L>=L0; this is an eventual bound, not a subsequence claim. Setting the density equal to one before L0 gives every required constraint for all integer L>=1 and preserves the limiting gap. The finite-prefix replacement is explicitly allowed by the unchanged gate. Every resulting finite matrix is strictly entrywise positive, so its gap is strictly positive. The zero infimum is approached across dimensions, not attained at a finite dimension. The same sequence is admissible for all B>=B*.

## G7 — history, primary precedent and scope: ACCEPT

The two-file change leaves unit298's partial theorem, source manuscript and assessment history intact. No new or inherited PDF grade is assigned here. The candidate's historical score references are not independently regraded or certified by this source audit. The PR and source distinguish exact budget threshold from optimal positive-gap value, omit a boundary rate, and make no local-Gibbs, marginal-matching, physical mass-gap or continuum claim. Other project-status remarks are outside this audit and are not newly certified.

The targeted reading now directly accesses [Aida's 2001 primary preprint](https://www.ms.u-tokyo.ac.jp/~aida/paper/preprint/handai3.pdf); its additive/derivation-based hypotheses were not identified with this transfer operator. [Biskup-Koenig, Lemma 4.5 and equation (4.29)](https://www.wias-berlin.de/people/koenig/www/PPP4PAM-CMP-final.pdf) provide a particularly close classical sign-region and split-budget precedent. See the short retained reading notes for exact scope. Neither comparison establishes priority for the present exact formulation or boundary family. The general sign-splitting mechanism must remain attributed as classical; citation of the close precedent is appropriate in future manuscript integration.

## All objections, limits and disposition

**No blocking objection remains.** The following nonblocking presentation ambiguity is preserved: the explanatory sentence after equation (3) should explicitly write its coefficient as

    (1/2)[rho^2/(1-rho^2) - (s-1)/2]
       = -rho/[2(1-rho^2)].

The displayed equation (3) already has the correct coefficient, and direct expansion verifies it. The current prose's unbracketed “one half of ... = ...” can momentarily make the inner expression and final coefficient unclear; this is not a failed gate or a change required to make the mathematics true.

The exact threshold is proved for fixed parameters and unrestricted-dimensional uniform Boolean cubes. The source does not establish uniform results as rho or b approaches an excluded endpoint, rates after dilution, or an optimal positive-gap formula. Novelty and importance are separate unresolved questions. No broad search absence is treated as evidence of originality.

All seven gates were evaluated without mathematical computation, builds, tests, Lean, an external runtime or source edits. The complete source and gates were read; no substantive inbound audit message arrived during either active audit period after its initiating assignment, no other chat was contacted, and no child agent was used. Only this new evidence directory was written. No disposable clone was created and no cleanup is pending.

Evidence is retained under `D:\Datos\the-eriksson-programme\autonomia\evidencia-299\source-audit299A`: exact assignment, context/read scope, judge table, short primary-source notes, separate raw Git/checkout subjects, raw PR snapshots, normalized complete body, input-manifest-resumed-final.json and raw-hashmanifest-resumed-final.json. Earlier partial artifacts remain separately preserved. Remote third-party full texts are not redistributed. The verdict binds only the exact source SHA and normalized PR body identified above.
