# Separate analytical source audit303A — ACCEPT

Frozen source: `9bc257640fc98ea9dd88317238fbdf0cbec79c95`.
Judges registration: `add50ba426e1fc8746d14c232d387cd5f0e5ae84`.
PR250: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/250
Capture method: `gh pr view 250 --repo lluiseriksson/THE-ERIKSSON-PROGRAMME --json body,headRefOid`.
Normalization: parse JSON body; replace CRLF/CR with LF; remove all terminal LF; append one LF; UTF-8 without BOM.
Normalized body: **841 bytes**, SHA-256 **`ed46bd015ff28cf2fbb22abca8dc31025dc3e9d51935a1e9ea430eb1d40a9f88`**.
The captured head is the frozen source. The judges are its immediate parent and were not changed by the candidate.

## Verdict and review boundary

**ACCEPT** against all six gates. For every fixed 0<rho<1, K>1 and 0<b<1, the construction satisfies mean one, floor b, critical moment at most two and critical K-tail moment at most one in every dimension. Its actual first and second transfer eigenvalues both tend to one, its normalized gap tends to zero, and its asymptotic escaped critical moment is exactly one. The fixed-cutoff endpoint obstruction now proved was expressly left separate in302; this is not a retrospective claim that302 had already proved it.

The all-dimension assertions are inequalities, not claims of moment equality in every finite dimension. The two moment limits are established separately. K is fixed before the family is constructed and never changed to enforce a constraint. The auxiliary T in the proof of moment convergence is a separate analytical truncation parameter, not a changing hypothesis cutoff.

The auditor is the same separate involved Codex/OpenAI context used for audits300–302, explicitly retained. This is not a blind restart, independent-provider or human review, formal verification, numerical experiment or PDF assessment. No grade is supplied. Both303 files were read in full, prior load-bearing sources and operational rules are unchanged, and the six arguments were rederived analytically. No inbound message arrived after the assignment before verdict; no subagent was spawned.

No local mathematical calculation, numerical/symbolic script, test, build, Lean, oracle or runtime was executed. Commands were confined to reading sources/primary references, git and PR metadata, raw captures, byte hashes and writing this evidence. No branch, source file, PR body, service or other chat was modified. Required repository checks and integration of PR249 before PR250 remain separate from analytical acceptance; no merge was performed.

## G1 — source299 inputs, exact normalization and convergence: ACCEPT

The load-bearing source is `49705281f05ab18b71bd9ebc2da1985a0433340c:research/critical299/critical299A.txt`, raw SHA-256 `00a0c712f9b929e3fb669356585c30f08bfd7a5218ea9d4a24121e5b26e00b03`, Git blob `650f87caf3fc972eb55350d6ef43b2fa12f1f094`. The candidate's copied source299 has that identical blob. It was read and checked in the retained audit300 context. The input is its actual undiluted product-tilt R_L and balanced family, not its later diluted density or a similarly named hypothetical random variable.

The exact product normalization gives E R_L^s=1 and R_L>0. The one-site expansion in299 has log E w_delta^t=t(t-s)delta^2/2+O(delta^4), for fixed 0<t<s. With delta_L=dL^(-1/3), its negative quadratic term dominates the vanishing aggregate fourth-order remainder, proving E R_L^t->0. In particular t=1 is permitted since s>1, so m_L=E R_L->0. Jensen also gives m_L<=(E R_L^s)^(1/s)=1 in every dimension. Finite prefix choices R_L=1 retain these exact bounds and all asymptotic statements.

The balanced coefficient beta_L in303 is the coefficient called a_L=kappa(delta_L)^(-L) in299, not the new coefficient a_L=1-p_L in303. The source proves beta_L->1, Z_L=1+beta_L m_L->1 and both actual leading transfer eigenvalues of w_L=(1+beta_L R_L)/Z_L tending to one through its Gram comparison. This distinction of coefficients prevents substitution of the new unbalanced coefficient into the old spectral theorem. Those source results were analytically checked previously; no score or publication status is used as their proof.

Now p_L=P(R_L>K-1)^(1/s) lies in [0,1] and a_L=1-p_L lies in [0,1]. Hence A_L=1-a_L m_L lies in [0,1]. The mean identity E q_L=A_L+a_L m_L=1 is exact, and q_L=A_L+a_L R_L is nonnegative. No inverse factor or missing probability mass occurs.

Since K-1 is a fixed positive number, Markov's inequality with any fixed 0<t<s gives P(R_L>K-1)<=E R_L^t/(K-1)^t->0. Consequently p_L->0, a_L->1 and A_L->1. The same moment argument at any fixed positive threshold gives R_L->0 in probability. As a_L is bounded, q_L=A_L+a_L R_L->1 in probability on the varying cube measures. This proves the asserted convergence; it is not assumed from mean normalization. The lower bound q_L>=A_L supplies every fixed floor b<1 eventually.

## G2 — all-L tail bound and coefficient endpoints: ACCEPT

On the event q_L>K, one has a_L R_L>K-A_L>=K-1. Since 0<=a_L<=1 and R_L>=0, this implies R_L>K-1. This implication requires no division by a_L, so it also handles a_L=0 without a singular step.

Let E_L={q_L>K}. Minkowski in the genuine Ls norm, s>1, gives

    ||q_L1_E_L||s
      <= A_L P(E_L)^(1/s) + a_L ||R_L1_E_L||s
      <= p_L + a_L = 1.

Here event inclusion bounds P(E_L)^(1/s) by p_L, A_L<=1 bounds its coefficient, and the exact normalization ||R_L||s=1 bounds the other summand. All expectations are under the uniform probability measure; the first term is the probability to the 1/s power, not a counting cardinality. Raising the final inequality to the positive power s proves the exact moment bound at the original fixed K for every L.

If a_L=0, then p_L=1 and q_L=1, so its K-tail is empty. If p_L=0, event inclusion gives an empty tail. Both cases satisfy the inequality directly, irrespective of whether they occur in a chosen finite prefix. No quasi-norm inequality is used; s>1 is essential and available. This is an all-dimension estimate, not an asymptotic estimate repaired by choosing larger cutoffs.

## G3 — full eigenvalue comparison and two-sided moment limit: ACCEPT

For the signed multiplier estimate, let q*=2s/(s-1)=1+1/rho. Forward hypercontractivity for Q=P_sqrt(rho) sends L2 to Lq* with norm at most one at the endpoint. Holder with 1/s+2/q*=1 gives, for unit u,v,

    |<u,Q M_h Q v>| <= ||h||s ||Qu||q* ||Qv||q* <= ||h||s.

Thus ||Q M_h Q||<=||h||s, including signed h. In particular, the exact critical normalization gives ||Q M_R_L Q||<=1. This bounds the whole operator uniformly in L, not only a matrix entry.

The transformed operators are exactly S(q_L)=A_L P_rho+a_L Q M_R_L Q and S(w_L)=Z_L^(-1)P_rho+(beta_L/Z_L)Q M_R_L Q. Subtraction followed by the operator norm triangle inequality gives the displayed error bound |A_L-Z_L^(-1)|+|a_L-beta_L/Z_L|. Both coefficients tend to zero, because the respective coefficients tend to one. The uniformly bounded multiplier factor prevents dimension growth from invalidating the comparison.

For a nonnegative density v, take X=M_sqrt(v)Q. Its square matrices XX*=T_v and X*X=S(v) have identical spectra, including zeros and multiplicities. The min-max perturbation estimate applies to every ordered eigenvalue of S within each fixed cube. It transfers both source limits lambda1(S(w_L)),lambda2(S(w_L))->1 to S(q_L), and isospectrality transfers both to the actual T_q. Hence the normalized gap tends to zero with a denominator tending to one. No restricted-space Rayleigh estimate is promoted to a claim about the true second eigenvalue.

The moment limit is independently justified from both sides. For x,y>=0 and s>1, (x+y)^s>=x^s+y^s; hence E q_L^s>=A_L^s+a_L^s E R_L^s=A_L^s+a_L^s->2.

For the upper bound fix any T>0. Since R_L->0 in probability, P(R_L>T)->0. The variables Y_L=q_L^s1_{R_L<=T} converge in probability to one and lie between zero and (1+T)^s. Their expectations therefore tend to one: for any eta>0, split E|Y_L-1| over |Y_L-1|<=eta and its complement and bound the latter by a fixed constant times its probability. This argument is valid across different probability spaces and does not invoke an unjustified shared-space dominated-convergence theorem.

On R_L>T, q_L<=1+R_L and (1+R_L)^s<=(1+1/T)^s R_L^s. Thus that part's expectation is at most (1+1/T)^s. For every fixed T, limsup E q_L^s<=1+(1+1/T)^s. Let T increase to infinity after the limsup to obtain the upper bound two. Together with the lower bound this proves E q_L^s->2. The auxiliary T was never used to change K or select the final density.

## G4 — exact total cap and tail-monotone dilution: ACCEPT

Write M_L=E q_L^s>=1 by Jensen. The candidate divides by M_L-1 only on the branch M_L>2. There the denominator exceeds one, the numerator is positive and smaller than the denominator, and epsilon_L=(M_L-2)/(M_L-1) lies in (0,1). Otherwise epsilon_L=0. Since M_L->2, epsilon_L->0 in both branches. No definition fails when q_L is constant and M_L=1.

The mixture v_L=(1-epsilon_L)q_L+epsilon_L is nonnegative with mean one. Convexity of the scalar power function yields E v_L^s<=(1-epsilon_L)M_L+epsilon_L. This equals two on the branch M_L>2, and is at most two on the other branch. The expectation itself need not equal the convex upper bound. The claimed exact norm budget is consequently the exact cap ||v_L||s<=2^(1/s), not finite-dimensional equality.

Tail monotonicity is pointwise at the same fixed K>1. If v_L>K, then q_L>1, since a mixture of q_L<=1 and one cannot exceed one. For q_L>1, moving toward one decreases the value, so v_L<=q_L and necessarily q_L>K. It follows that v_L^s1_{v_L>K}<=q_L^s1_{q_L>K} everywhere. Combining this with G2 preserves the exact K-tail bound for every L. At epsilon=0 the inequality is equality; epsilon=1 never occurs. This reasoning does not claim monotonicity for arbitrary thresholds below one.

Linearity of S in the density gives S(v_L)-S(q_L)=epsilon_L(P_rho-S(q_L)). Its norm is at most epsilon_L(1+||S(q_L)||), which tends to zero because G3 proves ||S(q_L)||=lambda1(T_q)->1. The same full-spectrum perturbation and isospectrality arguments preserve both leading eigenvalue limits and gap collapse. Also v_L-1=(1-epsilon_L)(q_L-1), which directly preserves convergence in probability to one.

For the final moment limit, source299's universal sign-region estimate gives 2lambda2(T_v)^s<=E v_L^s<=2. Its proof applies to all nonnegative mean-one densities: endpoint Holder bounds each disjoint sign region's Rayleigh quotient by its s-moment, and the positive cross term gives one copy of lambda2^s on each region. Zero second eigenvalue is harmless; otherwise positive Perron support provides both signs. Thus the estimate applies to the current v_L, not merely the original299 family. Since lambda2(T_v)->1, squeezing proves E v_L^s->2. No unsupported assertion that mixing preserves high moments is needed.

## G5 — floor, fixed prefix, Theta and endpoint meaning: ACCEPT

Both q_L and the constant one are at least A_L, so their convex mixture v_L is at least A_L. Because A_L->1, one finite L0 makes A_L>=b for all L>=L0. Set r_L=1 for smaller L and retain v_L after that index. Each prefix member has mean one, floor one, critical moment one and an empty tail above the originally specified K>1. Thus every requested constraint holds for every L. All limits from G3–G4 survive a finite prefix change. Final densities are strictly positive, so individual finite-dimensional gaps are positive even though their limit and infimum are zero.

The source302 identity applies: r_L->1 in probability and E r_L^s->2 give Theta=1, with its finite-prefix argument justifying the supremum-before-cutoff order. There is also a direct consistency check here that uses the new stronger bound. For each fixed J>1 the bounded truncation r^s1_{r<=J} has expectation tending to one, so the J-tail tends to one and H(J)>=1. Conversely H(K)<=1 by the all-L fixed-K estimate, and H is decreasing. Hence for every J>=K, H(J)=1 and in particular Theta=1. No exchange of limits and suprema is used.

This genuinely adds what302 did not establish: for every chosen K>1 there is a collapsing family satisfying the finite-cutoff budget tau=1 in every dimension, even with total cap two and prescribed floor. Therefore302's finite-cutoff universal positive-gap theorem cannot be extended to include tau=1 for these K. It does not establish an optimal positive constant when tau<1.

K=1 is a distinct excluded case. In the displayed construction R_L>0 implies P(R_L>K-1)=1 there, so p_L=1 and a_L=0, destroying the intended spectral channel rather than yielding the needed limits. The Markov argument in G1 also required K-1>0. Thus the proof cannot be extended to that cutoff by substitution or a limit in K, and no such extension is certified.

## G6 — provenance, classical inputs and relevance: ACCEPT

[Mossel–Oleszkiewicz–Sen, On Reverse Hypercontractivity, arXiv:1108.1210v5](https://arxiv.org/pdf/1108.1210v5), introduction equation (1.1) and tensorization, supports the classical forward Boolean endpoint used in G3. Its parameter conversion to q*=1+1/rho was checked above. The product-family spectrum and universal sign-region bound are explicit dependencies on the exact source299, while the Theta identity is an explicit dependency on the exact source302. Their retained readings and matching raw hashes are disclosed; prior scores and verdict labels are not mathematical substitutes.

The event inclusion, Minkowski estimate, coefficient normalization, bounded-part/large-R moment split and convex dilution are elementary. The construction directly resolves the specified fixed-cutoff obstruction within this programme. This source audit establishes neither an external priority claim nor a new general theorem beyond those stated hypotheses. It is suitable as a grouped extension of300–302, not evidence for a separate small-paper deposit or a higher importance rating. No broad novelty search was performed and no novelty is inferred from that absence.

All moments here use the base uniform measure. The argument does not identify it with a Perron invariant measure or invoke an operator-tail equivalence in another measure. It gives no matching-marginal, local/fixed-range, heat-bath, physical gap or continuum/Yang–Mills statement. Provider/human independence, formal verification and numerical assessment are not claimed.

## Qualifications and negative cases retained

1. K>1 and fixed rho in (0,1) are essential stated restrictions; K=1 and endpoint-uniform rho results remain unaddressed.
2. A separate family is constructed for each fixed K and floor b. No single family for every K>1 simultaneously is claimed.
3. The total budget is the exact inequality E r_L^s<=2, with equality only asserted in the limit. The tail cap is likewise an inequality for each L.
4. The ordinary positivity of each finite gap is compatible with gap collapse; no exactly zero finite-dimensional Perron gap is claimed.
5. This resolves the fixed-cutoff endpoint left open in302 without changing that earlier source, its limitations or its audit. The positive tau<1 result, stable301 counterexamples and negative299 examples are all preserved.
6. No optimum below the endpoint, external originality, standalone-paper value, new score or independent/human validation is established.
7. Repository checks and the required integration of predecessor PR249 before PR250 are not replaced by this ACCEPT. The assignment's predecessor integration status is coordination context, not a newly performed CI or merge audit.

No registered gate failed or was amended, and no mathematical repair was requested or made. ACCEPT binds only the frozen source and normalized body identified above.

## Evidence, private sources and cleanup

MANIFEST.json identifies the raw subjects, exact byte representations, sizes, SHA-256 digests and read coverage. Git files were captured as raw blobs without newline conversion. Operational instructions and sources299/302 were read in the retained context and verified unchanged;303 was fully read in this audit. The primary hypercontractivity passage was checked again through the primary web PDF.

PRIVATE-MOS-1108.1210v5.pdf is a private reference copy reused from evidence300, explicitly excluded from every prospective public bundle in the manifest and PRIVATE-SOURCES.md. No redistribution permission is implied by retaining its hash. No new PDF or manuscript note was created.

No disposable clone, worktree, runtime or service was created. Existing untracked `_drafts/` and `_tmp/` were left untouched. All new audit evidence is retained on D: and no audit-created clone cleanup is pending.
