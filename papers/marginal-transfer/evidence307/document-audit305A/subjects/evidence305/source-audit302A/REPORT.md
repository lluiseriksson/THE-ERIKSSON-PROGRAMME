# Analytical source audit302A — ACCEPT

Frozen candidate: `a41f341608012146dc5c4e5dc10bb02a90a3dd11`.
Registered judges: `868d80c81da95387198db3e3e860a769a42f2332`.
PR249: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/249
Capture method: `gh pr view 249 --repo lluiseriksson/THE-ERIKSSON-PROGRAMME --json body,headRefOid`.
Body normalization: parse JSON body; CRLF and CR to LF; strip all final LF; append one LF; UTF-8 without BOM.
Normalized body: **911 bytes**, SHA-256 **`1d37b92eff2c584ad4b0db89fac647e41bc9e5156b3893a5d63c236c3459a883`**.
Captured PR head equals the frozen candidate. The judges are its immediate parent and were not amended.

## Verdict, scope and review context

**ACCEPT** against G1–G6 for the stated finite-cutoff theorem, the sharp universal asymptotic threshold, both source-bound example families, and the total-budget comparison. No blocking mathematical defect was found. The constant in Theorem A is correct, including its powers of d and K and normalization by B_K. The limit/supremum issue is resolved by an explicit uniform-tail/finite-prefix argument, not by interchanging limits without justification.

Sharpness means that Theta<1 guarantees a positive uniform gap, whereas allowing Theta=1 in that universal guarantee fails. It does not mean that Theta>=1 forces a given family to collapse. Nor does it prove that the numerical positive-gap bound is optimal. The candidate's statement correctly keeps those distinctions.

This is a separate involved Codex/OpenAI analytical audit with the same context retained from audits300 and301. It is not a blind restart, independent-provider review, human peer review, formal proof or PDF grading. Both302 files were read in full. Sources299/300/301 and the operational rules were read in the retained context and verified unchanged; their precise roles are recorded below. No new mathematical question was opened, no subagent was spawned, and no inbound message arrived after the assignment before delivery.

No local mathematical execution, numerical or symbolic test, Lean, build, oracle, Colab runtime or score was used. Commands performed source and metadata reads, PR reads, byte captures/hashes and evidence writing only. No source, PR, service or repository state was mutated. Source301's required integration checks and the order PR248 before PR249 remain separate gates; this audit neither satisfies those checks nor authorizes bypassing that dependency.

## G1 — definition, monotone limit, uniform quantifiers and support: ACCEPT

For each fixed L, increasing K shrinks {r_L>K}; the critical moment on that set is nonnegative and nonincreasing. Supremum over L preserves this monotonicity. Thus H(K) decreases in the extended nonnegative reals and has limit inf_{K>=1} H(K), possibly infinity. Each individual moment is finite on its finite cube, but their supremum need not be finite; the definition correctly permits this.

If Theta<1, choose Theta<tau<1. The defining infimum implies there is a finite K>=1 with H(K)<tau, hence also H(K)<=tau. If every finite H(K) exceeded or equalled tau, its infimum could not be below tau. This works even if H initially takes the value infinity. K and tau are selected once for the entire family; no dimensionwise selection is hidden. Applying Theorem A with these same constants gives a positive lower gap simultaneously for every L.

This selection also supplies a uniform total moment bound K^(s-1)+tau; therefore a separate total-budget assumption is genuinely unnecessary for Theorem B, while a tail assumption remains. Theta=0 is the UI condition for the powers, since the change of cutoff from r>K to r^s>K^s is exact and s is fixed. No common coupling of the probability spaces is needed.

For support issues, E r=1 makes the active support nonempty. For 0<rho<1 the noise kernel is strictly entrywise positive and positive definite. Its congruence is positive semidefinite, vanishes off the support and has a strictly positive active block. Perron–Frobenius yields a simple top root and a strictly positive active Perron vector. Single-point support has only one positive eigenvalue, with the second counted as zero in the full matrix. The proposed gap is then one. Thus zeros and rank-one support are covered without a positive density floor assumption.

## G2 — independent derivation of the finite-cutoff bound: ACCEPT

Write p=1+rho, a=1-rho and s=p/(2-p). For unit h, Holder with conjugate exponents 2/(2-p) and 2/p gives

    E[w^(p/2)|h|^p]
      <= (E w^s)^((2-p)/2) (E|h|^2)^(p/2).

Raising to 2/p and applying forward hypercontractivity for Q=P_sqrt(rho) proves ||Q sqrt(w)h||2^2 <= (E w^s)^(1/s). With w=r1_{r>K}, the squared norm is at most tau^(1/s), so the norm is at most t=tau^(1/(2s)). Neither the s-th root nor the subsequent square root is missing.

For the top eigenvalue, the same bound gives lambda1<=||r||s. On the low set r^s<=K^(s-1)r, so E r^s<=K^(s-1)+tau, proving lambda1<=B_K. Testing T on its unit vector sqrt(r) gives <r,P_rho r>>=(E r)^2=1 from the nonnegative Walsh spectrum, hence lambda1>=1. All conventions are probability-normalized.

Because 0<=t<1, m=(1+t)/2 lies in [1/2,1) and d=(1-t)/2 is positive. If lambda2<m^2, nonnegativity and lambda1>=1 imply gap>1-m^2. Equality lambda2=m^2 belongs to the other case. In that case a real second eigenvector is supported on {r>0} and orthogonal to the positive Perron vector, so its positive and negative parts are both nonzero. Normalize those parts to h_+,h_-, and write h=u h_+-v h_- with u,v>0 and u^2+v^2=1. This remains valid for a repeated second eigenvalue and imposes no mean-zero condition under the base measure.

With D=<h_+,T h_->>0, pairing the eigenvalue equation with the two sign vectors gives A_+=lambda2+(v/u)D and A_-=lambda2+(u/v)D. Therefore each f=sqrt(r)h_sign has ||Qf||2>=sqrt(lambda2)>=m. Its high part is exactly sqrt(r1_{r>K})h_sign, so it obeys the unit-input estimate above. The ordinary L2 triangle inequality yields ||Qf_low||2>=m-t=d. Forward hypercontractivity gives ||f_low||p>=d, and E[r h_sign^2 1_{r<=K}]<=K gives ||f_low||2<=sqrt(K).

Solving 1/p=theta/a+(1-theta)/2 gives theta=(1-rho)^2/(1+rho)^2=1/s^2. The interpolation proof applies ordinary Holder to |g|^p=(|g|^a)^(theta p/a)(|g|^2)^((1-theta)p/2). Both Holder weights are positive, below one and sum to one, even though a<1. It never uses a false quasi-norm triangle inequality. The low parts are nonzero because their Lp norms are at least d>0; thus rearrangement is legitimate and gives

    ||f_low||a >= d^(1/theta) K^(-(1-theta)/(2theta)).

The reverse Boolean inequality is valid at the exact parameter rho=sqrt((1-a)(1-a)). For nonnegative functions with zeros, positive-epsilon approximation on the finite cube justifies its extension. Positivity of P allows discarding high parts before applying it to the two low parts. Their product gives

    D >= d^(2/theta) K^(-(1-theta)/theta)
      = d^(2s^2) K^(1-s^2).

The sign-basis compression has one eigenvalue lambda2 with vector (u,-v). The other, by its trace, is lambda2+D(v/u+u/v)=lambda2+D/(uv). It is larger and its Rayleigh value is at most the actual lambda1. Hence lambda1-lambda2>=D/(uv)>=2D since uv<=1/2. Dividing by lambda1 and using the upper bound B_K gives the second term in (2). This uses the full actual leading eigenvalues, not an assumed equality between compression and full spectra.

Combining the cases proves exactly min{1-m^2,2d^(2s^2)K^(1-s^2)/B_K}>0. At tau=0 the parameters are t=0,m=d=1/2 and the proof remains valid. At tau=1, outside the hypothesis, this proof gives d=0. That loss alone is not asserted to settle every possible finite-cutoff endpoint theorem; the proved sharpness below concerns Theta's asymptotic universal guarantee. No optimization of m or of the constant is claimed.

## G3 — the exact299 collapsing family and the order of limits: ACCEPT

The source299 dependency is the exact blob `650f87caf3fc972eb55350d6ef43b2fa12f1f094`, originally at `49705281f05ab18b71bd9ebc2da1985a0433340c:research/critical299/critical299A.txt`; the candidate tree contains the identical copied source. Its raw SHA-256 is `00a0c712f9b929e3fb669356585c30f08bfd7a5218ea9d4a24121e5b26e00b03`. Source300 is the exact `14f6c1afda58d925cdf1481ecb7791d0ade9395b` text retained and checked in audit300. These are unchanged analytical inputs, not inferred facts from a publication or score.

The family is the same balanced product tilt followed by the vanishing dilution enforcing ||r||s<=2^(1/s), plus the possible constant finite prefix supplying a prescribed floor 0<b<1. In the retained audit, the Gram eigenvalue estimates, transformed perturbation under dilution, normalization, moment limit and convergence in probability were checked against the source. The actual final family has gap->0, r_L->1 in probability and E r_L^s->2. Source300 proves its fixed-K tail limit one. Source302 adds a valid argument needed to turn that statement into Theta=1.

Here is the required argument without assuming a limit/supremum interchange. For any sequence in the stated setting with r_L->1 in probability and E r_L^s->M<infinity, fix K>1. The function F_K(x)=x^s1_{x<=K} is bounded and continuous at 1. Splitting into a sufficiently small neighborhood of 1 and its probability-small complement proves E F_K(r_L)->1. Continuity at K is not required; continuity at the limit point is. Thus each fixed-K tail moment tends to M-1, and H(K)>=M-1. This gives only the lower bound Theta>=M-1 by itself.

For the upper bound, fix epsilon>0 and one K0>1. There is L0 such that for all L>=L0, E r_L^s<=M+epsilon and E F_{K0}(r_L)>=1-epsilon. For every K>=K0, F_K>=F_{K0} pointwise, so the tail moment in every one of these dimensions is at most M-1+2epsilon. The finitely many dimensions below L0 each have a finite maximum density. Choose K also above their common finite maximum. Their tail moments then vanish. Therefore H(K)<=M-1+2epsilon for all sufficiently large K, with a cutoff allowed to depend on epsilon but not on L. Let epsilon decrease to zero. This proves Theta=M-1.

The finiteness of each cube and the finiteness of the prefix are essential to the last step and both are available. One does not first exchange a supremum and a limit and then invoke convergence in probability. Applying the valid identity to the actual299 family gives Theta=1, including its floor and prefix modifications. Thus a universal guarantee with Theta<=1 fails. Any proposed replacement condition Theta<c with c>1 would also include this family and fail. This establishes the exact asserted worst-case boundary.

## G4 — the exact301 stable family at every positive finite Theta: ACCEPT

The source301 used is exactly `6bc50cc52599b0df915895458002a3245e78e343:papers/marginal-transfer/ui-nonnecessity301A.txt`, blob `87fa4a42e545e1b88fe81cf025280cef8cf70b98`, raw SHA-256 `ff601419270947d5d3831455876e5163f39a93b04befac4e39b15d7186206741`. Its analytical audit is retained; this source is unchanged in302, while its operational integration checks remain separate.

For specified finite Theta0>0 put M=1+Theta0 and use exactly its one-vertex density (1+c N^(1/s)1_z)/(1+c N^(1/s-1)), c=(M-1)^(1/s). The prior audit rederived its exact rank-one norm, two strict geometric contractions, convergence of both actual leading eigenvalues, moment limit and finite prefix. The resulting r_L->1 in probability, E r_L^s->M, gap->1-rho, and gap>=(1-rho)/2 for every L. The norm constraint still requires any chosen B>M^(1/s), and the floor remains any chosen 0<b<1. No exact budget equality is imported.

The general identity proved in G3 therefore gives Theta=Theta0, rather than only an iterated fixed-K tail limit. The altered finite prefix cannot change Theta. In particular, choosing Theta0>=1 supplies stable families in the range where a collapsing family is possible. Choosing 0<Theta0<1 supplies non-UI families to which the new universal theorem applies. These facts distinguish a sharp worst-case guarantee from an if-and-only-if collapse criterion. The contrapositive of Theorem B says inf_L gap=0 implies Theta>=1; it does not assert convergence of every family's gaps to zero in that range.

## G5 — uniform total-budget comparison: ACCEPT

Let E r_L^s<=B^s for every L. Jensen and the mean-one condition force B>=1. On r_L>K, the inequality r_L<=K^(1-s)r_L^s gives E[r_L1_{r_L>K}]<=B^s K^(1-s), uniformly in L. Thus for X_L=r_L1_{r_L<=K}, its mean is at least (1-B^s K^(1-s))_+. Jensen on the full probability space, retaining the zeros of X_L, yields

    E[r_L^s1_{r_L<=K}] = E X_L^s
      >= (1-B^s K^(1-s))_+^s.

Subtract this from E r_L^s and take the supremum over L. The candidate's inequality H(K)<=B^s-(1-B^s K^(1-s))_+^s follows directly and is nonnegative. As K increases, s>1 makes the correction vanish and proves Theta<=B^s-1. There is no convergence-in-probability premise here, no unjustified conditioning on the truncated set, and no dimension-dependent error term.

For B<2^(1/s), the right side is below one, which recovers positivity by Theorem B. Source299 already supplies the explicit total-budget bound 1-B/2^(1/s) directly. This comparison does not improve that established total-budget estimate or establish a separate novelty claim. At B=1, Jensen forces constant densities, Theta=0 and actual gap 1-rho; nothing singular occurs. At or above the critical total budget, inequality (3) alone does not imply positive gaps, consistent with the source299 obstruction.

## G6 — actual weakening, primary sources, relevance and limitations: ACCEPT

The cutoff condition of300 used the convenient fixed budget 8^(-s). The new finite theorem permits every fixed tau<1. Its family consequence permits Theta in (0,1), while UI requires Theta=0. This is a real weakening, not a change of terminology: choose a stable301 example with 8^(-s)<Theta0<1. Since H(K)>=Theta0 for every K, it cannot satisfy300's original uniform cutoff budget, yet it satisfies the new theorem. The tail condition Theta<1 remains a substantive hypothesis. A bounded total critical moment alone remains insufficient, and no all-integrability-removal claim is accepted.

[Mossel–Oleszkiewicz–Sen, arXiv:1108.1210v5](https://arxiv.org/pdf/1108.1210v5), introduction equations (1.1)–(1.2) and tensorization, supplies the classical Boolean conventions. The reverse bilinear exponent a=1-rho lies at the correct equality parameter; it is not inferred from the weaker arbitrary-product version. This source supports classical inputs, not originality of302.

[Wang, arXiv:1305.4460v6](https://arxiv.org/pdf/1305.4460v6), introduction and Theorem1.1, concerns an invariant ergodic Markov operator and its operator-tail functional over unit L2 inputs. Theta here is a scalar density-power tail across varying base spaces. To compare via a Perron transform, the invariant measure becomes phi^2 times the base measure and the normalized Markov operator is phi^(-1)T(phi f)/lambda1. That transformation does not identify the two tail predicates. No quantitative bridge or contradiction of Wang is claimed.

[Miclo, Section6/Proposition11](https://perso.math.univ-toulouse.fr/miclo/files/2012/04/hyperboundedness.pdf) uses the fourth power of the L2-to-L4 operator norm for its threshold2. The candidate now states that power explicitly and does not conflate it with a raw density norm.

This is an elementary quantitative refinement and consolidation of the same sign-truncation mechanism, combined with already-audited examples and a classical concentration-of-moments argument. Mathematical correctness is accepted. External priority of the specialized combined boundary remains unresolved; a targeted comparison is not a novelty clearance. Retention within the existing manuscript, replacing the weaker presentation, is appropriate. No standalone-paper importance or numerical assessment is certified.

## Retained qualifications and negative cases

1. Sharpness is for the universal **asymptotic Theta threshold**, not optimality of the finite positive-gap formula or a classification of every individual family. This audit does not assert an additional finite-cutoff tau=1 endpoint theorem or its impossibility.
2. rho is fixed in (0,1). The constants need not remain positive uniformly as rho approaches an endpoint or as tau approaches one.
3. A cutoff K supplied by Theta<1 may depend on the family. The theorem gives a dimension-uniform bound for that family; it supplies no quantitative cutoff modulus from Theta alone.
4. The source301 total-budget slack and finite prefix remain; source299's collapsing family and source300's explicit escaped moment remain intact.
5. UI is sufficient and unnecessary. Theta<1 is sufficient and unnecessary for an individual stable family. Theta>=1 is necessary for infimum gap zero, not sufficient.
6. The total-budget comparison does not improve299 or establish novelty. No marginal-matching, local/fixed-range dynamics, physical gap, continuum or Yang–Mills consequence follows.
7. No grade, human/provider independence, formal certification or future-paper publication acceptance is implied. Required repository checks and PR248-before-PR249 integration order are not replaced by this source verdict.

No gate returned FAIL or INEXECUTABLE. No judge or candidate was revised in response to the reading. Acceptance binds the exact SHA/body stated at the top and cannot be transferred automatically to changed mathematical text.

## Evidence, privacy and cleanup

MANIFEST.json lists raw byte hashes, sizes, source identifiers and read coverage. Git objects were captured without text conversion. Existing operational instructions were read in the prior retained context and verified unchanged; full302 reads and primary targeted rereads belong to this audit. Retained source299/300/301 reads are explicitly distinguished from fresh reads.

The three files prefixed PRIVATE- are copies of primary PDFs retained from audit300 for private reference only. All are explicitly excluded from prospective public bundles in both the manifest and PRIVATE-SOURCES.md. Their retention/hash is not a redistribution authorization. No new PDF, paper or manuscript note was produced.

No disposable clone, worktree, runtime or service was opened. Existing untracked `_drafts/` and `_tmp/` were untouched. All newly retained evidence is in the requested D: directory; no audit-created clone cleanup is pending.
