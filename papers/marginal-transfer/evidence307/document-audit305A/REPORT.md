# DOCUMENT305 source/document audit

Verdict: ACCEPT for the frozen source/document gates G1-G7. No blocking source/document objection was found. G8 is PENDING / NOT YET EXECUTABLE and is not accepted or waived. This is neither a PDF review nor publication clearance and assigns no grade.

## Binding and method

Candidate: 375047fac74dee4e464031f7e5b4d2368d5276fa.
Judges registration: 51cb36abe877336df1e87d047b4f6e43b028adc4.
The registration is an ancestor of the candidate and the registered judges305 bytes equal the candidate copy.
PR: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/252.
Capture: gh pr view 252 --repo lluiseriksson/THE-ERIKSSON-PROGRAMME --json body,headRefOid.
Body normalization: parse body; replace CRLF and CR with LF; remove terminal LF characters; append exactly one LF; encode UTF-8 without BOM.
Observed normalized body: 1157 bytes, SHA256 211e1681aa56a5a7461d6f4a5d73ee2b887cb8e5edb94f54041d0db7a09f1dfd.
Observed PR head equals the candidate.
manuscript305A.tex: 71339 raw bytes, SHA256 6a0606e994cedcf0107dc700edf2c9b9b762fa8ef4d31da8a958cf3501c0fa65.
SOURCE-INPUTS305.json raw SHA256: 1322fb6d1c05da3acbd2b898287a88ffbae044df9c8a22adb7e19c9886835f76.

All 271 SOURCE-INPUTS305 file entries passed expected raw byte count and SHA256, and their raw-byte Git blob identifiers matched the frozen tree. Exact captured subjects are retained under subjects/. This is identity checking, not 271 separate scientific audits. The inventory is not self-hashed; its own raw bytes are independently bound in this audit manifest. Files were not normalized for raw hashing. The textual proof comparison normalized line endings only, as explicitly recorded below.

This review uses analytical derivation and document reading. No local mathematical computation, proof-assistant run, test, TeX build, PDF generation, Colab runtime or external mutation was used. The auditor is the same involved separate Codex/OpenAI context retained across300-303, now exposed to historical299 assessment and its score. There is no provider/human independence claim.

## G1 — preserved proofs and translated300-302 results: ACCEPT

The full manuscript was read. The 14 original proof environments from manuscript299A at 6f9b27f59e3b105a872c773ed4d38d027536655b match the first14 proof environments in305 exactly after line-ending normalization. There are18 proof environments in305: four added integrated proofs. The original marginal/code, parity, density-budget, supercritical, subcritical and balanced/exact critical arguments have not been replaced with citations to their earlier acceptance. Their theorem restrictions and interpretation remain. The comparison diff is retained.

Finite-cutoff bound rederived: fix 0<rho<1 and s=(1+rho)/(1-rho)>1. Forward hypercontractivity with p=1+rho gives ||Q sqrt(w)h||_2^2 <= ||w||_s for unit h. With w=r 1_{r>K}, its square-root operator bound is tau^(1/(2s)), not tau^(1/s). The low part contributes K^(s-1) E r, so lambda1<=B_K=(K^(s-1)+tau)^(1/s). Mean-one r gives lambda1>=<r,P_rho r>>=1; sqrt(r) is a unit vector in probability L2. These normalizations are consistent.

For lambda2>=m^2, sign pieces of a second eigenvector have Q-image norms at least m, because A_plus=lambda2+(v/u)D and A_minus=lambda2+(u/v)D. Removing the high-density image costs at most t, hence leaves at least d=m-t=(1-t)/2. Low-part L2 norm is at most sqrt(K). Interpolation between a=1-rho and2 has theta=s^(-2): 1/(1+rho)=theta/(1-rho)+(1-theta)/2. This is ordinary Holder applied to powers even though a<1; no invalid quasi-norm triangle inequality is invoked. It yields low-part a-norm at least d^(s^2) K^(-(s^2-1)/2). Reverse hypercontractivity of nonnegative functions then gives D>=d^(2s^2) K^(1-s^2).

The sign compression eigenvalues are lambda2 and lambda2+D/(uv). Since uv<=1/2, lambda1-lambda2>=2D. Dividing by the upper bound on lambda1 gives exactly 2 d^(2s^2) K^(1-s^2)/B_K. In the complementary case lambda2<m^2, lambda1>=1 gives gap>1-m^2. Minimum of these cases is the stated positive constant. Positivity is valid on active support; support one is separately gap one. Repeated second eigenvalues do not invalidate the choice of a real orthogonal second eigenvector. Zero density entries cause no division by r.

For Theta<1, monotonic H(K) permits one finite K with H(K)<=tau<1 for the entire family. The constant depends on that K and tau; no constant depending only on Theta is promised. The weighted-psi sufficient condition is correctly described as a weighted moment, not an arbitrary Young function or Luxemburg norm. Supercritical control implies tail decay; critical boundedness alone does not.

The total-moment implication Theta<=B^s-1 uses X=r 1_{r<=K} on the full probability space, including its zeros, not a renormalized conditional law. E X>=1-B^s K^(1-s), Jensen gives E X^s>=(1-B^s K^(1-s))_+^s, and subtraction followed by K infinity proves the claimed estimate. It does not discard the mandatory unit baseline.

For r_L->1 in probability and E r_L^s->M, bounded F_K(r_L)=r_L^s 1_{r_L<=K}, K>1, has mean tending to1. This yields each fixed-cutoff tail limit M-1. To pass to Theta, the proof fixes K0, controls all sufficiently large L uniformly for every K>=K0 using total moment and low-part estimates, and then kills the finitely many remaining tails by a larger cutoff. Thus it does not exchange supremum and limit without justification. Exact299 gives M=2 and Theta=1; stable301 gives M=1+Theta0. The universal threshold is sufficient and sharp in the worst case, not a necessary condition for a stable family.

Stable example: with N=2^L, c=(M-1)^(1/s), the spike density denominator Z=1+cN^(1/s-1) normalizes the mean exactly. Its moment tends to1+c^s and its fixed K>1 escaped moment tends to c^s. In probability-normalized L2, e_z=sqrt(N)1_z has unit norm and multiplication by1_z is its rank-one projection. Consequently ||Q|e_z><e_z|Q||=((1+rho)/2)^L, with no missing N. The scaled spike norm decays as a_rho^L, where a_rho=(1+rho)/2^(2rho/(1+rho))<1 by strict convexity. Normalization contributes d_rho^L. The AA*/A*A correspondence preserves the whole finite spectrum and multiplicities. Min-max perturbs actual lambda1,lambda2 toward1,rho; lambda1>=1 controls the ratio. This proves limit gap1-rho and, after a finite prefix, uniform gap at least(1-rho)/2. Strict B>M^(1/s) is indispensable to the stated eventual norm repair and is retained. No exact equality at B=M^(1/s) is inferred.

## G2 — full303 fixed-cutoff endpoint: ACCEPT

The product tilt R_L is inherited from exact299 with E R_L^s=1 and every smaller positive moment vanishing. This gives m_L=E R_L->0 and R_L->0 in probability. Balanced coefficients beta_L->1 and Z_L->1 already give two leading eigenvalues tending to1. Renaming beta avoids confusing it with the new coefficient a_L.

For each fixed K>1, p_L=P(R_L>K-1)^(1/s) tends to0 by Markov at any fixed interior exponent. Set a=1-p, A=1-a m and q=A+aR. The coefficients are within[0,1], E q=1, A,a->1 and q->1 in probability. On E={q>K}, aR>K-A>=K-1, so E is contained in{R>K-1}, also when a=0 since the first event is empty. Minkowski gives ||q1_E||_s<=A P(E)^(1/s)+a||R1_E||_s<=p+a=1. This proves the cap for every dimension, without an asymptotic replacement.

The signed multiplier estimate ||QM_hQ||<=||h||_s follows from Holder against |Qf|^2 and the endpoint map L2 to L^(2s/(s-1)); that exponent equals1+1/rho. Thus ||QM_RQ||<=1. Comparing constant and R coefficients with the balanced family gives an operator norm error tending to0, and min-max transfers both leading eigenvalue limits. This is stronger than a top-Rayleigh-value statement and excludes a hidden second-eigenvalue gap in the argument.

For M_L=E q^s, the inequality (A+aR)^s>=A^s+a^s R^s gives liminf>=2. On R<=T the integrand tends to1 in probability and is bounded by(1+T)^s, hence its expectation tends to1. On R>T, q^s<=(1+1/T)^s R^s. First L infinity and then T infinity gives limsup<=2. T is an auxiliary cutoff and never changes the fixed requested K.

When M_L>2, epsilon=(M_L-2)/(M_L-1) lies in[0,1), tends to0, and mixing q with1 gives a moment at most2 by convexity. When M_L<=2, epsilon=0; no invalid division or negative coefficient occurs. On {v>K>1}, q>=v>K, so v^s1_{v>K}<=q^s1_{q>K}. Therefore the all-L fixed-K tail cap survives dilution. The Gram perturbation is epsilon(P_rho-S(q)), whose norm tends to0 since ||S(q)||->1, and both actual eigenvalues still tend to1. The retained two-sign estimate2 lambda2^s<=E v^s<=2 then also squeezes the moment to2.

Because v>=A->1, replacing a finite prefix by1 imposes any b<1 without changing limits, mean, total cap or K>1 tail cap. For every J>1 the J-tail tends to1. For J>=K the uniform cap is at most1; hence H(J)=1 and Theta=1 exactly as a supremum. Each finite matrix remains strictly Perron positive, so the claim is collapse only in the dimension limit. Total and tail caps are inequalities in each dimension, not equalities. Families depend on K and b. The proof does not settle K=1: the probability threshold K-1 then vanishes and p is identically1. This limitation is explicit.

## G3 — quantifiers, normalization and scope: ACCEPT

Fixed rho and finite Boolean uniform measure are stated. The gap is the normalized actual transfer eigenvalue gap. r times the base measure is not silently substituted for the Perron invariant law. The classical Doob L2 isometry does not identify higher norms uniformly across dimensions. Code/marginal families, tilted near-degenerate families and stable/fixed-tail examples remain distinct in the introduction and conclusions; they are not claimed to satisfy each other's properties.

The stable construction retains M>1, strict B>M^(1/s), any0<b<1 and finite-prefix repair. The fixed-cutoff construction retains every fixed K>1 separately, not one family proving the assertion at all K>1 simultaneously. Tail results add explicit hypotheses; they do not abolish all integrability control. No local interaction, fixed-range Hamiltonian, physical phase transition, continuum limit, optimal positive constant, external priority or inherited importance grade is asserted.

## G4 — comparison, roadmap and historical objections: ACCEPT

The roadmap separates the construction families and brings the exact moment and tail endpoints into view. The new Miclo paragraph identifies threshold2 as the fourth power of an L2-to-L4 Markov norm, not the raw density norm. Fresh primary reading of Miclo Section6/Proposition11 confirms this close precedent and its failure of a general quantitative extension. This is a real credit requirement, not cosmetic novelty distancing. Primary reference: https://perso.math.univ-toulouse.fr/miclo/files/2012/04/hyperboundedness.pdf .

The reverse-hypercontractive machinery is classical; MOS is credited. Wang's operator-tail functional is under an invariant Markov measure and is not simply this scalar density tail. Primary records: https://arxiv.org/abs/1108.1210 and https://arxiv.org/abs/1305.4460v6 . These distinctions do not prove external originality. This audit did not perform an exhaustive novelty clearance or newly verify every historical primary-source claim. In particular, the earlier299 review's inability to retrieve Aida Theorem10 remains in its untouched report; the manuscript's author-side targeted reading statement is not retroactively turned into an auditor-side verification.

All six historical299 assessment files are byte-identical to the private originals. All seven objections remain in the full report, with a separate seven-part author response. Their disposition:
O1: specific Miclo fourth-power comparison added; broader implication questions remain open.
O2: external priority unresolved, not cleared.
O3: global-weight/fixed convention limitation persists.
O4: the finite-cutoff constant is explicit, but optimal constants, floor cutoffs, endpoint rates and code tradeoffs remain unresolved.
O5: family separation now clearer; no combined-properties theorem inferred.
O6: roadmap improved; procedural access-history prose removed from scientific comparison while archived evidence remains.
O7: identity, reproduction, analytical review and independent/human/formal review remain distinct; no new PDF assessed.
These are retained qualifications and author responses, not deletion or certification that every historical concern has disappeared.

## G5 — complete public evidence and raw provenance: ACCEPT

All271 inventory bindings passed raw bytes, SHA256 and frozen Git blob identity. All58 included audit files match both PUBLIC-SUBSET305 and the original private audit files. All9 excluded entries match their private originals and are absent from the public package. The excluded entries are eight third-party PDF copies across prior audit directories and one unrelated D storage-index copy. Nothing in this review grants redistribution permission.

The four original manifests are themselves copied unchanged. Their17,15,17,14 original file entries respectively are all accounted for by either an included or excluded entry; no original manifest entry is silently dropped. The manifests themselves add the four copies outside their own self-excluded lists, explaining58+9=67 versus63 original file entries. Original exclusions and read-scope metadata remain visible.

All six historical299 files match their original outputs byte-for-byte, including the original output manifest. Source proof files300-303 retain their accepted identities; the package does not replace full reports with acceptance summaries. PACKAGE-CHECKS.json and BINDINGS271.json contain per-file evidence. Original public-subset inventories are retained under subjects/evidence305. The source-inputs inventory lists package identity, not proof of correctness.

## G6 — review disclosure and nontransfer of ratings: ACCEPT

The manuscript names OpenAI/Codex assistance and author involvement, distinguishes the separate involved auditor context, discloses retained300-303 context rather than four blind reviews, and does not assert known served backend settings. This review additionally discloses fresh exposure to the complete historical299 assessment and rating. It does not pretend ignorance of prior acceptance conclusions. The historical score remains tied to its exact original PDF and is neither inherited nor recomputed for305.

Owner administration of AIRR and the distinction between a working-paper deposit, editorial acceptance and human peer review are explicit. PACKAGE-BOUNDARY305 and PR body state that no305 PDF has yet been compiled, reproduced or assessed. Any future assessment must bind exact PDF bytes, full context and objections. No current model review is sold as human or provider-independent evidence.

## G7 — freeze, distinct review and document checks: ACCEPT

The captured PR head/body match the frozen assignment exactly. Judges registration precedes and is unchanged at the candidate. No incoming guidance was solicited or incorporated during this review. No source or body edits occurred. No numerical grade, runtime or other chat action occurred. The author's preliminary draft and earlier reasoning are disclosed, so preregistration is not represented as a blind pre-hypothesis experiment.

Static text checks found40 labels,49 ref/eqref uses, no duplicate labels and no missing referenced label;17 citation uses resolve to11 bibliography keys. These are source-key checks, not TeX execution, hyperlink availability certification, pagination or visual inspection. The uncompiled SourceCommit placeholder remains and must be bound during the separately required reproduction. A stale nonrendering comment saying source302 audit is required is conservative documentary residue, not a mathematical defect or publication clearance. It was not edited.

Required GitHub checks and unchanged normal merge remain separate. The predecessor order remains PR249, then PR250, before PR252. This audit neither merges them nor certifies CI completion. Initial untracked _drafts/ and _tmp/ were not touched; tracked source status stayed unchanged.

## G8 — execution, exact PDF and publication: PENDING / NOT YET EXECUTABLE

No accepted305 exact PDF exists in this review. Required future work remains: two fresh owned Colab clones at the accepted exact SHA; identical paired PDF output; complete visual inspection of that exact PDF; first exact-PDF assessment with complete report and context; actual supported permission/grant/receipt/licence and quota checks; publication only through the applicable flow; and anonymous public readback. This audit supplies none of those results and does not waive them.

The placeholder source commit and pending reproduction cannot be treated as a finished deliverable. Existing v4 publication proves nothing about305 readiness. ACCEPT here is deliberately restricted to G1-G7 source/document correctness and representation.

## Remaining objections and relevance

No blocking error was found in the scoped mathematical translations or evidence package. Nonblocking unresolved scientific issues remain: external originality, significance beyond this specialized model, optimal constants and rates, K=1, simultaneous-family extensions, locality/physical interpretation, and implications from stronger existing literature. The results are coherent refinements of the same sign/truncation and finite-dimensional Gram methods. They are not independent methods or a basis for a standalone small-paper/priority claim. This audit distinguishes plausibility and checked analytical correctness from originality and importance; it assigns no importance score.

Artifacts include literal assignment, retained-context disclosure, full report, raw subject snapshots, per-file package checks, static source comparison, normalized PR body and capture, and a raw-hash manifest. No excluded private PDF or storage-index file is copied into this305 evidence directory.
