# DOCUMENT307 analytical document audit

Decision: ACCEPT for D1-D5, restricted to the exact source and PR body below. No blocking mathematical or documentary objection was found. D6 is PENDING / NOT EXECUTED, not accepted and not waived. This is not a PDF review, publication clearance or numerical score.

## Exact referent and method

Candidate: 3edb8d656e511d3f81c147f54451fb57a84e5c38.
Judges307 registration: c738f316baf273152237132880344d7e59eb9e2b.
Base305: 375047fac74dee4e464031f7e5b4d2368d5276fa.
Source306: 476940ce788fb3e75cc8594e57af9fde226f7e83.
Source306 judges: 03ffe342d6db76476509ab93f5adeaedb769b629.
PR254: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/254.
Capture method: gh pr view 254 --repo lluiseriksson/THE-ERIKSSON-PROGRAMME --json body,headRefOid.
Normalization: JSON-decode body; CRLF/CR to LF; remove terminal LF; append exactly one LF; UTF-8 without BOM.
Observed normalized body:1209 bytes; SHA2564061d306c67f4272ca0390db1d80c78f39525f328cccb2d764e3ea699df07f21.
The PR head matches the candidate. The registered judges307 bytes match the candidate. Source306 copied into evidence307 matches the original source commit, not merely the parent's acceptance summary.

This auditor retains involved source300-303 and document305 context and exposure to the complete historical299 PDF assessment and rating. The different306 auditor's full report/context/assignment and actual proof were read. Same-provider/shared-filesystem constraints and unknown actual serving are disclosed. No provider/human independence is claimed.

## D1 — replacement proof and lower-cutoff corollary: ACCEPT

The exact305-to307 diff changes the abstract, the endpoint theorem and its proof, adds the lower-cutoff corollary, and updates evidence/model-context references. Of18 proof environments in305, the first17 are text-identical after line-ending normalization. The eighteenth is the replaced endpoint proof;307 has19 proof environments because of the new corollary. No prior code, marginal, parity, density-budget, supercritical/subcritical, exact-critical-budget, finite-tau, stable-spike or asymptotic-Theta proof is altered.

The actual new source306 proof and its full analytical report were read and rederived as follows.

1. Exact mean-relative product. The source299 tilt uses w_delta(x)=(1+delta x)/n(delta), R_L=product_i w_delta(x_i), and n(delta)^s=E(1+delta x)^s. Independence on uniform bits gives E R_L^s=1 and m_L=E R_L=n(delta_L)^(-L)>0. Thus R_L/m_L=product_i(1+delta_L x_i) exactly. Neither the balancing coefficient nor a further normalization enters this identity. The new manuscript explicitly derives it instead of deducing a moving-threshold event from R_L->0.

2. Fractional moment. Fix rho in(0,1), the associated s>1, sufficiently small fixed d in(0,1), and a fixed t in(0,1). For F_t(z)=log(((1+z)^t+(1-z)^t)/2), positivity of the bracket on[-d,d] makes F_t smooth there; evenness makes odd derivatives at zero vanish. Its value is0 and its second derivative is t(t-1). A finite constant sup_{|z|<=d}|F_t''''(z)|/24 controls the fourth-order remainder. At delta_L=d L^(-1/3),
 L F_t(delta_L)=t(t-1)d^2 L^(1/3)/2+O_{t,d}(d^4 L^(-1/3)).
The first term tends to minus infinity and the remainder to0, so E(R_L/m_L)^t->0. Markov at threshold1 proves P(R_L>m_L)<=E(R_L/m_L)^t->0. Parameters t and d are fixed before L; there is no unjustified uniformity near t=0,1 or rho=0,1. A mean-one likelihood ratio may have vanishing fractional moments because of rare large values; this is not a contradiction.

3. Coefficients and strict event. Jensen gives m_L<=||R_L||_s=1. With p=P(R>m)^(1/s), a=1-p, A=1-am, all coefficients lie in[0,1] and E q=1 for q=A+aR. The relative estimate gives a->1. Source299's interior moment at1 gives m->0, hence A->1; R->0 in probability gives q->1 in probability. Crucially q-1=a(R-m). If a>0, {q>1}={R>m}; if a=0, q=1 and the strict event is empty. Both cases give the necessary inclusion. Minkowski gives
 ||q1_{q>1}||_s <= A P(q>1)^(1/s)+a||R1_{q>1}||_s <= p+a=1.
Raising to s proves the all-L strict-tail cap at one. There is no division by a or p and no replacement of a strict event by a weak event at an atom. p=0 is harmless as well. Mean normalization is exact, not asymptotic.

4. Real spectral dependency. The source299 one-site H has matrix n^(-1)[[1,sqrt(rho)delta],[sqrt(rho)delta,rho]] in the uniform orthonormal Walsh basis. Its largest eigenvalue is
 kappa=(1+rho+sqrt((1-rho)^2+4rho delta^2))/(2n).
The quadratic term in log kappa cancels at s=(1+rho)/(1-rho), so log kappa=O(delta^4) and beta_L=kappa(delta_L)^(-L)->1. Also log m(delta)=-(s-1)delta^2/2+O(delta^4), and log tau(delta)=-rho delta^2/[2(1-rho^2)]+O(delta^4). Consequently the balanced normalizer Z_L=1+beta_L E R_L tends to1, while the full Gram cross-block norm sqrt(beta_L)tau(delta_L)^L tends to0. The diagonal Gram blocks each have top eigenvalue1; min-max gives actual first and second positive eigenvalues approaching1. Added Gram zeros do not substitute for the second eigenvalue, since the lower bound tends to1 and is eventually positive.

Endpoint forward hypercontractivity for Q=P_sqrt(rho) maps L2 to L^{1+1/rho}=L^{2s/(s-1)} with norm1. Holder gives ||QM_hQ||<=||h||_s for real h, so in particular ||QM_RQ||<=1. Comparing constant and R coefficients gives
 ||S(q)-S(w)|| <= |A-Z^(-1)|+|a-beta/Z| ->0.
For nonnegative v, X=M_sqrt(v)Q is square, S(v)=X*X and T_v=XX*. They are isospectral with all multiplicities, including zeros. Min-max therefore transfers both actual leading eigenvalues to T_q. No two-dimensional restricted eigenvalue is promoted to an equality for the full matrix.

The non-elementary forward endpoint was freshly checked against the primary MOS manuscript, Eq.(1.1) and tensorization on page1: https://arxiv.org/pdf/1108.1210v5 . The time is -log(sqrt(rho)); this gives both L^{1+rho}->L2 and L2->L^{1+1/rho}. The added306 step needs forward hypercontractivity; reverse hypercontractivity remains part of the unchanged finite-tau sufficient bound.

5. Critical moment and ordered truncation. Superadditivity gives E q^s>=A^s+a^s E R^s->2. For each fixed T>0, q^s1_{R<=T}->1 in probability and is bounded by(1+T)^s, so its expectation tends to1 even on varying probability spaces. This follows by splitting a small neighborhood of1 and bounding its probability-small complement. On R>T, q<=1+R<=(1+1/T)R, so that part contributes at most(1+1/T)^s. Taking limsup in L first, then T infinity, proves M_L=E q_L^s->2. T is only an auxiliary moment cutoff; no cutoff or family hypothesis is changed.

6. Exact total cap and event-preserving dilution. When M<=2, epsilon=0; only when M>2 use epsilon=(M-2)/(M-1). Then0<=epsilon<1 and epsilon_L->0. Convexity for v=(1-epsilon)q+epsilon gives E v^s<=(1-epsilon)M+epsilon<=2 and E v=1. The identity v-1=(1-epsilon)(q-1) preserves the strict event at1 exactly. On that event v<=q, proving the pointwise tail inequality and the all-L cap. This argument is specific to the endpoint one and is not silently used below it. The Gram perturbation epsilon(P_rho-S(q)) tends to0 because ||S(q)||->1; both leading eigenvalue limits persist. Thus the normalized gap tends to0.

The two-sign estimate2 lambda2(T_v)^s<=E v^s<=2 squeezes the critical moment to2. Its inherited proof handles active support, zeros and second-eigenvalue multiplicity correctly: both nonzero sign parts are tested separately using restricted endpoint Holder, and their regions are disjoint. The test vector sqrt(r) has unit probability-L2 norm, giving lambda1>=<r,P_rho r>>=1. No zero-uniform-mean assumption is imposed on a second eigenvector.

7. Floor, same family and Theta. Since both q and1 exceed A, v>=A->1. Choose a single finite prefix cutoff depending on rho,d,b, and replace its densities by1. These prefix terms have empty STRICT tail above1; all means, floors and caps hold in every dimension. There is no K in the construction. Therefore, simultaneously for every real K>=1 and every L,
 r_L^s1_{r_L>K}<=r_L^s1_{r_L>1}.
Each fixed J>1 has bounded low part with expectation tending to1. Subtracting from the total moment limit2 yields J-tail limit1. Its supremum H(J) is at least1 and the all-L cap at1 makes it at most1. Thus H(J)=1 for J>1 and Theta=1, without interchanging a supremum and a limit. It is important that the bounded-truncation argument uses J>1, where its cutoff function is continuous at the probability limit1. The proof does not apply that argument at J=1. Each finite matrix still has a positive Perron gap; only the uniform lower infimum collapses.

8. Fixed cutoffs below one. For0<=K<1, r^s1_{r<=K}<=K^(s-1)r, including K=0. Adding the assumed tail cap gives E r^s<=1+K^(s-1)<2. Hence
 gap(T_r)>=1-[(1+K^(s-1))/2]^(1/s)>0
by the two-sign bound and lambda1>=1. At K=0 Jensen actually forces r=1; the displayed bound need not be optimal and is not claimed optimal. It is uniform in dimension for fixed K and rho, not as K increases to1. The corollary does not claim a complete classification of all tail budgets below one.

## D2 — consistent exposition and remaining restrictions: ACCEPT

The abstract now states one collapsing family at cutoff one, simultaneous larger cutoffs, and the fixed K<1 positive consequence. The theorem and proof match those quantifiers. Current scientific exposition no longer says K=1 is unresolved or that a new family is needed for each K>=1. The retained305 and303 documents correctly keep those old limitations as historical facts; their proofs and reviews are not retroactively upgraded.

The construction families remain separate: marginal-preserving codes, balanced tilts and stable single-vertex spikes are not asserted to share all properties. Fixed rho, strict budget slack B>M^(1/s) in the stable example, uniform base versus Perron measure, global weights, and absence of locality/physical/continuum claims remain intact. The extra relative-mean calculation removes two specific construction restrictions; it does not remove every integrability condition or establish a general Markov theorem.

The positive finite-tail constant is still unoptimized. The unchanged sufficient theorem's title “Finite cutoff below one” refers to its tail budget tau<1 despite K>=1; with the new “Cutoffs below one” corollary this can be read ambiguously in isolation. The formulas and adjacent prose disambiguate it, so it is a nonblocking editorial observation, not a false theorem or gate failure. A later editorial revision could name the first theorem “Finite cutoff with tail budget below one”; no source was changed here.

## D3 — source and evidence preservation: ACCEPT

All588 SOURCE-INPUTS307 entries were checked by raw byte length/SHA256 and by recomputing the raw Git blob identifier against the frozen tree. SOURCE-INPUTS307 itself was independently bound as an additional archive member; it is not expected to self-hash. Complete per-member results are in BINDINGS588.json. Raw snapshots are retained in subjects.raw.zip; each member preserves its exact unnormalized bytes. Partial duplicate snapshots from the interrupted slower directory copy are separately hashed and not represented as the complete set.

PUBLIC-SUBSET307 entries were checked against both their declared hashes and the original D evidence files. Its excluded LEEME disk-byte copy is absent from the public package, matches the declared original identity, and is explicitly disclosed. Original306 and305 manifests remain byte-identical; their original entries are all accounted for by included or excluded paths. The prior305 nested inventories still disclose their own historical third-party PDFs and storage-index exclusions; nesting does not silently grant redistribution or imply those omitted files are bundled.

All271 prior305 inventory files remain byte-identical. This includes manuscript305, full historical299 assessment and author response, and prior source/report/context artifacts. The new package preserves the complete305 audit, including its G8 limitation and all raw bindings. The complete306 report, actual source, judges, context, assignment, manifest and primary-reading notes are present. Parent acceptance summaries are supporting metadata, not proof substitutes.

Hashes establish identity, not correctness, privacy permission or publication authorization. No third-party fulltext, credential, grant or private publication receipt was added by this audit. The legacy files outside the fresh reading scope were checked for identity, not represented as588 new independent scientific reviews.

## D4 — historical objections and review context: ACCEPT

The full historical299 assessment and all seven objections remain unchanged and exposed to this auditor. The separate author response remains unchanged. O1's Miclo fourth-power norm-budget precedent is credited; O2 external priority remains unresolved; O3 global/fixed-convention scope remains; O4 optimal constants/rates and other quantitative usability questions remain; O5 families are kept separate; O6 roadmap changes do not erase original critique; O7 hashes, reproduction, analytical review and human/provider-independent/formal review remain distinct.

The formerly unresolved K=1 limitation is now addressed by an additional proved argument in307, not by rewriting historical305 or303. No numerical rating transfers from299 or305.305 never had a PDF assessment or new score. A future assessment must be the first assessment of the exact307 PDF bytes and record full context/report and objections.

The manuscript discloses involved OpenAI/Codex assistance, retained300-303 context, and the separate fresh-assignment306 review without calling it technical isolation or independent-provider evidence. This report additionally discloses retained305 context and historical299 score exposure. The author-administered AIRR deposit is a working paper, not editorial acceptance or human peer review. Primary bibliography remains targeted rather than an exhaustive novelty clearance. The relative-mean fractional-moment method, hypercontractivity, Minkowski, convexity and min-max are classical mechanisms; no new method or external priority is certified.

## D5 — freeze, static document checks and integration separation: ACCEPT

The normalized1209-byte PR254 body has the assigned hash and the captured head is the exact source SHA. Judges307 are unchanged from registration. No inbound guidance was used during this review and no candidate/source/PR mutation occurred. The earlier preparatory argument and prior305 draft remain explicitly disclosed; preregistration is not described as blind to those inputs.

Static reference checking found41 labels,49 ref/eqref uses, no duplicate label, and no unresolved reference;17 citation uses resolve to11 bibliography entries. The proof comparison preserves17 old proofs and identifies only the intended eighteenth replacement plus new nineteenth proof. These checks are textual, not a TeX build or visual layout assurance. SourceCommit remains SOURCE-NOT-BUILT, correctly marking unfinished reproduction rather than a public-ready artifact. The inherited nonrendering source302-audit comment is stale but conservative and has no mathematical or publication effect.

Required repository CI and normal unchanged-SHA integration are separate. The stated dependency sequence is250 before253, and252 before254;250 was reported merged in the assignment. This audit neither rechecks merger completion nor merges anything. It does not authorize a changed rebased/squashed surrogate or bypass required engineering checks.

## D6 — runtime, PDF and publication: PENDING / NOT EXECUTED

No runtime was opened and no305 or307 PDF was produced, assessed or visually checked. After the accepted document and engineering gates, two fresh owned Colab clones must use the exact accepted SHA, produce matching PDF and full-page images, undergo complete visual inspection and a first exact-PDF assessment with complete report/context. Actual permission, quota, receipts, licences and anonymous public readback remain required. No item is waived by this source audit. Existing publication of older versions is irrelevant to307 readiness.

## Conclusion and unresolved scope

ACCEPT is limited to D1-D5 for this exact frozen source/body. The new mean-relative estimate, strict-tail event identity and unchanged full Gram comparison prove the endpoint and simultaneous-family improvement. No blocking defect was found.

Remaining nonblocking issues are external originality and importance, optimal positive constants and rates, varying-rho behavior, local/physical/continuum interpretation, and a general tail-budget classification below one. The theorem-title ambiguity is recorded above. This is one coherent amendment of the grouped manuscript, not grounds for a standalone small paper or multiplied review count. No score is assigned.

## Final identity checkpoint

All588 declared bindings passed, with SOURCE-INPUTS307 independently checked as the589th raw archive member. All589 members passed SHA256/length readback from the completed ZIP. All308 included public audit files matched their private originals. The one excluded LEEME file remains absent; all original manifest entries are accounted for. All271 prior305 bindings remain unchanged. The59 retained partial directory snapshots also match their corresponding complete archive members; they are redundant, not the authoritative complete set.

manuscript307A.tex: 73378 raw bytes; SHA256 527fb31fa134923db32e90d666c6cedd5824fc1d4b2bd143169ab4411f3bd9ae.
SOURCE-INPUTS307.json: 126054 raw bytes; SHA256 8676f51f2ee40b0402b677d4036f6bfeeb91ff29a4f6309fa67f64b493c088b6.
The only tracked marginal-transfer path outside its588-file inventory is SOURCE-INPUTS307.json itself, as expected for a non-self-hashing manifest. Judges307 ancestry, judges306 original-copy identity, unchanged governance files, unchanged tracked source, and final PR head/body were checked again. The final normalized body remains1209 bytes and SHA2564061d306c67f4272ca0390db1d80c78f39525f328cccb2d764e3ea699df07f21.
