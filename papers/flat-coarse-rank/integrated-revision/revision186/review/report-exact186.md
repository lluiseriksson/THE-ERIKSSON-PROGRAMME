# Exact-PDF scientific model assessment: grouped supplement 186

## Artifact, decision and numerical assessment

Reviewed work: *Rectangular mean observations with critical inverse moments*, Lluis Eriksson, 7 November 2026, grouped supplement for the existing paper dossier. This report concerns exactly the eight-page PDF at `D:\Entregas\the-eriksson-programme\2026-11-07_rectangular-consolidation186\rectangular_observations.pdf`, 321889 bytes, SHA256 `040cae56bad1deb48605ea72f7d4e9ee28da00de702b5ebb11c039129fe65146`.

**Recommendation: minor_revision. Overall Millennium-scale assessment: 4.40/10. Rounded overall display: 4/10 stars, Strong.** This is the single first full assessment of this exact supplement. It is not a revision, conversion or repetition of a numerical assessment of v8 or of the source185 audit. The score is a research-position judgment on the supplied high-ceiling scale, not a probability of correctness or an arithmetic average of criterion ratings.

The supplement gives a clear, technically serious positive construction for arbitrary one-coordinate laminates and a complementary, quantitatively sharp asymptotic cost theorem for a particular strong Green certificate on homogeneous data. Its finite results are mathematically useful and unusually explicit about scope. They do not settle the unrestricted rectangular problem. Much of the machinery is classical, the specific priority claims remain unverified, and there is no independent proof reproduction or formal certificate. Those limits support the Strong classification, rather than a field-shaping or Millennium interpretation.

| Criterion | Stars | Basis |
|---|---:|---|
| Correctness confidence | 4/5 | Both principal theorems and the explicit examples withstand analytic checking of constants, quantifiers, edge conventions and endpoint orders. A finite-example convention needs explicit clarification. No independently executed or formal verification was performed. |
| Rigor and completeness | 4/5 | Actual energy inequalities, a constructive partition, odd-size tree charging, arbitrary-aspect endpoint lower bounds and matching meshes are supplied. The exact finite example and evidence citation could be more explicit. |
| Novelty relative to sources checked | 3/5 | The finite laminate adapter and all-partition certificate-cost statement are plausible specialized contributions. Core methods are classical; targeted primary-source comparison does not establish priority. |
| Significance if correct | 3/5 | These results enlarge a positive subclass and exclude a specific overly strong certification route. They help the stated finite programme, but neither the general variable-coefficient construction nor interacting/continuum results follow. |
| Reproducibility / independent inspectability | 3/5 | Displayed proofs are inspectable, all eight rendered pages and the full extracted text were read, and 48 manifest entries matched. The reported finite executions and repository evidence were not independently replayed or comprehensively audited. |

No unresolved objection demonstrated to invalidate Theorem 2.1 or Theorem 3.1 was found. The minor-revision recommendation retains the concrete convention and evidence-location issues below; it is not editorial admission or a claim that every possible error has been excluded.

## Identity, participation and limits of this review

Provider/interface context: OpenAI Codex. The inherited orchestration labels this agent as configured `gpt-6-astra`; actual served backend identity and reasoning setting are not exposed. Configuration is not platform runtime attestation. No evidence hash, effort tier or verified model identity is invented.

I previously audited the full source185 proof and supplied objections subsequently incorporated into this supplement. This is prior participation in the work's development through review, so the participation classification is **involved_in_manuscript**. There is also historical ancestor-review context in the same account/provider/orchestrated chat. This is neither blind nor organizationally independent. I did not open earlier numerical assessment files for this task or ask another reviewer. Their absence from this task's file reads does not erase inherited context or establish fresh-context controls. The new numerical judgment covers the entire present supplement, including section 3, not merely the familiar laminate proof.

The declared review-round file was read from the delivery directory; the initially supplied exported-directory location did not contain it. It selects this one existing reviewer and expressly discloses the shared context and unavailable served identity. This path correction is not a manuscript defect. The AIRR numeric policy and assessment schema were read from the supplied worktree. The policy's illustrative scores were not treated as targets.

There is no assigned public AIRR version identity for these bytes. The accompanying JSON is explicitly draft-scoped, not a schema-native registry record. No receipt, assessment UUID, public version number or version_id is fabricated. This report does not provide the separate operator provenance, model quorum or human editorial decision that a later publication process may require. It is scientific model evidence, not human peer review.

## Inputs and work actually performed

- Verified the delivery PDF hash and byte size against the declared frozen artifact.
- Read the complete eight-page Poppler text at `D:\Datos\the-eriksson-programme\autonomia\evidencia-186\exported\rectangular_observations.txt`; its SHA256 is `4e1dc26ffb4566de86e20858f926f013974c737edb1b663cb82c9be7e6e33794`.
- Individually inspected all eight existing rendered page images, page-1.png through page-8.png, in that directory. This was not merely contact-sheet inspection.
- Read the supplied build report and manifest. All 48 manifest entries matched their local SHA256 values, including the exported PDF, text, images, source and build outputs. Matching hashes establish consistency of this supplied packet, not an independently authenticated build or proof of execution provenance.
- Read the current declared-review-round186.json and policy/schema. Consulted selected passages of two primary mathematical references identified below.
- Analytically checked the mathematical arguments, including explicit finite examples, without executing mathematical code. No local extraction, rendering, build, oracle, Lean, Lake, runtime creation, git/source mutation or PDF edit occurred. No other model was consulted. Only the report and its draft JSON were written under the authorized review directory.

The supplied build report identifies source context `fda4743d41960bf2c0cb018e113cccb85d62ca9a`. I did not independently verify that commit's complete source tree. The source185 hash printed on page 7 matches the hash I previously read, but that earlier audit is not substituted for the exact-PDF reading performed here.

## Mathematical assessment: Theorem 2.1 and the laminate construction

### Local estimate and simultaneous inequality (pages 1-3)

The hypotheses are sufficient: integer D>=3, integer n>=2, c>0, and an arbitrary strictly positive sequence alpha on the first coordinate. The partition is determined by coefficients and parameters, not by the tested field. It works on all scalar fields and componentwise on finite real or complex fields, hence on actual coexact subspaces by restriction. The paper now explicitly distinguishes complex dimension from its doubled real dimension.

For a cut interval I of length m, the resistance R_I includes the final start. This is a safe upper bound for the longitudinal path resistances and is also needed in transverse averaging. For each fixed transverse coordinate, the pairwise variance identity gives

Var_I(u)=(1/m) sum_{r<s}|u(r)-u(s)|^2 <= (m-1)R_I E_1/2.

Each pair was bounded by R_I times the whole internal path energy. This is coarse but valid. No exterior edge has been used as an internal edge.

For an unweighted l-vertex path, the coefficient of edge k obtained by path Cauchy and pair averaging is bounded by k(l-k)<=l^2/4. Product-space tensorization uses the largest coordinate Poincare constant, not the sum, so no hidden factor D-1 is missing. Weighted Cauchy for v(y)=m^{-1}sum_I u gives |D_j v|^2 <= R_I m^{-2} sum_I alpha|D_j u|^2. Orthogonal decomposition then yields the displayed mR_I/2 longitudinal and mR_I/4 transverse bounds. The common coefficient sequence across fibres is exactly the required hypothesis. The paper correctly calls mR_I/2 an inverse-gap bound.

The partition algorithm accepts equality mR_I=2/c and never splits singletons. A longitudinal singleton generates only singleton rectangles, whose variances vanish even if its resistance exceeds the threshold. Every other leaf passes c Var_R<=E_{a,R}. Discarding nonnegative cross-cell and periodic-closing edges, and summing the normalized-mean orthogonal identity, proves equation (1) with K=c. There is no hidden kernel-to-full-space Schur implication here. Cutting a full-period coordinate, including at n=2 where the ambient convention has two positive-start edges, only reduces the energy.

### Critical cost and odd integer sizes (page 3)

With p=D/2 and d=2p-1, Holder yields R_I<=m^(1-1/p)b(I)^(1/p). A split implies b(I)>(2/c)^p m^{-d}. Terminal internal nodes are incomparable and have disjoint interval mass. Assigning an internal node to a terminal internal descendant is legitimate in the finite tree. Along any such ancestor path the weight m^{-d} decays backwards by at least r=(2/3)^d per level. The geometric sum is therefore finite without a logarithmic multiplicity charge.

The balanced-child inequalities floor(m/2)>=m/3 and ceil(m/2)<=2m/3 hold for every m>=2, with the extremal odd case m=3 included. Telescoping leaf weights increases cost by at most 2*3^d times the parent weight per split. The actual transverse leaf count is ceil(n/m)^d<=(2n/m)^d. Multiplication gives precisely the stated B_D=2*6^d/(1-r). No power-of-two assumption, bounded aspect ratio, monotonicity of alpha, or bounded contrast enters the count.

The final inverse-moment conversion uses sum_X a^{-p}<=MN/mu^p and mu^{-p}<=2^p/(1+mu)^p for mu>=1, together with an additive constant absorbed by max(1,N/(1+mu)^p). This correctly proves the target upper order. The paper appropriately does not assert a matching lower bound for every individual coefficient.

### Thin layer and minimum-only certificate (pages 3-4)

For n=t^D, b=n^(2-2/D), mu=n^2 and H=(n mu-b)/(n-1), the mean, upper coefficient bound and moment formula check algebraically. The moment is strictly below 2 at each size but tends to 2. The PDF now explicitly uses a common M=2 and disclaims a common M<2, resolving the uniform-quantifier distinction from my source audit.

The root resistance is n^(-1+2/D)+(n-1)^2/(n^2-b/n)<2, so c=1 uses one global mean. Since b tends to infinity and b/mu tends to zero, no fixed B and theta>0 can enforce a<=B or a>=theta mu throughout the sequence. This is a genuine separation from that fixed-gap subclass, not a general arbitrary-coefficient solution.

A cell meeting the layer has minimum b. A transverse path coordinate test has gap at most 12/l^2, and a full-cycle Fourier test at most 40/l^2. Thus a cell passing the minimum-only sufficient test has transverse lengths <=sqrt(40b). It contains at most (40b)^{d/2} weak-layer vertices. Counting the n^d layer vertices gives the stated 40^{-d/2}n^{d/D} lower bound. Singleton testing is expressly vacuous. This lower bound concerns that certificate, not the actual successful observations on those same coefficients.

## Mathematical assessment: Theorem 3.1 and exact finite distinctions

### Spectrum and subcritical bound (pages 4-5)

For a cut l-vertex path, the stated cosine spectrum is correct. Tensorization with homogeneous a=n^2 gives equation (6). The n=2 distinction between the cut path eigenvalue two and retained positive-start periodic eigenvalue four is correctly stated before scaling. Adding full-period edges preserves connectivity and increases ordered eigenvalues. Trace monotonicity follows from the scalar eigenvalue comparison for every s>0, without incorrectly asserting operator monotonicity of arbitrary powers.

Each connected V-vertex rectangle has V-1 positive eigenvalues and lambda_max<=4Dn^2. Hence T_s>=(V-1)/(4Dn^2)^s, and a passing partition obeys equation (7). For fixed 0<s<D/2 this is the required Omega(n^(D-2s)) lower bound uniformly over aspect ratio and placement. Singletons are harmless because their trace is zero.

### Critical all-partition lower bound (page 5)

The dyadic mode-block argument is the main point requiring care. With m the smallest side, t_j=2^(j+1)/m and j from zero to floor(log_2 m)-3, all selected coordinate frequencies lie below half their corresponding side length. Consecutive blocks have matching ceil endpoints and are disjoint. Since t_j l_i>=2, each block has at least V t_j^D/2^D modes. Path and retained-cycle eigenvalues on these low-frequency blocks are bounded above by 256D n^2 t_j^2. At p=D/2 the powers of t_j cancel. The smaller safe constant A_D=2^{-D}(256D)^{-ceil(D/2)} is valid also for odd D. This proves equation (8), including very anisotropic rectangles.

In any q-cell partition, cells with V>=N/(2q) cover at least half the vertices; each side of such a cell is at least n/(2q), since all other sides are <=n. Summing their trace lower bounds yields the displayed implicit inequality in q. For n>=2^16, the split q>=sqrt(n) versus q<sqrt(n) yields q>=(A_D/8)log_2 n as claimed. Thus the logarithmic obstruction is not an artifact of choosing cubes or a particular hierarchy.

### Matching meshes and the weak endpoint (page 5)

Equation (9) follows from lambda_k>=4n^2 max_i(k_i)^2/M^2 and at most D2^{D-1}j^{D-1} modes in a max-frequency shell. The three sums are respectively O(M^(D-2s)), O(1+log M), and bounded for 2s>D. The proposed choices of M give n^(D-2s), log n, and constant cell counts, with floor-zero cases handled by singletons. Short final intervals only improve the bound. For s>D/2 the lower order is simply q>=1. These observations establish the full three-regime Theta statement as an asymptotic claim for fixed D and s.

The actual cut-root gap is at least four. The weak counting estimate W_p<=1 follows by bounding frequencies with |k|<sqrt(lambda)/2, using (1+sqrt(lambda)/2)^D<=lambda^(D/2) for lambda>=4. If an eigenvalue were below one, choosing a threshold between it and one would contradict this bound by integrality of the counting function. This really is a sufficient weak certificate here; it does not furnish the missing variable-coefficient construction.

### Exact finite examples and a convention clarification (page 6, section 3.3)

For D=4,n=4,a=16, the periodic spectrum and multiplicities binomial(8,m) follow from the generating polynomial (1+z)^8. The two displayed contributions give 56/96+70/128=217/192>1. A cut length-two four-dimensional box has trace [4+6/2+4/3+1/4]/32=103/384. Both values check.

For n=2,mu=4,c=16, the asserted spectrum 16m with multiplicity binomial(r,m) is correct **when both positive-start periodic edges are retained in each full coordinate**. Then 16^p T_p=sum_{m=1}^r binomial(r,m)m^{-p}; it passes exactly for r<=1. A cell has at most two vertices, and the minimum is 2^(D-1). The D=4 root value is 4+6/4+4/9+1/16=865/144. The actual periodic gap is 16, so the global one-mean inequality with K=c holds.

The paragraph should explicitly name that retained-edge convention. Section 3 initially permits both cutting and retaining full-period coordinates, but the exact finite statement is not independent of that choice. If every full coordinate is cut, a two-vertex cell instead has eigenvalue 8, its test value is 2^p>1, and all nonsingleton cells fail; the minimum is then 2^D, not 2^(D-1). If q_s optimizes over the allowed retention choices, the stated minimum remains correct because retaining edges is best. If the convention is fixed in advance as all-cut, it changes. This is a precise local ambiguity and correction request, not a disproof of the asymptotic Theorem 3.1, whose orders survive both conventions.

The all-pairs resistance identity at the end of section 3.3 follows from G_R 1=0 and the Laplacian pseudoinverse formula for resistance. The paper correctly limits its identification to s=1 and does not rule out every resistance-based method.

## Mathematical assessment: actual coexact falsifier (page 6, section 4)

The coefficient sum is 27+37*64=2395; the mean and 1<=a<=2mu check. The critical moment bound is 31991/320<100, using mu<38, sqrt(mu)<31/5 and mu/64<1. The favorable fibre has four coefficients 64, yielding nR=1/4<4/15.

For G a delta at (1,1,1), the stated two backward-difference components are generated by an antisymmetric plaquette potential, up to global sign convention. Their backward divergence cancels. Each is a pair of opposite adjacent deltas with norm squared two and zero mean. At n=4 its connecting-direction gradient energy is six and each other direction contributes four; the two components have total energy 28. All nonzero forward-gradient starts are inside {0,1,2}^3, so the actual weighted energy is also 28. The target is (15/2)*4=30 while the global mean vanishes. This is a valid coexact counterexample to the proposed representative-fibre one-cell extension, not to the laminate theorem or the unrestricted partition question.

## Literature, originality and programme relevance

I checked the actual statements of Lemma 3.1 and Theorem 5.7, with the rectangular mesh condition (5.6), in [Nochetto, Otarola and Salgado, arXiv:1402.1916v2](https://arxiv.org/pdf/1402.1916v2). They use Muckenhoupt-weighted Sobolev norms and constants depending on the weight characteristic and geometry; the rectangular interpolation theorem assumes comparable neighboring coordinate sizes. The supplement accurately distinguishes those stated results from its finite counting-norm observation theorem with inverse-moment cell budget. This distinction does not establish that no earlier theorem, reduction or adaptive construction yields the same result.

I also checked Section 2's weak Schatten definition and associated discussion in [Frank, arXiv:1206.3325v1](https://arxiv.org/pdf/1206.3325v1). This is appropriate context for the classical weak-versus-strong ideal distinction. It is not a priority certificate for the supplement's exact finite all-partition cost theorem.

Muckenhoupt and Binev-DeVore were not fully read or independently compared in this assessment. The manuscript itself admits limited retrieval and does not import their inaccessible proofs. Its elementary derivations stand on their own, but broad priority relative to weighted approximation and adaptive partition literature remains unestablished. No claim of independent originality is warranted.

The strongest plausible specialized contributions are the explicit laminate construction under a global critical inverse moment, the arbitrary-aspect rectangular certificate-cost lower bound with matching meshes, and the concrete separation examples tying these mechanisms together. Their value is within finite weighted observation design. No interacting theory, continuum scaling limit, physical mass gap, general critical rectangular theorem or Millennium solution follows. The PDF consistently retains these boundaries.

## All objections, corrections and unresolved limits

**O1 — Exact finite edge convention, page 6 section 3.3; minor mathematical clarification.** Add that the n=2,c=16 example retains both positive-start periodic edges on full coordinates, and distinguish its exact minimum from the all-cut convention. The explicit all-cut falsifier is the two-vertex eigenvalue 8 and test value 2^p>1 described above. Theorem 3.1's asymptotic orders remain supported.

**O2 — Incomplete evidence locator, page 7 section 5.2 and reference [6] on page 8; reproducibility correction.** Reference [6] gives a commit hash but no repository URL or evidence directory paths. A commit hash alone is not a self-contained retrieval location. Add a stable repository URL and pinned paths or an archived manifest linking the exact programs, inputs and execution records. This does not prove the evidence is unavailable publicly; it means the PDF does not tell an external reader how to locate it without additional dossier knowledge.

**O3 — Execution assurance remains limited, page 7.** The numbers of payloads, controls, mutations and tests are manuscript reports. I did not independently rerun or comprehensively inspect those scientific archives. Matching this build packet's hashes is not verification of those mathematical executions, and repeated clones using the same source are not independent replication. The PDF already says this; retain it in any public summary. No formal verification claim is supported.

**O4 — Priority remains open, pages 6-8.** The targeted literature comparison is relevant and cautious but insufficient for a novelty ruling. A human specialist comparison with weighted approximation/adaptive partition results would materially strengthen the originality claim. Avoid implying that the known Hardy, tensorization, spectral-counting, weak-ideal or adaptive-tree principles were invented here. The present PDF does not make that overclaim.

**O5 — Finite and subclass scope, pages 1, 4, 6-7.** The positive theorem retains one-coordinate lamination. The negative Green result constrains a sufficient certificate rather than all successful observations, and the coexact witness rejects only a representative-fibre mechanism. These are substantive restrictions, correctly disclosed, which limit broader significance. They must not disappear from abstracts, release summaries or numerical-star displays.

**O6 — Presentation and metadata, all pages and build report; editorial.** All eight page images are legible; I observed no clipping, overlap or missing formulas. There are repeated missing prose spaces such as 'units184', 'gap is32', 'coefficients64', 'controls,72' and 'commit506...' and compressed bibliography journal/volume joins. Correct these in a later typeset artifact. The supplied pdfinfo report shows empty Title, Author, Subject and Keywords metadata despite the visible title and author. Populate appropriate bibliographic metadata for discoverability in a future artifact. The source hash is split across two lines on page 7, but reconstructs correctly; provide a directly copyable manifest alongside it. None changes the present mathematical findings.

No material objection presently shown to invalidate either principal theorem is left unresolved. This statement must be read together with O1-O6 and the explicit limits of a single involved model's inspection; it is not proof certification or permission to suppress adverse findings.

## Final disposition and preservation

Retain this complete report and its one numerical result against SHA256 `040cae56bad1deb48605ea72f7d4e9ee28da00de702b5ebb11c039129fe65146`. Minor revisions to the finite boundary convention, evidence locator and presentation are recommended. Any changed PDF is a different artifact; the current score is not automatically transferred to it. This report is an annex to the frozen draft, not a request to alter its bytes recursively to include the assessment.

The associated JSON intentionally remains draft-scoped. It must not be described as a native imported AIRR version record, served-model attestation, fresh blind evaluation or editorial acceptance. This sole assessment's positive findings and all qualifications are preserved without resampling.
