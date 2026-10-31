# Scientific model assessment of the exact integrated manuscript

Date: 2026-10-30. Review identifier: astra-exact-pdf-024. No numerical score requested or assigned.

## Artifact and scope

Reviewed: Lluis Eriksson, *Coarse information and finite rank obstructions for flat lattice Hodge forms*, dated 30 October 2026, eight pages, supplied as `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-integrated\flat_coarse_rank.pdf`.

Verified PDF SHA256: `119ea6ae2f0434598aab39d0f1ba338fec8fd8a27ca67faef2474f7d58561eed`.
Verified LF-normalized TeX SHA256: `ec1f4090f71d9bf0260bba62ebdb507286d121a72c93ad6e5d4c06d484a9c5dd`.
Supplied manuscript commit: `d803cd3b920a7547420352ed28abc204593d1685`.

I read the review request, complete TeX, declaration map, historical reconciliation, validation024.json, and historical extracted text. I visually inspected all eight page JPEGs and independently checked every JPEG hash against the manifest inside render024.zip. The manifest also identifies the exact PDF and TeX hashes above. I did not rerender or recompile. All pages are legible; no clipping or missing mathematical symbols was apparent. Page 7 has substantial unused space from the forced page break before the disclosure; that is cosmetic.

The historical PDF hash was independently checked as `48b2b725422263a272d9862621fa723d3d82c9d186dd7151be39c6ff1e3ff2e7`. Historical comparison used its supplied extracted text; I did not re-extract or visually review all thirteen historical pages. The comparison therefore has an extraction-fidelity limitation.

## Assessment

**Correctness:** The explicit finite-dimensional arguments in the body are mathematically sound on the intended integer lattices with linear measurements. I found no counterexample to Lemma 4.1, Theorem 5.1, Proposition 5.2, Theorem 6.1, or Proposition 7.1 under their intended hypotheses. The retained block witness, spectral ladder and witness-repair identities also check out. This is a reading assessment, not an exhaustive proof certification. The abstract has a material scope omission: it does not say that the observations are linear, and its unrestricted wording is false for nonlinear observations. This must be corrected. There are smaller parameter and source-identification defects below.

**Originality:** The mathematical mechanism is elementary classical Fourier analysis, rank-nullity/min-max, and singular Schur complementation. The paper candidly disclaims a new general spectral principle. Its defensible contribution is a concrete formulation, normalization audit, extension from a particular erased witness to arbitrary linear finite-dimensional observations, and formal development for this programme. A broad mathematical novelty or priority claim is not supported. The two-item bibliography is insufficient to document the classical Schur and relevant gauge-RG context. A targeted primary-source search does not establish that the exact packaged statement has never appeared before.

**Programme relevance:** The result gives a valid negative constraint on a specific unscaled, full-space flat route. It prevents repeated attempts to repair that route using only a fixed number of linear observations or uniformly bounded-rank fine terms, and separately excludes bounded-codimension sectors of the specified form. This is a useful diagnostic, not a positive construction of the physical theory. Its relevance to an interacting, physically scaled or gauge-restricted continuum programme remains conditional on bridges not supplied here. No Yang-Mills mass-gap progress in the sense of establishing a positive gap, continuum construction, or reconstruction theorem follows from this manuscript.

Disposition as a scientific model assessment: **qualified support for the narrowly stated analytic results; revise scope wording, attribution and reproducibility presentation before treating this exact PDF as a finished scientific account.** This is not an editorial acceptance or a recommendation to bypass independent review.

## Detailed mathematical checks

### Sections 2-3, pages 1-3: normalization and retained historical results

1. The real embedding E_j is injective and isometric because u and v are orthogonal internal unit coordinates. There are at least two such coordinates for Nc >= 2. For one nonzero spatial component, each unordered pair involving j contributes one forward-difference norm, with the sign irrelevant after squaring. The divergence contributes the backward j-difference; translation invariance equates its total norm to the forward difference. Equation (2) has no missing factor of two. The phrase "exclusive two plaquette incidences" means the mutually exclusive cases j=i or j=k, not two contributions per unordered plaquette.

2. The constant-sector block calculation gives Q_ell A = ell v. Fine and coarse counting norms are therefore ell^d (N')^d S and ell^(2sigma+2) (N')^d S. The condition sigma >= (d-2)/2 is necessary for this sector as ell grows, with equality uniquely scale-neutral. It is correctly not advertised as full-space sufficiency.

3. For distinct p,q and ell >= 2, the profile exp(2 pi i x_q/ell) is well defined on a torus of side ell N'. The q-offset root sum cancels every block. The p-line shifts leave the profile unchanged. The p-divergence vanishes, including wraparound. The norm is (ell N')^d and the single contributing curl direction has squared multiplier 4 sin^2(pi/ell). Equation (3) follows. At ell=2 the imaginary part of this particular profile is zero, but the witness remains nonzero; no parity exception is needed.

4. The factorized-penalty conclusion uses only Psi(0)=0. Inserting the witness gives CP(ell) >= 1/lambda_ell >= ell^2/(4 pi^2). A discontinuous or negative-valued penalty causes no problem because it is evaluated at zero. The statement concerns an inequality assumed on the entire domain; existence of such an estimate for every chosen nonlinear penalty is not claimed.

5. The historical higher-frequency spaces have real dimension two each because a complex coefficient is stored in two real internal coordinates. Real inner products are real parts of the complex Gram sum. Distinct r in the stated half-band are orthogonal, and derivative amplitudes have the same frequency Gram orthogonality. Thus the bound holds for arbitrary linear combinations, not just generators. The monotonicity of sin(pi r/ell) on the stated range and finite-dimensional min-max give the displayed 2R-th eigenvalue bound. R=floor(ell^alpha), 0<alpha<1, eventually lies in the range, and R^2/ell^2 <= ell^(-2(1-alpha)). No nonlinear eigenvalue interpretation is used.

6. Expansion of the changed-map quadratic form gives exactly lambda_ell + epsilon_ell^2 + nu_ell. Its finite-scale necessary inequality and liminf consequence follow. Homogeneity proves the claimed equivalence only on the real line spanned by the one witness. The leakage identity epsilon_ell^2=ell^(d-2) eta_ell^2 is correct; in d=4 leakage o(ell^-1) cannot repair even this line when V=0. No sufficiency for the whole field space follows, as the text correctly says.

### Section 4, pages 3-4: constructed real band

Take R to be a nonnegative integer (the PDF should say this explicitly). Coordinate differences between frequency indices have absolute value <= 2R<n, so no nonzero such difference is zero modulo n. The complex character Gram matrix is n^d I. Synthesis therefore has complex rank B=(2R+1)^d, real rank 2B. There is no reality constraint a_-k=conjugate(a_k): f is complex and its two components are stored as independent real field coordinates. Consequently including both k and -k does not create the commonly suspected factor-of-two overcount. For R=0 the space consists of two independent constant internal components and the energy bound is zero, as required. The n=1 admissible case is correspondingly R=0.

Applying the same Gram identity after multiplying each coefficient by exp(2 pi i k_i/n)-1 proves the full-sum energy formula. The multiplier estimate |exp(it)-1|<=|t| yields 4 pi^2 d R^2/n^2. All norms have counting normalization and unit differences. This is a conservative band using one spatial component and two internal coordinates; it is not asserted to exhaust the entire low spectral subspace.

### Section 5, pages 4-5: finite rank and sectors

The image of (C,V) restricted to S_R has dimension at most dim F + rank V. If this is less than 2B, rank-nullity supplies a nonzero A with CA=VA=0. The extra quadratic term then vanishes even for nonsymmetric V. Combining the two inequalities contradicts the strict threshold c>b_R(n). The bound need not use rank of the symmetric part of V; killing V itself is sufficient. Allowing a large norm for V cannot escape its kernel.

The codomain count is intentionally weaker than replacing dim F by rank C. The sharper analytic inequality follows by the same argument, but is not needed and is not claimed as the recorded formal endpoint. Equality of the budget or c=b_R(n) produces no contradiction, and the PDF correctly uses strict inequalities in the obstruction.

For Proposition 5.2 the same argument applied to (C,P) produces a vector in ker P directly. Thus the sector result is not an invalid deduction from full-space failure. No positivity or projection property of P is necessary. Rank P equals the codimension of ker P in this finite-dimensional setting. The example d=4, n=16, R=1 gives 2*3^4=162, b=pi^2/16<1 and 12+149=161: it is correct.

### Section 6, page 5: quantifiers

F and the bound r are fixed while n_L=(L+1)N' tends to infinity with fixed positive integer N'. The maps and penalties may depend on L. Choosing R=M+r+1 after M=dim F and r, and then L after the proposed c>0, correctly defeats any such families. The finite choice L>max{2R,a/c,1} is more than necessary but valid: n_L>L>1 and a<cL<=c n_L^2. There is no hidden requirement of uniform operator-norm bounds, continuous dependence on L, or locality.

The theorem does not treat arbitrary nonlinear observations, bounded-rank nonlinear maps, growing-codimension gauge constraints, or arbitrary quotient norms. A harmonic/constant removal represented by a bounded-rank linear P is covered. General local gauge fixing typically imposes a number of constraints growing with lattice size, so its exclusion cannot be inferred. These limits are scientifically significant even though they do not invalidate the theorem.

### Section 7, pages 5-6: fixed-map criterion

For N=ker C and W=N-perp, restriction to N forces A>=0. If z is in ker A and D*w has nonzero pairing with z, varying tz+w keeps the observation fixed but makes the quadratic form unbounded below. This forces ker A subset ker D*. Since A is self-adjoint in finite dimensions, the latter is equivalent to range D subset range A. Completing the square using A-dagger then proves sufficiency exactly as written. C restricted to W has a linear inverse on its image, and a finite-dimensional extension T to F exists. The displayed quadratic penalty cancels the remaining Schur form. With a Euclidean norm on F, a sufficiently large nonnegative multiple of ||y||^2 also works because that inverse is bounded. The existence statement places no bound uniform in changing C or H on the necessary penalty coefficient; none should be inferred.

The example H=diag(0,2), c=1, C(x,y)=x+y gives B=diag(-1,1). On ker C its form is zero, but on (t,1-t) it is 1-2t. Thus no finite Phi(1) repairs it. Detection of the negative eigendirection and nonnegativity on the kernel are genuinely insufficient at the singular boundary. The proposition is correct but classical, not evidence of a new general sufficiency principle.

### Section 8, page 6: scaling and actual consumer

Multiplication of K0 by ell^2 changes the particular band bound to 4 pi^2 d R^2/(N')^2. This no longer tends to zero in ell for fixed R and N'. The proof therefore stops; the manuscript correctly does not turn that failure into a positive physical coercivity theorem. In the unit-spacing convention, increasing n increases the torus side in lattice units. Calling this "refinement" must not silently import fixed physical spacing/domain conventions of a continuum limit.

I read the main-tree `PhysicalGaugeFixedPrecision.lean` definition and coercivity adapter. It explicitly treats the shell K0+a Q*Q-Sigma, a positive a and a strict summable perturbation budget. Its certified constant is min(1,a)/CP minus that budget. The zero-perturbation base gives the manuscript's min(1,a)/CP. The source explicitly describes itself as fixed-volume and leaves Wilson-Hessian and uniformity identifications external. Thus the text's narrow base-route specialization is supported. It should identify the zero-perturbation specialization and exact declarations in its companion map rather than asking the reader to find them. The phrase "its coercivity constant is" should mean a certified lower bound, not an assertion of the optimal spectral constant.

## Objections and corrections retained

### O1 — Material abstract scope omission (page 1, first three abstract sentences; compare Section 5)

The abstract says observations in a fixed finite-dimensional space can vary arbitrarily, without stating linearity. The literal nonlinear reading is false. A concrete falsifier is F=R, C_L(A)=||A||^2, Phi_L(y)=y, V_L=0. Then Phi_L(0)=0 and K0>=0 gives ||A||^2 <= <A,K0 A>+Phi_L(C_L A) for every L. Even a single scalar nonlinear observation suffices. This is a direct counterexample to the overbroad wording, not to the body theorem.

Correction: say "linear observations into a fixed finite-dimensional real space" and "linear fine-space repairs of uniformly bounded rank" in the abstract. Preserve the separate freedom that Phi_L may be arbitrary and nonlinear. Also avoid describing the result outside the PDF as applying to arbitrary measurements without this qualifier.

### O2 — Implicit discrete parameter hypotheses (Section 3, page 2; Section 4 opening, page 3; Section 6 opening, page 5)

R is introduced only as R>=0 although {-R,...,R}^d and its cardinality formula require R to be an integer. The first introduction of ell and N' in Section 3 similarly leaves their integer/positive character implicit; Section 6 states N'>=1 but not explicitly integer. A reader can infer the intended parameters, and the inspected Lean statements use naturals and nonzero hypotheses. Nevertheless the mathematical setup should not rely on this inference.

Correction: declare ell,N' positive integers in Section 3 and R a nonnegative integer in Section 4; explicitly take N' positive integer and L nonnegative integer in Section 6. A literal noninteger R destroys the claimed cardinality formula; this diagnoses the missing declaration rather than a defect in the intended proof.

### O3 — Classical attribution and contextual bibliography are inadequate (Section 1, page 1; Section 7, pages 5-6; references, page 8)

Only the author's predecessor and Dodziuk are cited. Dodziuk is appropriately described as historical context, but does not by itself document the singular-Schur criterion or the min-max/rank-perturbation background. Calling Proposition 7.1 classical without a direct reference leaves a visible attribution gap. The original paper's Balaban/Dimock discussion has also disappeared from the bibliography, despite the continuing programme relevance and restricted-domain caveat.

Correction: cite appropriate classical matrix sources directly next to Proposition 7.1; explain that the nonlinear-penalty formulation follows by minimizing on each fiber of C, using the standard singular Schur condition. Restore at least a concise primary-source gauge-RG comparison. Do not present these additions as novelty certification. Exact priority for the packaged lattice/formalization result remains unverified.

### O4 — Consumer and reproduction access need a precise public map (Section 8, page 6; Section 9, pages 6-7; supplied declaration-map.json)

The consumer specialization is asserted through repository inspection, but the external declaration map lists no consumer declaration, source file or zero-Sigma specialization. It lists module names and evidence directories for formal endpoints, but the PDF itself does not provide a direct repository URL or a resolvable URL for the map. Bare SHAs and local directory names are not sufficient for a reader without this supplied workspace to reproduce the audit. I could check the source locally; an ordinary reader may not.

Correction: provide a stable repository/source link and supplement location, and map `flatGaugeFixedPrecisionCLM` and `flatGaugeFixedPrecision_coerciveWithPositiveConstant_of_flatPoincare` at the inspected SHA, explicitly taking zero perturbation. Describe min(1,a)/CP as an available lower bound. Ensure old and new anchors remain separately accessible. This is a reproducibility/presentation objection, not an allegation that the source specialization is wrong.

### O5 — Historical retention should be qualified (Section 3 opening, page 2; reconciliation supplement)

All principal mathematical results of the historical paper are retained: constant sector, exact transverse kernel witness, first-mode energy, arbitrary factorized penalty, spectral ladder, repair identity, liminf, witness-line equivalence and leakage scale. However the old Appendix A square-wave precursor (even ell, quotient 8/ell) and the substantive Balaban/Dimock contextual discussion are not reproduced. The appendix is weaker and is not needed for any current proof; its omission does not remove the main theorem. Calling the replacement literally complete in every respect would nonetheless overstate retention.

Correction: describe retention as the principal results and state that the historical appendix remains in v1; optionally retain a one-sentence square-wave note. Restore the relevant gauge-RG context as in O3. Do not erase the historical version or its distinct evidence record.

### O6 — Formal evidence remains reported evidence, not this review's reproduction (Section 9, pages 6-7)

I inspected selected source declarations and their mathematical correspondence, but did not execute Lean, Lake, or the focal oracles. I did not independently recompute all old/new compiled-object, raw-log and source-manifest comparisons or audit the full dependency closure. The exact PDF's assertion of complete same-source runs therefore remains a supplied provenance claim beyond the scope of this reading assessment. This limitation must not disappear when this review is summarized.

Correction: retain the stated analytic/formal separation, link all evidence, and describe my work as source inspection plus analytic review. Do not use this report to claim an independent Lean rebuild or full formal certification. Reproducibility claims can be separately audited on the authorized Linux workflow if needed; no new run is required merely to resolve the analytic arguments assessed here.

## Originality: primary-source comparison

The following are primary publications or author-hosted research sources inspected through their publisher/repository pages. This was targeted verification, not an exhaustive novelty search.

- Arthur Albert, *Conditions for Positive and Nonnegative Definiteness in Terms of Pseudoinverses*, SIAM J. Appl. Math. 17(2), 434-440 (1969), https://epubs.siam.org/doi/10.1137/0117041 . Publisher bibliographic record verified; full paywalled article not read in this review. It is a relevant classical attribution to investigate/cite, not a newly verified line-by-line source for every formulation in Proposition 7.1.
- David Carlson, Emilie Haynsworth and Thomas Markham, *A Generalization of the Schur Complement by Means of the Moore-Penrose Inverse*, SIAM J. Appl. Math. 26(1), 169-175 (1974), https://epubs.siam.org/doi/10.1137/0126013 . Publisher abstract explicitly treats D-CA^+B and associated matrix questions. This verifies the established generalized-Schur lineage; the fixed-map equivalence in this report was also checked directly by its proof.
- Jakob Hansen and Robert Ghrist, *Toward a Spectral Theory of Cellular Sheaves*, author-hosted manuscript, Section 5.1, https://jakobhansen.org/publications/spectralsheaves.pdf . Its low-rank perturbation interlacing discussion illustrates that the underlying spectral rank mechanism is standard in discrete Hodge settings. It is not claimed as the earliest source or as containing this exact lattice normalization.
- Jozef Dodziuk, *Finite-difference approach to the Hodge theory of harmonic forms* (1976), institutional record https://academicworks.cuny.edu/gc_pubs/180/ . The identity and historical relevance of the manuscript's cited source are supported. No claim is made that it proves this paper's precise torus formula.
- J. Dimock, *Covariant Axial Gauge*, arXiv:1410.2798v2, https://arxiv.org/html/1410.2798v2 . The author's introduction and gauge-fixing construction explicitly combine block averaging with restrictions and distinguish small lattice spacing from large unit-spacing volume by scaling. This supports the importance of domain/scaling qualifications and the need to restore that context. It does not establish the present programme's missing interacting bridge.

No new-general-theorem priority is warranted by this comparison. A formalization may be a useful original artifact even when the mathematics formalized is standard. Whether that package meets a particular journal's significance threshold is an editorial question this model assessment does not settle.

## Formal-source inspection and limits

Read-only git inspection at new main-tree anchor `e31b428917aa767b4a1aad097db5cf92fb9cd23e` covered `PhysicalFourierRankObstruction.lean`, `UniformPhysicalCoarseRankWall.lean`, `TorusPhysicalHodge.lean`, and the relevant beginning of `PhysicalGaugeFixedPrecision.lean`; targeted searches also located the flat-Poincare and localization consumers. The theorem statements use linear maps, natural R, nonzero lattice side and dimension, Nc>=2, the actual flat Hodge operator, and the necessary rank/strict-threshold assumptions. The uniform proof constructs its R and L rather than assuming a supplied low-energy subspace. The finite budget theorem reaches the physical band through proved dimension and energy declarations.

A git diff of all `YangMills` paths from tested uniform commit `17ca395d4e9de992b1c575454a112da9e6f97e86` to the new tree produced no differences. A targeted diff of `PhysicalFourierRankObstruction.lean` from tested `a79e6e4b2e5de72e73bd6109069eb2f82127c355` to the new tree also produced no differences. These are source-identity checks, not builds.

I separately read the preserved old `PhysicalCriticalRescalingFourierFactorizedRepair.lean` at `7b25bfb39357406cf61880e3ac0428d7d1ba3449`. Its factorized and repair endpoints explicitly specialize to dimension four. The module was absent from the new tree's RG file listing. The PDF properly keeps the old anchor separate and labels the general-dimension, trigonometric, spectral and asymptotic discussion analytic. I found no evidence in the inspected declarations that the paper substitutes an assumed band for a constructed one. I did not audit every imported definition or validate actual compiled objects.

## Relevance and concrete future falsification criteria

The next scientifically meaningful step is not to obtain a more favorable score for this obstruction. It is to specify which premise a proposed physical route changes, then prove the corresponding claim. A purported counterexample to Theorem 6.1 must keep a fixed finite-dimensional real F, linear C_L, uniformly bounded rank V_L (or P_L for the separate sector claim), unit-spacing K0, and one c>0 for all L. If any one of these changes, it is a different problem, not a refutation.

For a changed observable, checking nonzero response on the historical witness is only a necessary first test; the new band theorem forces an increasing effective budget for uniform unscaled full-space control. For a proposed fine Hessian, a finite rank bound cannot suffice, but a growing-rank or full-rank positive term is not ruled out. For a quotient, one needs a specified norm, representative/sector map and a justified coercivity theorem. For physical scaling, recompute the exact energy and norms before transferring any obstruction. None of these tasks is resolved by an axiom audit alone.

## Model assessments and review context

Configured reviewer model requested in the delegation record: `gpt-6-astra`. Actual served model identity was not exposed to this reviewer; a requested configuration is not proof of backend identity. Reasoning setting was not exposed to this reviewer and is not inferred. This assessment was generated through the OpenAI/Codex workflow in the same orchestrated chat/account/provider context as the preparation. The reviewer agent had no prior involvement in preparing the manuscript, but received the manuscript's provenance, review questions and limitations from the orchestrating agent. This is neither blind nor organizationally independent review. Any operator-visible service metadata should be retained separately and not replaced by model self-report.

No older score or review was inherited as an assessment of these bytes, and no score target guided this review. No manuscript edits, publication, submissions, external chat messages, new runtimes, Lean execution, purchases or provider transfers were performed. Only this report and its machine-readable summary were written in the authorized review directory. This model assessment is distinct from human peer review, editorial decision and publication. All objections above remain part of the assessment even if a later manuscript corrects them; a later artifact requires its own identified review scope.

## Input-file and task-context record

The parent agent supplied this as the one user-authorized named-model review of the exact integrated eight-page candidate, requested scientific objections without a target grade, prohibited delegation and manuscript changes, and required Windows read-only/light inspection without Lean/Lake execution. A follow-up instruction confirmed that the reviewed PDF will remain frozen and any correction will be a new artifact. Those statements are supplied context, not independently established external permissions or service telemetry.

Files read or inspected for the assessment:

- `D:\LEEME.md` and `C:\Users\lluis\.codex\plugins\cache\openai-primary-runtime\pdf\26.1026.10807\skills\pdf\SKILL.md` (operating instructions).
- `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-integrated\SCIENTIFIC-REVIEW-REQUEST.txt`.
- `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-integrated\flat_coarse_rank.pdf` (exact hash; visual content via bound page images).
- `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-integrated\flat_coarse_rank.tex`.
- `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-integrated\declaration-map.json`.
- `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-integrated\HISTORICAL-SCOPE-RECONCILIATION.md`.
- `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-integrated\validation024.json`.
- `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-integrated\render024.zip` (entry list and manifest.json read without extraction).
- `D:\Capturas\the-eriksson-programme\2026-10-30_flat-wall-integrated\page-1.jpg` through `page-8.jpg` (all eight visually inspected and hashes checked against the manifest).
- `D:\Datos\the-eriksson-programme\autonomia\evidencia-023\historical-paper.pdf` (hash check).
- `D:\Datos\the-eriksson-programme\autonomia\evidencia-023\historical-paper.txt` (historical mathematical/context comparison, including a separate read of pages 5-6 to avoid tool-output truncation).
- Read-only Git objects from `D:\Proyectos\the-eriksson-programme` at the explicitly identified old/new/tested commits; selected modules and scope of inspection are listed above.

No other local assessment or earlier model score was read as review evidence. The report is specific to the exact PDF hash; it does not automatically apply to later corrections.
