# Exact-artifact scientific correction assessment

Review ID: astra-exact-pdf-corrections-025. Date: 2026-10-30.

## Identification and outcome

This is a new assessment of the corrected eight-page manuscript, *Coarse information and finite rank obstructions for flat lattice Hodge forms*, specifically the frozen PDF at:

`D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-corrected\flat_coarse_rank.pdf`

Verified PDF SHA256: `b37f2fe86b7a8a526ad02f8b28491c300a9ff72d5653536bc5532e8c9468ed8f`.

Verified LF-normalized TeX SHA256: `f8e0699eb9e5fac4f89ceb94f2b8be539052ffd017f2f13b0eae703fe82d81a5`.

Supplied manuscript source commit, also recorded by the render report: `77b8ec265dea2bd6b3e6c9ffe85e02b423a9e00b`.

Verified render026.zip SHA256: `268dfdbc56265bb9074482bfe8375e1f62b02629228ed5a506b707e1b02c2f77`.

**Outcome: solid within the stated finite, flat, unit-spacing, linear-observation scope. O1-O5 are substantively resolved in this artifact. O6 remains an explicit verification limitation. No new material mathematical error or blocking objection was found in this correction review.** This is a qualified scientific model assessment, not proof of error-free mathematics, independent formal certification, editorial acceptance, or publication.

I assign no numerical score and seek no target score. The prior report remains intact and continues to describe the previous PDF. Its verdict was not transferred to these new bytes: I read the new complete TeX, visually inspected all eight new pages, reviewed the changes, and rechecked the principal arguments and corrected source specialization. The weighted derivative family of PR98 is outside this manuscript and outside this assessment.

## Evidence and method

I verified the delivered PDF hash and LF-normalized TeX hash. I read the render026 manifest and recomputed all 28 listed file hashes; all matched, including the PDF, TeX, extracted text, report, and all eight page images. I inspected page-1.jpg through page-8.jpg individually at `D:\Datos\the-eriksson-programme\autonomia\evidencia-025\render026`. The report records eight pages, nine steps with exit code zero and no layout warnings. These execution records are supplied provenance, not steps I reran. My own visual check found no clipping, overlapping mathematics, missing symbols or unreadable references.

I compared the prior and corrected TeX using a read-only diff. The main analytic proof bodies were not replaced: changes clarify scope and integer types, add the nonlinear-observation counterexample, add classical and gauge-context attribution, qualify historical retention, specify the consumer specialization and links, and expand disclosure. The prior complete report and summary retain their original verified hashes:

- Previous report: `954afe0931bc039321194b95787145ab1e0d0337b51290fdd73a4d8087842fd1`.
- Previous summary: `9152e8410094f8adf3a737a0d508bde0349e962176e98fabcc7a41f6959ca576`.

I read the corrected declaration map both locally and at its exact Git object. The exact linked GitHub map was also successfully retrieved through the GitHub connector. I reread the beginning of the consumer module and its explicit-Poincare coercivity theorem at the stated formal-source anchor. No Lean, Lake, oracle, compilation or rendering was executed locally. No source, PDF, repository state or public service was changed.

## Objection-by-objection assessment

### O1: essential linearity — resolved

**Locations in corrected PDF:** abstract and Section 1, page 1; Section 5, page 4; Section 6 and its concluding paragraph, page 5.

The abstract now explicitly requires linear observations into a fixed finite-dimensional real space and linear fine-space repairs of uniformly bounded rank. Section 1 says the map is always real-linear while its output penalty may be nonlinear. Section 6 explicitly declares linear C_L and V_L, arbitrary scalar functions Phi_L with Phi_L(0)=0, and linear sector constraints P_L in Theorem 6.1.

The previously decisive counterexample is retained on page 5: allowing C_L(A)=||A||^2 into R and Phi_L(y)=y with V_L=0 gives c=1, because the flat Hodge form is nonnegative. This is correct and directly explains the essential distinction between nonlinear observation and nonlinear post-observation penalty. It no longer contradicts the corrected abstract or body. The old objection is resolved by a genuine hypothesis correction, not by deleting the counterexample or changing the scientific question silently.

The abstract's phrase about bounded-rank constraints is understood in the standard linear-algebraic sense, with explicit linearity supplied in Proposition 5.2 and Theorem 6.1. It does not license a claim about arbitrary nonlinear constraints.

### O2: discrete parameter types — resolved

**Locations:** Section 3 opening, page 2; Section 4 opening, page 4; Section 6 opening, page 5.

The block side ell and coarse side N' are now positive integers. R is explicitly a nonnegative integer. Section 6 takes N' positive integer, L nonnegative integer, and the uniform rank bound r nonnegative integer. Section 2 already declares integer d,n,Nc with their lower bounds. Consequently the cardinality (2R+1)^d, no-aliasing test 2R<n, finite torus and refinement family have the intended types without relying on an informal real-parameter reading. No new parameter inconsistency was found.

### O3: classical attribution and gauge-RG context — resolved at the requested scope

**Locations:** Section 1, pages 1-2; Section 7 opening, page 6; references [3]-[5], page 8.

Albert (1969) and Carlson-Haynsworth-Markham (1974) are now cited for pseudoinverse/singular-Schur background. Section 7 identifies its fixed-map formulation as the classical range condition expressed through boundedness below on observation fibers and disclaims a new general matrix criterion. The completed-square proof remains present, so correctness does not rest on a citation alone.

The added Dimock paragraph concerns an abelian covariant axial-gauge/block-averaging setting, distinguishes unit-spacing volume from small-spacing scaling, and explicitly declines to identify this unrestricted flat form with all constrained fluctuation forms. It does not claim to refute classical gauge-fixed estimates. This restores the relevant primary-source context without pretending to reproduce Balaban's whole programme.

The new bibliography uses the correct previously verified identifiers: Albert DOI 10.1137/0117041, Carlson et al. DOI 10.1137/0126013, and Dimock arXiv:1410.2798v2. My literature verification remains limited: Albert publisher bibliography, Carlson publisher abstract/bibliography, and Dimock introduction/gauge context. I have not read Albert's full article, do not assert exact line-by-line matching to either classical original, and have not performed an exhaustive priority search. The response-to-review correctly discloses these limits. This resolves the missing-attribution objection, not the broader question of whether a journal will consider the concrete formalized package sufficiently original.

Primary sources retained for this bounded assessment:

- [Albert, publisher record](https://epubs.siam.org/doi/10.1137/0117041).
- [Carlson, Haynsworth and Markham, publisher abstract](https://epubs.siam.org/doi/10.1137/0126013).
- [Dimock, author manuscript](https://arxiv.org/html/1410.2798v2).

No new literature search was necessary to check these specific corrections, and no new priority claim is inferred from adding references.

### O4: precise consumer and reproduction map — resolved as a presentation/source-identification defect

**Locations:** Section 8, pages 6-7; Section 9, page 7; corrected declaration-map.json.

Section 8 now explicitly notes the negative perturbation shell, specializes all perturbations and summable majorants to zero, takes a>0 and CP>0, and calls min(1,a)/CP an available certified lower bound rather than the optimum. It identifies the module and precision declaration. The map supplies the full theorem name, namespace, exact source SHA, file URL and specialization:

`flatGaugeFixedPrecisionCLM`

`flatGaugeFixedPrecision_coerciveWithPositiveConstant_of_flatPoincare`

at `e31b428917aa767b4a1aad097db5cf92fb9cd23e` in `YangMills/RG/PhysicalGaugeFixedPrecision.lean`.

The reread source has lower bound min(1,a)/CP - sum_i delta_i and assumptions summability, ||Sigma_i||<=delta_i, and a strict budget. Setting all Sigma_i and delta_i to zero makes the norm bound and summability immediate and the budget 0<min(1,a)/CP follows from a,CP>0. Thus the claimed base specialization is mathematically correct. It is explicitly source-level reasoning, not a newly compiled Lean adapter.

The paper now links the [exact corrected map](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/7ab9a61c060d07a5a7a08081115981e47684a39a/papers/flat-coarse-rank/declaration-map.json), [repository](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME), and [preserved reproduction tree](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/tree/e31b428917aa767b4a1aad097db5cf92fb9cd23e/reproducibility). The map's exact URL successfully returned the corrected contents through the GitHub fetch tool. I did not download or rebuild the full evidence tree or test every linked notebook. Consequently access/source identification is repaired; O6 remains unaffected.

### O5: historical retention qualification — resolved

**Locations:** Section 3 opening, page 2; restored context in Section 1, pages 1-2.

The paper now claims retention of the principal results, explicitly says the historical Appendix A square-wave witness remains in v1 and is not reproduced here, and gives its quotient 8/ell. This matches the previously reviewed historical appendix. The principal constant-sector, transverse-kernel, energy, spectral-multiplicity, arbitrary-factorized-penalty, repair, liminf, witness-line and leakage results remain present in Section 3. The restored gauge-RG discussion also addresses the contextual omission.

The historical PDF and previous report were not edited. This corrected wording does not suggest that every sentence or weaker precursor of the historical version has been reproduced.

### O6: independent formal verification limit — retained, not solved by disclosure

**Locations:** Section 9, page 7; model/review-context disclosure, page 8.

The new disclosure accurately states that the reviewer did not rebuild Lean or audit the complete evidence/dependency closure and that reproduction statements describe supplied records. This appropriately prevents my reading review from being marketed as independent formal reproduction. It does not independently verify those records, and must not be summarized as having resolved that evidential limitation.

The analytic fixed-map proposition, counterexample, source consumer specialization, spectral/asymptotic historical conclusions and general-dimensional historical calculations remain distinct from the advertised formal endpoints. Old dimension-four formal evidence remains separately anchored at `7b25bfb39357406cf61880e3ac0428d7d1ba3449`; new physical-band/uniform evidence uses `e31b428917aa767b4a1aad097db5cf92fb9cd23e` with its tested-stage SHAs. No inference is made that the absent old modules became part of the new main source merely because reproductions exist there.

## Principal mathematics rechecked on the corrected text

**Flat normalization and block witness, Sections 2-3, pages 2-4.** The two-internal-coordinate embedding is real-linear and isometric. Unordered plaquettes contribute one transverse difference each and divergence contributes the remaining direction, giving exactly the unit-spacing stencil energy. The block character is periodic on side ell N', its transverse block sum vanishes, its divergence is zero, and its energy/norm quotient is 4 sin^2(pi/ell). The constant-sector powers and necessary sigma threshold are correct. Testing any factorized penalty at coarse zero yields CP>=ell^2/(4 pi^2). Higher-frequency and derivative Gram orthogonality justify the 2R-dimensional min-max bound. The changed-map/fine-term quotient, finite necessary budget, liminf and restriction to a single witness line remain correct and correctly limited.

**Constructed band, Lemma 4.1, page 4.** Integer R and 2R<n give an injective complex synthesis of B characters. Real dimension is 2B because real and imaginary coefficients are stored independently in two internal coordinates, with no conjugate-symmetry constraint. Parseval applies both to mass and derivative amplitudes. The estimate |exp(it)-1|<=|t| produces 4 pi^2 d R^2/n^2 for every linear combination. R=0 gives two constant directions and zero energy, consistently.

**Finite budget and sectors, Theorem 5.1 and Proposition 5.2, pages 4-5.** Applying rank-nullity to (C,V) on the constructed band gives a nonzero vector killed by both maps when dim F+rank V<2B. No positivity or symmetry of V is needed because VA=0. The strict comparison c>b_R is essential and present. Applying the same argument directly to (C,P) gives a vector in ker P; no invalid inference from full-space failure is used. The numerical example 162 versus 12+149=161 is correct. These are necessary budgets, not sufficiency criteria.

**Uniform quantifiers, Theorem 6.1, page 5.** F and r are fixed first; C_L,V_L,Phi_L may vary with L within the stated hypotheses. After proposing c>0, choose R=dim F+r+1 and then large enough L. The displayed finite choice L>max{2R,a/c,1} ensures both no aliasing and b_R(n_L)<c. Arbitrary linear-map norms or scalar rescalings do not affect the kernel argument. Bounded-rank linear constraints are covered directly; arbitrary growing-rank gauge constraints and quotient norms are not.

**Singular fixed-map criterion, Proposition 7.1, page 6.** Restriction to ker C forces A>=0. Varying tz+w with z in ker A at fixed Cw forces ker A subset ker D*. This is equivalent in finite dimensions to range D subset range A. Completion of the square with A-dagger proves sufficiency; extending the inverse of C on W supplies the quadratic penalty. A large nonnegative norm-square penalty also works with a fixed Euclidean norm on F. No uniform bound over changing maps is asserted. The example diag(0,2), c=1, C(x,y)=x+y still yields 1-2t+Phi(1) and is valid.

**Scaling and consumer, Section 8, pages 6-7.** Multiplying K0 by ell^2 changes this band's threshold to 4 pi^2 d R^2/(N')^2, so the proof no longer drives it below an arbitrary c. This is only an escape from this proof. The text does not turn it into a positive coercivity theorem. The inspected fixed-volume source does not claim a uniform CP, so there is no contradiction with its finite-volume positivity. Interaction, Wilson-Hessian identification, localization constants, continuum measures and mass gap remain outside the result.

No newly inserted statement invalidates these arguments. There is no need to manufacture a new mathematical objection merely because the previous ones have been addressed.

## Correctness, originality and relevance remain separate

**Correctness:** the narrow analytic claims are supported by their displayed proofs in this exact artifact; the material abstract overbreadth is corrected. No mathematical blocker found in this reading/correction assessment. Full formal-evidence validation is still outside the work performed.

**Originality:** the revised attribution is scientifically more accurate, but does not increase the novelty of the classical Fourier/rank-nullity/min-max/Schur arguments. The concrete normalization, programme diagnosis and formal realization are the potential contribution. Exact priority and publication significance remain unsettled; no new-general-theorem claim is justified.

**Relevance:** the result constrains a particular unscaled flat route and finite-dimensional linear repair mechanisms. It does not establish an interacting theory, provide physical positive coercivity, resolve arbitrary gauge sectors, or prove a continuum Yang-Mills mass gap. The revised text preserves these limitations. PR98's weighted derivative theorem is explicitly excluded from this report and cannot inherit this assessment.

## Model assessments and review context

This is the same reviewer agent continuing the authorized exact-artifact review to check substantive corrections. I had no role in drafting the original manuscript, but I did supply the previous objections and therefore have prior review involvement in the correction cycle. I did not edit this corrected manuscript. This distinction is important: this follow-up is not a fresh blind assessment.

The configured model requested by the original spawn/delegation was `gpt-6-astra`. Actual served backend identity and reasoning setting were not exposed to this reviewer and are not inferred. A requested model name and a model's own assertion are not backend telemetry. The workflow remains in the same orchestrated chat, account and provider (OpenAI/Codex) as preparation. There is no organizational independence, blind-review claim or human peer review. Any operator-visible service telemetry should be retained separately.

This follow-up was explicitly limited to substantive corrections, without a target grade or replacement of the earlier report. The earlier negative scope finding remains part of the immutable record for its old artifact. This new report applies only to the hash identified above. It does not authorize submission, editorial acceptance, publication, or reuse as review of future modified PDFs.

## Input and output record

Inputs for this follow-up included:

- Corrected delivery folder: `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-corrected`, specifically `flat_coarse_rank.pdf`, `flat_coarse_rank.tex`, `declaration-map.json`, and `RESPONSE-TO-REVIEW-024.md`.
- Render evidence: `D:\Datos\the-eriksson-programme\autonomia\evidencia-025\render026.zip` and extracted `render026\manifest.json`, `report.json`, and `page-1.jpg` through `page-8.jpg`; all 28 manifest entries were hash-checked.
- Prior objection record: `D:\Datos\the-eriksson-programme\autonomia\evidencia-024\astra-review\scientific-review.md` retained in this reviewer context and re-hash-checked, with `summary.json` reread. These were a record of objections, not automatic approval of the corrected artifact.
- Prior TeX `D:\Entregas\the-eriksson-programme\2026-10-30_flat-wall-integrated\flat_coarse_rank.tex`, used only to identify the substantive changes.
- Read-only Git objects in `D:\Proyectos\the-eriksson-programme`: corrected map at `7ab9a61c060d07a5a7a08081115981e47684a39a`, consumer source at `e31b428917aa767b4a1aad097db5cf92fb9cd23e`, and manuscript opening at `77b8ec265dea2bd6b3e6c9ffe85e02b423a9e00b`.
- Exact corrected-map GitHub URL listed above, successfully fetched read-only.
- Previously read D:\LEEME.md and PDF skill instructions remain applicable; no new artifact authoring, rendering or compiler workflow was invoked.

Outputs are only this new report and its new machine-readable summary in `D:\Datos\the-eriksson-programme\autonomia\evidencia-025\astra-review-corrections`. The old assessment and every manuscript artifact were preserved unchanged.
