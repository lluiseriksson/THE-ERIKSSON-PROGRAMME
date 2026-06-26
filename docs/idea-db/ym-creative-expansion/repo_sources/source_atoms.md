# Source atoms used by the creative formula pack

Generated: 2026-06-26

These are compact atoms extracted from repository files and metadata. They are not a replacement for source PDFs or Lean verification.

## ym.frontier.hRpoly
- repo: `the-eriksson-programme`
- status: `repo_statement`
- summary: The verified core carries no project axiom; the live M3 UV input is hRpoly, the concrete YM cluster-expansion-with-holes remainder/activity bound.
- formula: `|Rsc(t,k)| <= A*exp(-c0*t)*g_k^kappa0`
- Lean refs: `YangMills.RG.lattice_mass_gap_of_cluster_and_coupling`, `YangMills.RG.lattice_mass_gap_of_cluster_and_logistic_coupling`
- source refs: HYPOTHESIS_FRONTIER.md:28-45, YangMills/RG/UVMassGap.lean:79-140
- do-not-use-as: Do not treat M3 as Clay; continuum/OS reconstruction remains separate.

## ym.core.area_ir
- repo: `the-eriksson-programme`
- status: `repo_statement`
- summary: Strong-coupling/KP/area-law and IR side are theorem-fed; hRpoly remains the UV source producer.
- formula: `normalized Wilson loop <= Nc * exp(perimeter terms) * sigma^Area(C)`
- Lean refs: `normalized_wilson_loop_area_law`, `finite_volume_area_law_exp`, `gibbs_truncated_correlation_bound`
- source refs: README.md:150-201, CURRENT-STATE.md:76-100
- do-not-use-as: Do not use strong-coupling lattice confinement as continuum mass-gap proof.

## cmp116.eq229.d_stage
- repo: `the-eriksson-programme`
- status: `visual_confirmed_or_lean_encoded`
- summary: CMP116 Eq. (2.29) D-family product summability shape.
- formula: `sum_D prod_{Y in D} alpha6 * exp(-delta*kappa*d_k(Y)) <= 1`
- Lean refs: `CMP116Eq229Summability`, `cmp116Eq229Weight`, `cmp116_DStage_sum_le_of_eq229`
- source refs: YangMills/RG/BalabanCMP116Eq229.lean:34-58, docs/source-db/examples/cmp116-current-seed.json:93-104
- blockers: Cammarota CMP85 theorem extraction, D-family dictionary and thresholds

## cmp116.eq231.p_stage
- repo: `the-eriksson-programme`
- status: `visual_confirmed_or_lean_encoded`
- summary: CMP116 Eq. (2.31) P-bond entropy boundary and filtered PIndex interface.
- formula: `rho=gamma2*epsilon1^2/(20*gk^2); sum_P exp(-rho*gapMass)*exp(-2*rho*|P|) <= 1 if 4*M^4*exp(-2*rho)<=rho`
- Lean refs: `cmp116Eq231SourcePIndex`, `cmp116Eq231SourcePIndex_mem_iff`, `CMP116Eq231PBondBoundary.of_sourcePIndexMemIff`, `cmp116PGeometricFamilySummation_of_eq231`
- source refs: YangMills/RG/BalabanCMP116Eq231.lean:33-96, YangMills/RG/BalabanCMP116Eq231.lean:250-360, docs/source-db/examples/cmp116-current-seed.json:106-136
- blockers: P-family source membership iff, positive-orientation carrier convention, pointwise P-residual majorization

## cmp116.eq237.post_p
- repo: `the-eriksson-programme`
- status: `visual_confirmed_or_lean_encoded`
- summary: CMP116 Eq. (2.37) fixed-Z0 prime weight, finite reindexing, and post-P source bound consumer.
- formula: `W(Z,Z0p)=exp(-((kappa1-1)*M^-4*gap))*prod_i(A237*exp(-b*metric_i))*exp(Calpha5*alpha5*|Z|)`
- Lean refs: `cmp116Eq237FixedZ0PrimeWeight`, `cmp116PostPResidualSourceBound_of_eq237`, `cmp116PostPResidualSourceBound_of_eq237_globalIndex`
- source refs: YangMills/RG/BalabanCMP116Eq237.lean:183-228, YangMills/RG/BalabanCMP116Eq237.lean:58-108
- blockers: fixed-Z0 prime source estimate, final Z0 prime summation, source dictionary for global index

## dimock.cluster_standard_loss
- repo: `the-eriksson-programme`
- status: `source_extracted`
- summary: Dimock standard cluster theorem: input activity decay produces H# with decay loss 3*kappa0+3.
- formula: `|H(X)|<=H0*exp(-kappa*d_M(X)) => |H#(Y)|<=O(1)*H0*exp(-(kappa-3*kappa0-3)*d_M(Y))`
- Lean refs: `AppendixFSecondUrsellClosure`, `AppendixFHsharpLeafSource`
- source refs: docs/source-db/catalogs/dimock-rg-i-iii-extracted.json:10-77
- blockers: ordinary-vs-holes metric dictionary, finite connected-cover entropy constants

## dimock.green_resolvent_decay
- repo: `the-eriksson-programme`
- status: `source_extracted`
- summary: Dimock resolvent/random-walk source formulas for covariance/Green localization.
- formula: `C_(k,r)=A_(k,r)+a_k^2*A_(k,r)*Q_k*G_(k,r)*Q_k^T*A_(k,r); G_k=sum_omega G_(k,omega); |G_k f|<=C exp(-(gamma0/2)d)||f||_inf`
- Lean refs: `PhysicalLocalizedCovarianceRootCertificate`, `CovarianceKernel`, `KernelDecay`
- source refs: docs/source-db/catalogs/dimock-rg-i-iii-extracted.json:80-139, docs/source-db/catalogs/dimock-rg-i-iii-extracted.json:300-360
- blockers: physical gauge operator dictionary, root localization proof

## dimock.appendixF_holes
- repo: `the-eriksson-programme`
- status: `source_extracted`
- summary: Dimock Appendix F with holes: metric stitching, first K activity, K# ultralocal integration, second Ursell H#.
- formula: `d_M(Y mod Omega^c)<=sum_i d_M(X_i mod Omega^c)+(n-1); |K(Y)|<=O(1)H0 exp(-(kappa-kappa0-2)d_M(Y)); H#(Y)=sum_{n>=1}1/n! sum_{union Yi=Y} rho^T prod K#(Yi)`
- Lean refs: `appendixFHoleCoverUnion_discreteModifiedMetric_add_one_le_sum`, `AppendixFSecondUrsellClosure`
- source refs: docs/source-db/catalogs/dimock-rg-i-iii-extracted.json:575-760
- blockers: connected cover entropy, measurable K/K# for physical field types

## tree.target_preserving_bound
- repo: `lean-rooted-tree-polymer-expansion`
- status: `verified_artifact`
- summary: Target-preserving rooted-tree/leaf summation closes finite tree combinatorics with 4^n bound and target-union decay retained.
- formula: `(n+1)/(n+1)! * sum_T prod_v c_T(v)! <= 4^n; T_n(Y)<=M*exp(-rho*m(Y))*L^n`
- Lean refs: `MarkedRootedClosure.normalizedRootedChildFactorialTreeBound`, `MarkedRootedClosure.targetPreservingWeightedTreeBound`
- source refs: README.md:34-63, archive/theorem-manifest.json:15-49
- blockers: not model-specific hRpoly

## tree.catalan_identity
- repo: `rooted-tree-catalan-closure`
- status: `finite_evidence_and_open_general_lean_proof`
- summary: Exact Catalan child-factorial tree identity with finite evidence and a narrow Prüfer-profile route; general Lean proof remains open.
- formula: `sum_T prod_v c_T(v)! = n! * Catalan(n)`
- Lean refs: `YangMills.KP.RootedChildFactorialCatalanIdentity`, `YangMills.RG.catalanClosure_fixedPoint`
- source refs: README.md:33-65, archive/theorem-manifest.json:5-48, docs/PRUFER_PROFILE_REDUCTION.md:16-79
- blockers: general Lean proof of RootedChildFactorialCatalanIdentity

## riemann.error_budget
- repo: `riemann-prime-resolvent`
- status: `verified_lean_bookkeeping`
- summary: Three-part deterministic error budget and componentwise convergence-to-zero package.
- formula: `|spectral-prime| <= |spectral-prolate|+|prolate-target|+|target-prime|; componentwise E_i->0 => total->0`
- Lean refs: `RiemannPrimeResolvent.ErrorBudget.total_nonneg`, `RiemannPrimeResolvent.three_step_triangle`, `RiemannPrimeResolvent.VanishingBudget.total`
- source refs: RiemannPrimeResolvent/Basic.lean:20-68, RiemannPrimeResolvent/Convergence.lean:21-42, docs/THEOREM-LEDGER.md:11-18
- blockers: analogy only; must instantiate with YM quantities

## riemann.resolvent_tail_rate
- repo: `riemann-prime-resolvent`
- status: `verified_lean_bookkeeping`
- summary: Finite Stieltjes/resolvent positivity, closed prime-tail majorant and candidate rate exponent.
- formula: `primeTailMajorant(delta,X)=exp(-delta*log X)*(log X/delta+1/delta^2); rateExponent(q)=min((2q-1)/3,2/3)`
- Lean refs: `finiteSquaredResolvent_nonneg`, `primeTailMajorant_nonneg`, `rateExponent_pos`, `rateExponent_le_two_thirds`
- source refs: RiemannPrimeResolvent/FiniteStieltjes.lean:23-60, RiemannPrimeResolvent/PrimeTail.lean:20-49, RiemannPrimeResolvent/RateOptimization.lean:19-47
- blockers: do not import RH content; use as finite positivity/rate template only

## physmath.research_moves
- repo: `physmath-knowledge-tree`
- status: `governed_heuristic`
- summary: Research moves: renormalize, finitize, preserve exact target, eliminate tree leaves, normalize by parent kernel, close exact generating function, condition on separator, localize homotopy.
- formula: `move = {description, output, risks, lean_test}`
- Lean refs: `PhysMathKnowledgeTree.Bridge examples`, `Lean target audit queue`
- source refs: graph/research_moves.json:66-79, graph/research_moves.json:187-247, graph/research_moves.json:249-360
- blockers: heuristic, not theorem evidence
