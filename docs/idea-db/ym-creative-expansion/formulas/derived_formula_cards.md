# Derived formula cards

**Important:** every card here is an experimental or governance candidate unless its status explicitly says `verified_formula_atom` in `repo_sources/source_atoms.json`. Do not cite these as literature or as proved Lean theorems.


## D01.YMActivityBudget.min_exponent_triangle — YM activity error-budget triangle: source H# plus dictionary defects
- status: `experimental_derived_formula`
- provenance atoms: `riemann.error_budget`, `dimock.appendixF_holes`, `ym.frontier.hRpoly`
- formula ASCII: `If |H_src#(Y)|<=A0*exp(-eta0*d(Y)) and |H_YM#(Y)-H_src#(Y)|<=sum_i Ai*exp(-etai*d(Y)), then |H_YM#(Y)| <= (A0+sum_i Ai)*exp(-min_i eta_i * d(Y)).`
- formula LaTeX: `|H^\#_{YM}(Y)|\le(A_0+\sum_i A_i)e^{-\eta_*d(Y)},\quad \eta_*=\min(\eta_0,\eta_1,\ldots)`
- why it matters: Turns a vague “physical-to-source dictionary” into separately provable covariance, Gaussian, support and Jacobian defects. It is a safe Lean theorem and a strong audit device.
- proof route: Pure triangle inequality and exp monotonicity; no source paper needed. Then instantiate fields one by one.
- blockers: Define exact YM/source H# comparison terms, Prove each defect has decay
- risk: low as bookkeeping; high if agents silently set all defects to zero.
- proposed Lean declarations: `YMActivityErrorBudget`, `activity_decay_of_source_and_budget`, `activity_budget_total_nonneg`

## D02.power_lifted_coupling_tail — Power-lifted coupling summation: keep r^kappa when possible
- status: `experimental_derived_formula`
- provenance atoms: `ym.frontier.hRpoly`
- formula ASCII: `If 0<=g_k<=C*r^k, 0<r<1 and p is a positive natural/integer exponent, then g_k^p <= C^p*(r^p)^k and sum_k A*e^{-c*t}*g_k^p <= A*C^p*(1-r^p)^(-1)*e^{-c*t}.`
- formula LaTeX: `\sum_k Ae^{-ct}g_k^p\le AC^p(1-r^p)^{-1}e^{-ct}`
- why it matters: The current assembled theorem already closes with a geometric profile; this sharper variant may improve constants when κ₀ is a natural exponent and r^κ₀ is admissible.
- proof route: Use pow_le_pow_left₀ and finite/infinite geometric sum with base r^p.
- blockers: κ₀ in current theorem is real; create Nat-specialized endpoint or bridge real κ₀ to Nat
- risk: medium; only a constant/rate refinement, not hRpoly itself.
- proposed Lean declarations: `coupling_power_geometric_decay_nat`, `hUV_of_per_scale_power_tail`, `lattice_mass_gap_of_cluster_and_power_coupling`

## D03.prime_tail_style_rg_tail — Prime-tail closed majorant as a late-scale RG tail template
- status: `experimental_derived_formula`
- provenance atoms: `riemann.resolvent_tail_rate`, `ym.frontier.hRpoly`
- formula ASCII: `For 0<r<1 and polynomial prefactor k^m, sum_{k>=K} k^m*r^k <= r^K * P_m(K)/(1-r)^(m+1). Use this as the RG analogue of X^{-delta}(log X/delta+1/delta^2).`
- formula LaTeX: `\sum_{k\ge K}k^m r^k\le r^K\,P_m(K)/(1-r)^{m+1}`
- why it matters: Many source bounds hide polynomial-in-scale factors in O(1). This gives a finite, audit-friendly way to avoid absorbing them too early.
- proof route: Start with m=1,2 by differentiating finite geometric sums or using induction k^m <= C_m,K a^k for any a>1.
- blockers: Choose exact polynomial prefactors from Balaban/Dimock source constants
- risk: low for toy lemma; medium for source instantiation.
- proposed Lean declarations: `geometric_tail_with_linear_prefactor`, `geometric_tail_with_quadratic_prefactor`, `rg_tail_majorant_of_poly_prefactor`

## D04.covariance_root_stieltjes_resolvent — Covariance-root localization by Stieltjes/resolvent integral
- status: `experimental_derived_formula`
- provenance atoms: `riemann.resolvent_tail_rate`, `dimock.green_resolvent_decay`, `ym.frontier.hRpoly`
- formula ASCII: `For finite SPD K, K^(-1/2) = (1/pi)*integral_0^infty s^(-1/2)*(K+sI)^(-1) ds. If resolvent kernels decay uniformly/integrably, then the covariance-root kernel decays.`
- formula LaTeX: `K^{-1/2}_{xy}=\pi^{-1}\int_0^\infty s^{-1/2}(K+sI)^{-1}_{xy}ds`
- why it matters: The repo already has exact covariance from coercivity and carries root localization as source input. This gives a finite-dimensional toy theorem route that connects Dimock Green resolvents with the Riemann resolvent positivity style.
- proof route: First prove a spectral finite-matrix theorem for diagonal matrices; then self-adjoint diagonalization; then kernel bound via integral majorant.
- blockers: Mathlib spectral calculus ergonomics, uniform decay constants for (K+sI)^(-1), field/bond dictionary
- risk: high but genuinely creative and potentially high payoff.
- proposed Lean declarations: `spd_root_as_resolvent_integral_toy`, `kernel_decay_of_resolvent_integral_toy`, `physical_root_localization_of_resolvent_family`

## D05.random_walk_green_to_root_pipeline — Dimock random-walk Green expansion as root-localization producer
- status: `experimental_derived_formula`
- provenance atoms: `dimock.green_resolvent_decay`, `D04.covariance_root_stieltjes_resolvent`
- formula ASCII: `C=A+a^2*A*Q*G*Q^T*A and G=sum_omega G_omega with |G_omega| localized. Combine finite-range A,Q with D04 to produce root kernel localization certificate.`
- formula LaTeX: `C=A+a^2AQGQ^TA,\quad G=\sum_\omega G_\omega\Rightarrow |C^{1/2}_{xy}|\lesssim e^{-m d(x,y)}`
- why it matters: Targets the exact open source hypothesis `PhysicalLocalizedCovarianceRootCertificate.root kernel localization` instead of adding another consumer.
- proof route: Lean finite support calculus: finite-range A/Q composition loses a bounded radius; Green expansion supplies exponential decay; root integral supplies square-root.
- blockers: prove/cite gauge precision resolvent identity, finite support radius of Q/A in physical gauge layer
- risk: high; do as toy finite theorem first.
- proposed Lean declarations: `finite_range_composition_preserves_kernel_decay`, `green_random_walk_sum_kernel_decay`, `covariance_root_certificate_of_green_resolvent_decay`

## D06.eq231_admissible_automaton — Eq. (2.31) P-family as a finite admissibility automaton
- status: `experimental_derived_formula`
- provenance atoms: `cmp116.eq231.p_stage`, `physmath.research_moves`
- formula ASCII: `P in PIndex(Z,D) iff P subset gapCubes(Z,D) x Fin4 and admissible(Z,D,P)=true, where admissible is decomposed into local endpoint, positive-orientation and no-duplicate constraints.`
- formula LaTeX: `P\in\mathcal P(Z,D)\iff P\subseteq Gap(Z,D)\times\{0,1,2,3\}\land Adm(Z,D,P)`
- why it matters: This is the highest source-honesty payoff: it discharges carrier containment and unlocks existing Eq. (2.31) consumers without adding more wrappers.
- proof route: Make `admissible` a Bool conjunction of finite local predicates; prove membership iff by unfolding; separately prove source dictionary from CMP116/CMP109 text.
- blockers: exact CMP116 P definition, CMP109 positive bond convention to Fin4, carrier count <= 4*|gap|
- risk: medium; high payoff because it removes a live source hypothesis.
- proposed Lean declarations: `CMP116Eq231SourcePIndexMemIff`, `cmp109PositiveOrientationCarrier`, `cmp116Eq231_admissible_of_sourceP`, `sourceP_of_cmp116Eq231_admissible`

## D07.eq231_lower_cardinality_boost — Eq. (2.31) entropy boost from |P| lower bound
- status: `experimental_derived_formula`
- provenance atoms: `cmp116.eq231.p_stage`
- formula ASCII: `If each source P satisfies |P| >= lambda*gapMass, then sum_{P admissible} exp(-rho*gapMass)*exp(-2*rho*|P|) <= exp(-((rho+2*rho*lambda)-4*M^4*exp(-2*rho))*gapMass). For lambda=1/2 this doubles the useful rho term.`
- formula LaTeX: `\sum_P e^{-\rho G}e^{-2\rho |P|}\le e^{-((\rho+2\lambda\rho)-4M^4e^{-2\rho})G}`
- why it matters: The source database records a visual lower bound |P| >= 1/2 M^{-4}|Z0\Y0|. If it is part of the same summation lane, it may give a stronger P-stage margin.
- proof route: Extract q^m from the powerset sum: sum_{S subset B, m<=|S|} q^|S| <= q^m(1+q)^|B|, then exp-bound.
- blockers: source confirmation that lower bound applies to exactly the P family being summed, define gapMass/cardinality relation
- risk: medium; possible mismatch of source lower bound context.
- proposed Lean declarations: `cmp116PGeometricFamilySummation_of_eq231_with_cardLowerBound`, `cmp116Eq231_entropy_margin_cardLowerBound`

## D08.eq231_catalan_admissible_entropy — Replace powerset entropy by Catalan/forest entropy for structured admissible P
- status: `speculative_derived_formula`
- provenance atoms: `cmp116.eq231.p_stage`, `tree.catalan_identity`, `tree.target_preserving_bound`
- formula ASCII: `If admissible P is encoded by rooted forests/skeletons with n bonds and target-preserving fibers bounded by Catalan(n), then sum_P q^|P| <= sum_n Catalan(n)*(A*q)^n = C(A*q)-1 for A*q<1/4.`
- formula LaTeX: `\sum_{P\,adm}q^{|P|}\le\sum_n C_n(Aq)^n=\frac{1-\sqrt{1-4Aq}}{2Aq}-1`
- why it matters: Could relax the brutal 2^carrier entropy if P is much more structured than arbitrary subsets. This is out-of-the-box and must be tested with finite examples before source use.
- proof route: Start with toy finite gap graphs. Enumerate admissible P for small gaps, compare with powerset and Catalan counts. Only then attempt Lean statement.
- blockers: source P may be arbitrary finite bond subset, not forest-like, Catalan identity general Lean proof still open in separate artifact
- risk: high/speculative; keep outside source DB.
- proposed Lean declarations: `admissibleP_forestEncoding_toy`, `eq231_catalan_entropy_bound_toy`, `sourceP_catalan_not_powerset_counterexample_search`

## D09.eq237_metric_stitching_product_extraction — Post-P product metric extraction using Dimock metric stitching
- status: `experimental_derived_formula`
- provenance atoms: `cmp116.eq237.post_p`, `dimock.appendixF_holes`
- formula ASCII: `If d(Y)<=sum_i d(X_i)+(n-1) and b>=0, then prod_i exp(-b*d(X_i)) <= exp(-b*d(Y))*exp(b*(n-1)). Absorb exp(b*(n-1)) into the n-component entropy/generating function.`
- formula LaTeX: `\prod_i e^{-bd(X_i)}\le e^{-bd(Y)}e^{b(n-1)}`
- why it matters: This is the exact algebraic heart of Eq. (2.37) final summation: extract the target decay before losing component structure.
- proof route: Pure real inequality from Dimock Eq. (641). Prove once, reuse in Eq. (2.37) and Appendix-F H# lanes.
- blockers: exact metric dictionary d_k/d_{k+1}/modified metric, component union theorem
- risk: low for algebra; medium for source dictionaries.
- proposed Lean declarations: `exp_metric_product_le_of_stitching`, `cmp116Eq237_componentProduct_extracts_targetDecay`, `appendixF_metricStitching_exponentBudget`

## D10.eq237_catalan_second_ursell_closure — Eq. (2.37) final sum through Catalan second-Ursell generating function
- status: `experimental_derived_formula`
- provenance atoms: `cmp116.eq237.post_p`, `tree.target_preserving_bound`, `tree.catalan_identity`, `dimock.appendixF_holes`
- formula ASCII: `After D09, the n-component contribution has shape Catalan(n)*(A*K0*exp(b))^n*exp(-b*d(Y)). If A*K0*exp(b)<1/4, close by the Catalan generating function and keep exp(-b*d(Y)).`
- formula LaTeX: `\sum_n C_n(AK_0e^b)^n e^{-bd(Y)}=\mathcal C(AK_0e^b)e^{-bd(Y)}`
- why it matters: This merges the Catalan closure repo with Dimock Appendix F to attack the final post-(2.37) summation rather than just indexing it.
- proof route: First use existing 4^n endpoint; then replace by conditional Catalan endpoint when RootedChildFactorialCatalanIdentity is proved or assumed explicitly.
- blockers: general Catalan identity proof, exact component count-to-tree mapping, smallness A*K0*exp(b)<1/4
- risk: medium-high; potentially useful for constants and proof search.
- proposed Lean declarations: `catalanGeneratingBound_of_small`, `cmp116Eq237_finalSummation_catalanToy`, `appendixFSecondUrsell_catalanClosure_sourceShape`

## D11.loss_ledger_algebra — Unified loss ledger for Balaban/Dimock exponents
- status: `experimental_derived_formula`
- provenance atoms: `dimock.cluster_standard_loss`, `dimock.appendixF_holes`, `cmp116.eq237.post_p`
- formula ASCII: `Represent every source step as eta_out = scale*eta_in - loss, e.g. kappa -> kappa-3*kappa0-3, kappa -> kappa-kappa0-2, L*kappa -> L*(kappa-6*kappa0-6). Compose losses mechanically.`
- formula LaTeX: `\eta_{out}=a\eta_{in}-\ell`
- why it matters: Stops agents from mixing incompatible κ, κ₀, L and δ exponents. A small Lean/file-level algebra layer can check positive-margin obligations before analytic work.
- proof route: Finite list fold over affine maps eta ↦ a*eta-loss; prove monotonicity and positivity conditions.
- blockers: fill exact source constants per lane
- risk: low; high practical value for planning.
- proposed Lean declarations: `ExponentLossStep`, `ExponentLossChain.margin`, `positive_margin_of_chain`

## D12.target_preserving_fiber_before_overcount — Keep exact union/target fibers before overcounting
- status: `experimental_derived_formula`
- provenance atoms: `tree.target_preserving_bound`, `physmath.research_moves`, `dimock.appendixF_holes`
- formula ASCII: `For fixed target Y, keep Fib(Y,n)={(Y1,...,Yn): union Yi=Y and Omega-connected}; prove metric extraction on Fib(Y,n) before mapping to rooted trees or cardinality bounds.`
- formula LaTeX: `\mathrm{Fib}(Y,n)=\{(Y_i):\cup_iY_i=Y,\Omega\text{-connected}\}`
- why it matters: Prevents target erasure. This is exactly the pattern that made rooted-tree target-preserving summation valuable.
- proof route: Define finite sigma/fiber index; prove equality of nested sum and fiber sum; only then apply tree overcount.
- blockers: finite source-to-Lean fiber dictionary, Ursell coefficient convention
- risk: low-medium; mostly bookkeeping but can be hard Lean engineering.
- proposed Lean declarations: `AppendixFExactUnionFiber`, `metric_extracts_before_target_forget`, `fiber_sum_le_tree_overcount_after_decay`

## D13.ward_defect_before_norms — Gauge/Ward cancellation before absolute-value majorization
- status: `speculative_derived_formula`
- provenance atoms: `physmath.research_moves`, `ym.core.area_ir`
- formula ASCII: `Decompose H = H_exact_cancel + d_W B + Def. If integral(d_W B * weight)=0 and |Def(X)|<=D0*exp(-eta*d(X)), then activity is controlled by the defect rather than the full naive norm.`
- formula LaTeX: `H=H_{cancel}+d_WB+Def,\quad |H_{eff}(X)|\le D_0e^{-\eta d(X)}`
- why it matters: A possible route for raw YM activity: avoid destroying gauge/center cancellations by taking norms too early.
- proof route: Start finite: signed sum over a finite group action with invariant measure; show exact sector integrates to zero and bound defect.
- blockers: actual differentiable/gauge Ward identity for lattice variables, boundary/regulator defect control
- risk: high/speculative but worth a toy finite theorem.
- proposed Lean declarations: `finiteWardCancellation_toy`, `wardDefectActivityBound_toy`, `centerChargeCancellation_before_norm`

## D14.separator_collar_covariance_split — Condition on a collar/separator to localize covariance defects
- status: `experimental_derived_formula`
- provenance atoms: `physmath.research_moves`, `dimock.green_resolvent_decay`
- formula ASCII: `Split field variables into A | collar S | B. If precision K_AB=0 conditional on S, covariance cross terms are carried by Schur-complement/collar defects; residual <= C*exp(-gamma*width(S)).`
- formula LaTeX: `\|C_{AB}^{defect}\|\le Ce^{-\gamma\,width(S)}`
- why it matters: Could localize the physical covariance/root certificate by finite Markov-blanket identities before using random-walk decay.
- proof route: Finite SPD block matrix theorem: if K_AB=0, conditional independence; perturbation bound when K_AB small.
- blockers: gauge constraints may make Schur complement dense, exact block support of K
- risk: medium-high; good finite counterexample generator.
- proposed Lean declarations: `threeBlockGaussianConditionalIndependence_toy`, `schurComplement_collar_defect_bound_toy`

## D15.continuum_guardrail_M3_not_Clay — Hard guardrail: M3 lattice gap is not continuum Clay
- status: `governance_formula`
- provenance atoms: `ym.frontier.hRpoly`, `ym.core.area_ir`
- formula ASCII: `M3_discharge => unconditional lattice mass gap only. Clay requires continuum limit + OS/Wightman reconstruction + positive physical mass gap; none may be inferred from hRpoly alone.`
- formula LaTeX: `M3\not\Rightarrow M5\quad\text{without continuum construction and reconstruction}`
- why it matters: Prevents agents from turning creative formula search into false theorem claims.
- proof route: Documentation/governance, not mathematical proof.
- blockers: None
- risk: low and mandatory.
- proposed Lean declarations: `NoLeanNeeded_claim_boundary_in_docs`
