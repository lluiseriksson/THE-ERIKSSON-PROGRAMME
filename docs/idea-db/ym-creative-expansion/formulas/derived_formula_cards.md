# Derived formula cards

These cards are experimental unless their status says otherwise. They are not source truth.


## D01.YMActivityBudget.min_exponent_triangle — YM activity error-budget triangle: source H# plus dictionary defects

**Status:** experimental_derived_formula

**Provenance:** ['riemann.error_budget', 'dimock.appendixF_holes', 'ym.frontier.hRpoly']

**Formula Ascii:** If |H_src#(Y)|<=A0*exp(-eta0*d(Y)) and |H_YM#(Y)-H_src#(Y)|<=sum_i Ai*exp(-etai*d(Y)), then |H_YM#(Y)| <= (A0+sum_i Ai)*exp(-min_i eta_i * d(Y)).

**Why It Matters:** Turns a vague “physical-to-source dictionary” into separately provable covariance, Gaussian, support and Jacobian defects. It is a safe Lean theorem and a strong audit device.

**Proof Route:** Pure triangle inequality and exp monotonicity; no source paper needed. Then instantiate fields one by one.

**Blockers:** ['Define exact YM/source H# comparison terms', 'Prove each defect has decay']

**Risk:** low as bookkeeping; high if agents silently set all defects to zero.


## D02.power_lifted_coupling_tail — Power-lifted coupling summation: keep r^kappa when possible

**Status:** experimental_derived_formula

**Provenance:** ['ym.frontier.hRpoly']

**Formula Ascii:** If 0<=g_k<=C*r^k, 0<r<1 and p is a positive natural/integer exponent, then g_k^p <= C^p*(r^p)^k and sum_k A*e^{-c*t}*g_k^p <= A*C^p*(1-r^p)^(-1)*e^{-c*t}.

**Why It Matters:** The current assembled theorem already closes with a geometric profile; this sharper variant may improve constants when κ₀ is a natural exponent and r^κ₀ is admissible.

**Proof Route:** Use pow_le_pow_left₀ and finite/infinite geometric sum with base r^p.

**Blockers:** ['κ₀ in current theorem is real; create Nat-specialized endpoint or bridge real κ₀ to Nat']

**Risk:** medium; only a constant/rate refinement, not hRpoly itself.


## D03.prime_tail_style_rg_tail — Prime-tail closed majorant as a late-scale RG tail template

**Status:** experimental_derived_formula

**Provenance:** ['riemann.resolvent_tail_rate', 'ym.frontier.hRpoly']

**Formula Ascii:** For 0<r<1 and polynomial prefactor k^m, sum_{k>=K} k^m*r^k <= r^K * P_m(K)/(1-r)^(m+1). Use this as the RG analogue of X^{-delta}(log X/delta+1/delta^2).

**Why It Matters:** Many source bounds hide polynomial-in-scale factors in O(1). This gives a finite, audit-friendly way to avoid absorbing them too early.

**Proof Route:** Start with m=1,2 by differentiating finite geometric sums or using induction k^m <= C_m,K a^k for any a>1.

**Blockers:** ['Choose exact polynomial prefactors from Balaban/Dimock source constants']

**Risk:** low for toy lemma; medium for source instantiation.


## D04.covariance_root_stieltjes_resolvent — Covariance-root localization by Stieltjes/resolvent integral

**Status:** experimental_derived_formula

**Provenance:** ['riemann.resolvent_tail_rate', 'dimock.green_resolvent_decay', 'ym.frontier.hRpoly']

**Formula Ascii:** For finite SPD K, K^(-1/2) = (1/pi)*integral_0^infty s^(-1/2)*(K+sI)^(-1) ds. If resolvent kernels decay uniformly/integrably, then the covariance-root kernel decays.

**Why It Matters:** The repo already has exact covariance from coercivity and carries root localization as source input. This gives a finite-dimensional toy theorem route that connects Dimock Green resolvents with the Riemann resolvent positivity style.

**Proof Route:** First prove a spectral finite-matrix theorem for diagonal matrices; then self-adjoint diagonalization; then kernel bound via integral majorant.

**Blockers:** ['Mathlib spectral calculus ergonomics', 'uniform decay constants for (K+sI)^(-1)', 'field/bond dictionary']

**Risk:** high but genuinely creative and potentially high payoff.


## D05.random_walk_green_to_root_pipeline — Dimock random-walk Green expansion as root-localization producer

**Status:** experimental_derived_formula

**Provenance:** ['dimock.green_resolvent_decay', 'D04.covariance_root_stieltjes_resolvent']

**Formula Ascii:** C=A+a^2*A*Q*G*Q^T*A and G=sum_omega G_omega with |G_omega| localized. Combine finite-range A,Q with D04 to produce root kernel localization certificate.

**Why It Matters:** Targets the exact open source hypothesis `PhysicalLocalizedCovarianceRootCertificate.root kernel localization` instead of adding another consumer.

**Proof Route:** Lean finite support calculus: finite-range A/Q composition loses a bounded radius; Green expansion supplies exponential decay; root integral supplies square-root.

**Blockers:** ['prove/cite gauge precision resolvent identity', 'finite support radius of Q/A in physical gauge layer']

**Risk:** high; do as toy finite theorem first.


## D06.eq231_admissible_automaton — Eq. (2.31) P-family as a finite admissibility automaton

**Status:** experimental_derived_formula

**Provenance:** ['cmp116.eq231.p_stage', 'physmath.research_moves']

**Formula Ascii:** P in PIndex(Z,D) iff P subset gapCubes(Z,D) x Fin4 and admissible(Z,D,P)=true, where admissible is decomposed into local endpoint, positive-orientation and no-duplicate constraints.

**Why It Matters:** This is the highest source-honesty payoff: it discharges carrier containment and unlocks existing Eq. (2.31) consumers without adding more wrappers.

**Proof Route:** Make `admissible` a Bool conjunction of finite local predicates; prove membership iff by unfolding; separately prove source dictionary from CMP116/CMP109 text.

**Blockers:** ['exact CMP116 P definition', 'CMP109 positive bond convention to Fin4', 'carrier count <= 4*|gap|']

**Risk:** medium; high payoff because it removes a live source hypothesis.


## D07.eq231_lower_cardinality_boost — Eq. (2.31) entropy boost from |P| lower bound

**Status:** experimental_derived_formula

**Provenance:** ['cmp116.eq231.p_stage']

**Formula Ascii:** If each source P satisfies |P| >= lambda*gapMass, then sum_{P admissible} exp(-rho*gapMass)*exp(-2*rho*|P|) <= exp(-((rho+2*rho*lambda)-4*M^4*exp(-2*rho))*gapMass). For lambda=1/2 this doubles the useful rho term.

**Why It Matters:** The source database records a visual lower bound |P| >= 1/2 M^{-4}|Z0\Y0|. If it is part of the same summation lane, it may give a stronger P-stage margin.

**Proof Route:** Extract q^m from the powerset sum: sum_{S subset B, m<=|S|} q^|S| <= q^m(1+q)^|B|, then exp-bound.

**Blockers:** ['source confirmation that lower bound applies to exactly the P family being summed', 'define gapMass/cardinality relation']

**Risk:** medium; possible mismatch of source lower bound context.


## D08.eq231_catalan_admissible_entropy — Replace powerset entropy by Catalan/forest entropy for structured admissible P

**Status:** speculative_derived_formula

**Provenance:** ['cmp116.eq231.p_stage', 'tree.catalan_identity', 'tree.target_preserving_bound']

**Formula Ascii:** If admissible P is encoded by rooted forests/skeletons with n bonds and target-preserving fibers bounded by Catalan(n), then sum_P q^|P| <= sum_n Catalan(n)*(A*q)^n = C(A*q)-1 for A*q<1/4.

**Why It Matters:** Could relax the brutal 2^carrier entropy if P is much more structured than arbitrary subsets. This is out-of-the-box and must be tested with finite examples before source use.

**Proof Route:** Start with toy finite gap graphs. Enumerate admissible P for small gaps, compare with powerset and Catalan counts. Only then attempt Lean statement.

**Blockers:** ['source P may be arbitrary finite bond subset, not forest-like', 'Catalan identity general Lean proof still open in separate artifact']

**Risk:** high/speculative; keep outside source DB.


## D09.eq237_metric_stitching_product_extraction — Post-P product metric extraction using Dimock metric stitching

**Status:** experimental_derived_formula

**Provenance:** ['cmp116.eq237.post_p', 'dimock.appendixF_holes']

**Formula Ascii:** If d(Y)<=sum_i d(X_i)+(n-1) and b>=0, then prod_i exp(-b*d(X_i)) <= exp(-b*d(Y))*exp(b*(n-1)). Absorb exp(b*(n-1)) into the n-component entropy/generating function.

**Why It Matters:** This is the exact algebraic heart of Eq. (2.37) final summation: extract the target decay before losing component structure.

**Proof Route:** Pure real inequality from Dimock Eq. (641). Prove once, reuse in Eq. (2.37) and Appendix-F H# lanes.

**Blockers:** ['exact metric dictionary d_k/d_{k+1}/modified metric', 'component union theorem']

**Risk:** low for algebra; medium for source dictionaries.


## D10.eq237_catalan_second_ursell_closure — Eq. (2.37) final sum through Catalan second-Ursell generating function

**Status:** experimental_derived_formula

**Provenance:** ['cmp116.eq237.post_p', 'tree.target_preserving_bound', 'tree.catalan_identity', 'dimock.appendixF_holes']

**Formula Ascii:** After D09, the n-component contribution has shape Catalan(n)*(A*K0*exp(b))^n*exp(-b*d(Y)). If A*K0*exp(b)<1/4, close by the Catalan generating function and keep exp(-b*d(Y)).

**Why It Matters:** This merges the Catalan closure repo with Dimock Appendix F to attack the final post-(2.37) summation rather than just indexing it.

**Proof Route:** First use existing 4^n endpoint; then replace by conditional Catalan endpoint when RootedChildFactorialCatalanIdentity is proved or assumed explicitly.

**Blockers:** ['general Catalan identity proof', 'exact component count-to-tree mapping', 'smallness A*K0*exp(b)<1/4']

**Risk:** medium-high; potentially useful for constants and proof search.


## D11.loss_ledger_algebra — Unified loss ledger for Balaban/Dimock exponents

**Status:** experimental_derived_formula

**Provenance:** ['dimock.cluster_standard_loss', 'dimock.appendixF_holes', 'cmp116.eq237.post_p']

**Formula Ascii:** Represent every source step as eta_out = scale*eta_in - loss, e.g. kappa -> kappa-3*kappa0-3, kappa -> kappa-kappa0-2, L*kappa -> L*(kappa-6*kappa0-6). Compose losses mechanically.

**Why It Matters:** Stops agents from mixing incompatible κ, κ₀, L and δ exponents. A small Lean/file-level algebra layer can check positive-margin obligations before analytic work.

**Proof Route:** Finite list fold over affine maps eta ↦ a*eta-loss; prove monotonicity and positivity conditions.

**Blockers:** ['fill exact source constants per lane']

**Risk:** low; high practical value for planning.


## D12.target_preserving_fiber_before_overcount — Keep exact union/target fibers before overcounting

**Status:** experimental_derived_formula

**Provenance:** ['tree.target_preserving_bound', 'physmath.research_moves', 'dimock.appendixF_holes']

**Formula Ascii:** For fixed target Y, keep Fib(Y,n)={(Y1,...,Yn): union Yi=Y and Omega-connected}; prove metric extraction on Fib(Y,n) before mapping to rooted trees or cardinality bounds.

**Why It Matters:** Prevents target erasure. This is exactly the pattern that made rooted-tree target-preserving summation valuable.

**Proof Route:** Define finite sigma/fiber index; prove equality of nested sum and fiber sum; only then apply tree overcount.

**Blockers:** ['finite source-to-Lean fiber dictionary', 'Ursell coefficient convention']

**Risk:** low-medium; mostly bookkeeping but can be hard Lean engineering.


## D13.ward_defect_before_norms — Gauge/Ward cancellation before absolute-value majorization

**Status:** speculative_derived_formula

**Provenance:** ['physmath.research_moves', 'ym.core.area_ir']

**Formula Ascii:** Decompose H = H_exact_cancel + d_W B + Def. If integral(d_W B * weight)=0 and |Def(X)|<=D0*exp(-eta*d(X)), then activity is controlled by the defect rather than the full naive norm.

**Why It Matters:** A possible route for raw YM activity: avoid destroying gauge/center cancellations by taking norms too early.

**Proof Route:** Start finite: signed sum over a finite group action with invariant measure; show exact sector integrates to zero and bound defect.

**Blockers:** ['actual differentiable/gauge Ward identity for lattice variables', 'boundary/regulator defect control']

**Risk:** high/speculative but worth a toy finite theorem.


## D14.separator_collar_covariance_split — Condition on a collar/separator to localize covariance defects

**Status:** experimental_derived_formula

**Provenance:** ['physmath.research_moves', 'dimock.green_resolvent_decay']

**Formula Ascii:** Split field variables into A | collar S | B. If precision K_AB=0 conditional on S, covariance cross terms are carried by Schur-complement/collar defects; residual <= C*exp(-gamma*width(S)).

**Why It Matters:** Could localize the physical covariance/root certificate by finite Markov-blanket identities before using random-walk decay.

**Proof Route:** Finite SPD block matrix theorem: if K_AB=0, conditional independence; perturbation bound when K_AB small.

**Blockers:** ['gauge constraints may make Schur complement dense', 'exact block support of K']

**Risk:** medium-high; good finite counterexample generator.


## D15.continuum_guardrail_M3_not_Clay — Hard guardrail: M3 lattice gap is not continuum Clay

**Status:** governance_formula

**Provenance:** ['ym.frontier.hRpoly', 'ym.core.area_ir']

**Formula Ascii:** M3_discharge => unconditional lattice mass gap only. Clay requires continuum limit + OS/Wightman reconstruction + positive physical mass gap; none may be inferred from hRpoly alone.

**Why It Matters:** Prevents agents from turning creative formula search into false theorem claims.

**Proof Route:** Documentation/governance, not mathematical proof.

**Blockers:** ['None']

**Risk:** low and mandatory.


## D16 — Eq231 two-sided source dictionary with explicit admissibility skeleton

**Status:** source_shape_candidate

**Provenance:** THE-ERIKSSON-PROGRAMME Eq. (2.31) + CMP116/CMP109 source keys

**Formula Ascii:** P in PIndex Z D <-> P subset gapCubes Z D x Fin4 and sourceAdmissible Z D P = true and PositiveOriented P

**Why It Matters:** It separates the carrier fact from the nontrivial admissibility content, avoiding a vacuous admissible predicate that hides the source definition.

**Proof Route:** Define a record `CMP116Eq231SourceDictionary` with fields carrier, orientation, admissibility_iff; prove existing hmem from the record.

**Blockers:** Exact Balaban P-family definition and positive bond convention.

**Risk:** medium-high: could expose missing source details rather than close them.


## D17 — Eq231 admissibility normal form as finite conjunction

**Status:** toy_lean_candidate

**Provenance:** Eq. (2.31) filtered family + research move audit_information_loss

**Formula Ascii:** admissible Z D P = true <-> carrier_ok Z D P && separation_ok Z D P && connectivity_ok Z D P && nonempty_gap_ok Z D P

**Why It Matters:** Allows builders to prove individual source-package fields instead of a monolithic iff.

**Proof Route:** Make a Boolean normal-form record and prove projection lemmas. Later map each boolean to a source paragraph.

**Blockers:** Need decide actual admissibility components from CMP116.

**Risk:** medium: wrong decomposition if source admissibility has different components.


## D18 — Eq231 entropy with lower-cardinality rebate

**Status:** experimental_idea

**Provenance:** CMP116 Eq. (2.31) lower bound |P| >= 1/2*M^-4*gap

**Formula Ascii:** sum_P exp(-rho*g - 2*rho*|P|) <= exp(-(rho + rho*c_lb - carrier_entropy)*g)

**Why It Matters:** If the lower bound is source-compatible, the P-sum may have extra margin for later constants.

**Proof Route:** Prove a filtered-powerset lemma with a predicate `c_lb*g <= |P|`; compare to existing Eq. (2.31) theorem.

**Blockers:** Need source proof of lower-cardinality for all P in the exact family.

**Risk:** high: lower-cardinality may not hold for every admissible P or may be used differently.


## D19 — Eq237 fixed-Z0prime product extraction via metric stitching

**Status:** toy_lean_candidate

**Provenance:** Dimock Appendix F Eq. (641) + CMP116 Eq. (2.37)

**Formula Ascii:** exp(-a*sum_i d_i) * exp(b*(n-1)) <= exp(-a*d(Y)) when d(Y) <= sum_i d_i + (n-1) and b<=a

**Why It Matters:** Extracts the exact exponential price of Ω-connected stitching as a reusable finite inequality.

**Proof Route:** Lean theorem over finite sums of natural metrics using `Real.exp_le_exp`.

**Blockers:** Need sign assumptions and exact coefficients.

**Risk:** low-medium: finite algebra; source dictionary remains separate.


## D20 — Second-Ursell Catalan radius comparator

**Status:** experimental_idea

**Provenance:** rooted-tree Catalan closure + Appendix F second Ursell

**Formula Ascii:** If exact tree coefficient <= Catalan(n), then sum_n Catalan(n) x^n <= (1 - sqrt(1-4x))/(2x)

**Why It Matters:** Could replace coarse 4^n by an exact stability radius and sensitivity bound.

**Proof Route:** First prove a real-analysis toy comparator; only later attempt upstream tree coefficient identity.

**Blockers:** General Lean proof of rooted child factorial Catalan identity remains open.

**Risk:** high: may not match the actual source Ursell/tree class.


## D21 — hRpoly four-defect budget

**Status:** source_shape_candidate

**Provenance:** Riemann ErrorBudget + UVMassGap hRpoly

**Formula Ascii:** |Rsc t k| <= (raw_source + covariance_defect + dictionary_defect + support_defect) * exp(-c0*t)*g_k^kappa0

**Why It Matters:** Prevents a failed exact transport from killing the route; each defect can be attacked independently.

**Proof Route:** Define a record with four nonnegative amplitudes and a sum theorem into existing `hRpoly` shape.

**Blockers:** Must prove each defect decays with the same or stronger profile.

**Risk:** medium: may only repackage the hard input unless sub-defects are source-grounded.


## D22 — covariance-root Laplace discretization toy

**Status:** toy_lean_candidate

**Provenance:** Riemann finite Stieltjes/resolvent positivity + covariance root certificate

**Formula Ascii:** K^(-1/2) approx sum_j w_j*(K+s_j I)^(-1), w_j>=0, s_j>=0 -> positivity and kernel decay inherited termwise

**Why It Matters:** Gives a finite bridge from resolvent localization to root localization.

**Proof Route:** In finite-dimensional abstract form, prove nonnegativity and weighted-sum decay inheritance.

**Blockers:** Approximation error and physical K dictionary.

**Risk:** medium-high: exact square root identity is not obtained by approximation.


## D23 — source-package anti-vacuity witness

**Status:** toy_lean_candidate

**Provenance:** UVMassGap non-vacuity theorem discipline

**Formula Ascii:** exists Z D P, D in DIndex Z and P in PIndex Z D and P.Nonempty

**Why It Matters:** Stops source-package fields from being discharged by an empty family.

**Proof Route:** Add optional witness fields to experimental source packages and prove consumers do not need them but audits do.

**Blockers:** A real witness requires source dictionary and examples.

**Risk:** low: audit-only; should not be required by theorem consumers.


## D24 — finite-fiber duplicate target audit

**Status:** toy_lean_candidate

**Provenance:** physmath move separate_support_roles + Eq. (2.37) fibers

**Formula Ascii:** sum_{x in index} f(target x) = sum_{y in targets} fiberCard(y)*f(y)

**Why It Matters:** Detects false injectivity assumptions when target unions collide.

**Proof Route:** Finite reindex theorem with fiber cardinality. Use it before replacing dependent sums by target sums.

**Blockers:** None for toy theorem.

**Risk:** low.


## D25 — P-family carrier count with orientation quotient

**Status:** source_shape_candidate

**Provenance:** CMP109 positive-oriented bonds + Eq. (2.31) carrier count

**Formula Ascii:** card(gapCubes x Fin4) = 4*card(gapCubes); orientedCarrier embeds source bonds into this carrier

**Why It Matters:** Turns the 4-direction count into a dictionary lemma instead of repeating ad hoc card_product arguments.

**Proof Route:** Define `PositiveBondCarrier` with map sourceBond -> Cube x Fin 4 and prove injective/card bound.

**Blockers:** Exact source bond orientation convention.

**Risk:** medium.


## D26 — CMP116 Eq229 threshold interface from Cammarota

**Status:** source_extraction_candidate

**Provenance:** Cammarota CMP85 target + CMP116 Eq. (2.29)

**Formula Ascii:** small(alpha6, kappa, metric constants) -> sum_D prod_Y alpha6*exp(-delta*kappa*d(Y)) <= 1

**Why It Matters:** This is one of the remaining source theorem feeds, not just wiring.

**Proof Route:** Extract exact theorem statement and create an honest threshold record with all constants.

**Blockers:** Clean primary theorem extraction from Cammarota.

**Risk:** high but high payoff.


## D27 — Dimock/Balaban exponent-loss ledger

**Status:** source_shape_candidate

**Provenance:** Dimock extracted source keys for 3*kappa0+3, 5*kappa0+5, 6*kappa0+6

**Formula Ascii:** loss_total = cover_loss + first_cluster_loss + second_ursell_loss + source_dictionary_loss

**Why It Matters:** Makes exponent losses auditable instead of magic constants.

**Proof Route:** Create a finite ledger record with theorem `effective_kappa = kappa - loss_total`; connect to Appendix F estimates.

**Blockers:** Exact matching of each loss to source theorem.

**Risk:** medium.


## D28 — local homotopy boundary defect for gauge cancellation

**Status:** experimental_idea

**Provenance:** physmath move localize_homotopy + Ward defect route

**Formula Ascii:** P h d + d h P - P = [P,h]d + d[h,P] + boundary(P)

**Why It Matters:** Possible route to keep cancellations before norms in gauge activity estimates.

**Proof Route:** Toy finite cochain-complex matrix identity; no physical claim.

**Blockers:** Need actual gauge homotopy/projection and measure compatibility.

**Risk:** very high/speculative.


## D29 — Appendix-F half-budget split for target-card tilt

**Status:** toy_lean_candidate

**Provenance:** rooted leaf summation half-budget endpoints + Dimock Appendix F target fiber

**Formula Ascii:** exp(-a*d(Y))*card(targetFiber Y) <= exp(-(a/2)*d(Y)) if card <= exp((a/2)*d(Y))

**Why It Matters:** A reusable absorption lemma for finite target-card tilts.

**Proof Route:** Simple exponential inequality; instantiate with repository target-card theorem later.

**Blockers:** Need target-card bound.

**Risk:** low-medium.


## D30 — single-scale source theorem adapter with explicit projection loss

**Status:** source_shape_candidate

**Provenance:** PhysicalGaugeCMP116ActivityTransport + Appendix-F Ksharp route

**Formula Ascii:** PhysicalRawDecay A -> CMP116RawMetricDecay (A*C_proj*C_metric) when eval/support/metric projections hold

**Why It Matters:** Makes the physical-to-CMP116 conversion measurable as constants instead of an opaque transport package.

**Proof Route:** Refactor transport theorem into three projection constants and prove multiplication of constants.

**Blockers:** Actual physical raw estimate and metric normalization.

**Risk:** medium-high.
