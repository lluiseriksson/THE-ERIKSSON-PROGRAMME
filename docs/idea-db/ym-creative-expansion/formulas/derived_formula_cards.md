# Derived Formula Cards

Generated card index. Status fields are experimental unless promoted by real source extraction and Lean checks.

## D01.YMActivityBudget.min_exponent_triangle — YM activity error-budget triangle: source H# plus dictionary defects

**Status:** `experimental_derived_formula`
**Risk:** low as bookkeeping; high if agents silently set all defects to zero.

```text
If |H_src#(Y)|<=A0*exp(-eta0*d(Y)) and |H_YM#(Y)-H_src#(Y)|<=sum_i Ai*exp(-etai*d(Y)), then |H_YM#(Y)| <= (A0+sum_i Ai)*exp(-min_i eta_i * d(Y)).
```

**Why it matters:** Turns a vague “physical-to-source dictionary” into separately provable covariance, Gaussian, support and Jacobian defects. It is a safe Lean theorem and a strong audit device.

**Proof route:** Pure triangle inequality and exp monotonicity; no source paper needed. Then instantiate fields one by one.

**Blockers:**
- Define exact YM/source H# comparison terms
- Prove each defect has decay


## D02.power_lifted_coupling_tail — Power-lifted coupling summation: keep r^kappa when possible

**Status:** `experimental_derived_formula`
**Risk:** medium; only a constant/rate refinement, not hRpoly itself.

```text
If 0<=g_k<=C*r^k, 0<r<1 and p is a positive natural/integer exponent, then g_k^p <= C^p*(r^p)^k and sum_k A*e^{-c*t}*g_k^p <= A*C^p*(1-r^p)^(-1)*e^{-c*t}.
```

**Why it matters:** The current assembled theorem already closes with a geometric profile; this sharper variant may improve constants when κ₀ is a natural exponent and r^κ₀ is admissible.

**Proof route:** Use pow_le_pow_left₀ and finite/infinite geometric sum with base r^p.

**Blockers:**
- κ₀ in current theorem is real; create Nat-specialized endpoint or bridge real κ₀ to Nat


## D03.prime_tail_style_rg_tail — Prime-tail closed majorant as a late-scale RG tail template

**Status:** `experimental_derived_formula`
**Risk:** low for toy lemma; medium for source instantiation.

```text
For 0<r<1 and polynomial prefactor k^m, sum_{k>=K} k^m*r^k <= r^K * P_m(K)/(1-r)^(m+1). Use this as the RG analogue of X^{-delta}(log X/delta+1/delta^2).
```

**Why it matters:** Many source bounds hide polynomial-in-scale factors in O(1). This gives a finite, audit-friendly way to avoid absorbing them too early.

**Proof route:** Start with m=1,2 by differentiating finite geometric sums or using induction k^m <= C_m,K a^k for any a>1.

**Blockers:**
- Choose exact polynomial prefactors from Balaban/Dimock source constants


## D04.covariance_root_stieltjes_resolvent — Covariance-root localization by Stieltjes/resolvent integral

**Status:** `experimental_derived_formula`
**Risk:** high but genuinely creative and potentially high payoff.

```text
For finite SPD K, K^(-1/2) = (1/pi)*integral_0^infty s^(-1/2)*(K+sI)^(-1) ds. If resolvent kernels decay uniformly/integrably, then the covariance-root kernel decays.
```

**Why it matters:** The repo already has exact covariance from coercivity and carries root localization as source input. This gives a finite-dimensional toy theorem route that connects Dimock Green resolvents with the Riemann resolvent positivity style.

**Proof route:** First prove a spectral finite-matrix theorem for diagonal matrices; then self-adjoint diagonalization; then kernel bound via integral majorant.

**Blockers:**
- Mathlib spectral calculus ergonomics
- uniform decay constants for (K+sI)^(-1)
- field/bond dictionary


## D05.random_walk_green_to_root_pipeline — Dimock random-walk Green expansion as root-localization producer

**Status:** `experimental_derived_formula`
**Risk:** high; do as toy finite theorem first.

```text
C=A+a^2*A*Q*G*Q^T*A and G=sum_omega G_omega with |G_omega| localized. Combine finite-range A,Q with D04 to produce root kernel localization certificate.
```

**Why it matters:** Targets the exact open source hypothesis `PhysicalLocalizedCovarianceRootCertificate.root kernel localization` instead of adding another consumer.

**Proof route:** Lean finite support calculus: finite-range A/Q composition loses a bounded radius; Green expansion supplies exponential decay; root integral supplies square-root.

**Blockers:**
- prove/cite gauge precision resolvent identity
- finite support radius of Q/A in physical gauge layer


## D06.eq231_admissible_automaton — Eq. (2.31) P-family as a finite admissibility automaton

**Status:** `experimental_derived_formula`
**Risk:** medium; high payoff because it removes a live source hypothesis.

```text
P in PIndex(Z,D) iff P subset gapCubes(Z,D) x Fin4 and admissible(Z,D,P)=true, where admissible is decomposed into local endpoint, positive-orientation and no-duplicate constraints.
```

**Why it matters:** This is the highest source-honesty payoff: it discharges carrier containment and unlocks existing Eq. (2.31) consumers without adding more wrappers.

**Proof route:** Make `admissible` a Bool conjunction of finite local predicates; prove membership iff by unfolding; separately prove source dictionary from CMP116/CMP109 text.

**Blockers:**
- exact CMP116 P definition
- CMP109 positive bond convention to Fin4
- carrier count <= 4*|gap|


## D07.eq231_lower_cardinality_boost — Eq. (2.31) entropy boost from |P| lower bound

**Status:** `experimental_derived_formula`
**Risk:** medium; possible mismatch of source lower bound context.

```text
If each source P satisfies |P| >= lambda*gapMass, then sum_{P admissible} exp(-rho*gapMass)*exp(-2*rho*|P|) <= exp(-((rho+2*rho*lambda)-4*M^4*exp(-2*rho))*gapMass). For lambda=1/2 this doubles the useful rho term.
```

**Why it matters:** The source database records a visual lower bound |P| >= 1/2 M^{-4}|Z0\Y0|. If it is part of the same summation lane, it may give a stronger P-stage margin.

**Proof route:** Extract q^m from the powerset sum: sum_{S subset B, m<=|S|} q^|S| <= q^m(1+q)^|B|, then exp-bound.

**Blockers:**
- source confirmation that lower bound applies to exactly the P family being summed
- define gapMass/cardinality relation


## D08.eq231_catalan_admissible_entropy — Replace powerset entropy by Catalan/forest entropy for structured admissible P

**Status:** `speculative_derived_formula`
**Risk:** high/speculative; keep outside source DB.

```text
If admissible P is encoded by rooted forests/skeletons with n bonds and target-preserving fibers bounded by Catalan(n), then sum_P q^|P| <= sum_n Catalan(n)*(A*q)^n = C(A*q)-1 for A*q<1/4.
```

**Why it matters:** Could relax the brutal 2^carrier entropy if P is much more structured than arbitrary subsets. This is out-of-the-box and must be tested with finite examples before source use.

**Proof route:** Start with toy finite gap graphs. Enumerate admissible P for small gaps, compare with powerset and Catalan counts. Only then attempt Lean statement.

**Blockers:**
- source P may be arbitrary finite bond subset, not forest-like
- Catalan identity general Lean proof still open in separate artifact


## D09.eq237_metric_stitching_product_extraction — Post-P product metric extraction using Dimock metric stitching

**Status:** `experimental_derived_formula`
**Risk:** low for algebra; medium for source dictionaries.

```text
If d(Y)<=sum_i d(X_i)+(n-1) and b>=0, then prod_i exp(-b*d(X_i)) <= exp(-b*d(Y))*exp(b*(n-1)). Absorb exp(b*(n-1)) into the n-component entropy/generating function.
```

**Why it matters:** This is the exact algebraic heart of Eq. (2.37) final summation: extract the target decay before losing component structure.

**Proof route:** Pure real inequality from Dimock Eq. (641). Prove once, reuse in Eq. (2.37) and Appendix-F H# lanes.

**Blockers:**
- exact metric dictionary d_k/d_{k+1}/modified metric
- component union theorem


## D10.eq237_catalan_second_ursell_closure — Eq. (2.37) final sum through Catalan second-Ursell generating function

**Status:** `experimental_derived_formula`
**Risk:** medium-high; potentially useful for constants and proof search.

```text
After D09, the n-component contribution has shape Catalan(n)*(A*K0*exp(b))^n*exp(-b*d(Y)). If A*K0*exp(b)<1/4, close by the Catalan generating function and keep exp(-b*d(Y)).
```

**Why it matters:** This merges the Catalan closure repo with Dimock Appendix F to attack the final post-(2.37) summation rather than just indexing it.

**Proof route:** First use existing 4^n endpoint; then replace by conditional Catalan endpoint when RootedChildFactorialCatalanIdentity is proved or assumed explicitly.

**Blockers:**
- general Catalan identity proof
- exact component count-to-tree mapping
- smallness A*K0*exp(b)<1/4


## D11.loss_ledger_algebra — Unified loss ledger for Balaban/Dimock exponents

**Status:** `experimental_derived_formula`
**Risk:** low; high practical value for planning.

```text
Represent every source step as eta_out = scale*eta_in - loss, e.g. kappa -> kappa-3*kappa0-3, kappa -> kappa-kappa0-2, L*kappa -> L*(kappa-6*kappa0-6). Compose losses mechanically.
```

**Why it matters:** Stops agents from mixing incompatible κ, κ₀, L and δ exponents. A small Lean/file-level algebra layer can check positive-margin obligations before analytic work.

**Proof route:** Finite list fold over affine maps eta ↦ a*eta-loss; prove monotonicity and positivity conditions.

**Blockers:**
- fill exact source constants per lane


## D12.target_preserving_fiber_before_overcount — Keep exact union/target fibers before overcounting

**Status:** `experimental_derived_formula`
**Risk:** low-medium; mostly bookkeeping but can be hard Lean engineering.

```text
For fixed target Y, keep Fib(Y,n)={(Y1,...,Yn): union Yi=Y and Omega-connected}; prove metric extraction on Fib(Y,n) before mapping to rooted trees or cardinality bounds.
```

**Why it matters:** Prevents target erasure. This is exactly the pattern that made rooted-tree target-preserving summation valuable.

**Proof route:** Define finite sigma/fiber index; prove equality of nested sum and fiber sum; only then apply tree overcount.

**Blockers:**
- finite source-to-Lean fiber dictionary
- Ursell coefficient convention


## D13.ward_defect_before_norms — Gauge/Ward cancellation before absolute-value majorization

**Status:** `speculative_derived_formula`
**Risk:** high/speculative but worth a toy finite theorem.

```text
Decompose H = H_exact_cancel + d_W B + Def. If integral(d_W B * weight)=0 and |Def(X)|<=D0*exp(-eta*d(X)), then activity is controlled by the defect rather than the full naive norm.
```

**Why it matters:** A possible route for raw YM activity: avoid destroying gauge/center cancellations by taking norms too early.

**Proof route:** Start finite: signed sum over a finite group action with invariant measure; show exact sector integrates to zero and bound defect.

**Blockers:**
- actual differentiable/gauge Ward identity for lattice variables
- boundary/regulator defect control


## D14.separator_collar_covariance_split — Condition on a collar/separator to localize covariance defects

**Status:** `experimental_derived_formula`
**Risk:** medium-high; good finite counterexample generator.

```text
Split field variables into A | collar S | B. If precision K_AB=0 conditional on S, covariance cross terms are carried by Schur-complement/collar defects; residual <= C*exp(-gamma*width(S)).
```

**Why it matters:** Could localize the physical covariance/root certificate by finite Markov-blanket identities before using random-walk decay.

**Proof route:** Finite SPD block matrix theorem: if K_AB=0, conditional independence; perturbation bound when K_AB small.

**Blockers:**
- gauge constraints may make Schur complement dense
- exact block support of K


## D15.continuum_guardrail_M3_not_Clay — Hard guardrail: M3 lattice gap is not continuum Clay

**Status:** `governance_formula`
**Risk:** low and mandatory.

```text
M3_discharge => unconditional lattice mass gap only. Clay requires continuum limit + OS/Wightman reconstruction + positive physical mass gap; none may be inferred from hRpoly alone.
```

**Why it matters:** Prevents agents from turning creative formula search into false theorem claims.

**Proof route:** Documentation/governance, not mathematical proof.

**Blockers:**
- None


## D16 — Eq231 two-sided source dictionary with explicit admissibility skeleton

**Status:** `source_shape_candidate`
**Risk:** medium-high: could expose missing source details rather than close them.

```text
P in PIndex Z D <-> P subset gapCubes Z D x Fin4 and sourceAdmissible Z D P = true and PositiveOriented P
```

**Why it matters:** It separates the carrier fact from the nontrivial admissibility content, avoiding a vacuous admissible predicate that hides the source definition.

**Proof route:** Define a record `CMP116Eq231SourceDictionary` with fields carrier, orientation, admissibility_iff; prove existing hmem from the record.

**Blockers:**
- E
- x
- a
- c
- t
-
- B
- a
- l
- a
- b
- a
- n
-
- P
- -
- f
- a
- m
- i
- l
- y
-
- d
- e
- f
- i
- n
- i
- t
- i
- o
- n
-
- a
- n
- d
-
- p
- o
- s
- i
- t
- i
- v
- e
-
- b
- o
- n
- d
-
- c
- o
- n
- v
- e
- n
- t
- i
- o
- n
- .


## D17 — Eq231 admissibility normal form as finite conjunction

**Status:** `toy_lean_candidate`
**Risk:** medium: wrong decomposition if source admissibility has different components.

```text
admissible Z D P = true <-> carrier_ok Z D P && separation_ok Z D P && connectivity_ok Z D P && nonempty_gap_ok Z D P
```

**Why it matters:** Allows builders to prove individual source-package fields instead of a monolithic iff.

**Proof route:** Make a Boolean normal-form record and prove projection lemmas. Later map each boolean to a source paragraph.

**Blockers:**
- N
- e
- e
- d
-
- d
- e
- c
- i
- d
- e
-
- a
- c
- t
- u
- a
- l
-
- a
- d
- m
- i
- s
- s
- i
- b
- i
- l
- i
- t
- y
-
- c
- o
- m
- p
- o
- n
- e
- n
- t
- s
-
- f
- r
- o
- m
-
- C
- M
- P
- 1
- 1
- 6
- .


## D18 — Eq231 entropy with lower-cardinality rebate

**Status:** `experimental_idea`
**Risk:** high: lower-cardinality may not hold for every admissible P or may be used differently.

```text
sum_P exp(-rho*g - 2*rho*|P|) <= exp(-(rho + rho*c_lb - carrier_entropy)*g)
```

**Why it matters:** If the lower bound is source-compatible, the P-sum may have extra margin for later constants.

**Proof route:** Prove a filtered-powerset lemma with a predicate `c_lb*g <= |P|`; compare to existing Eq. (2.31) theorem.

**Blockers:**
- N
- e
- e
- d
-
- s
- o
- u
- r
- c
- e
-
- p
- r
- o
- o
- f
-
- o
- f
-
- l
- o
- w
- e
- r
- -
- c
- a
- r
- d
- i
- n
- a
- l
- i
- t
- y
-
- f
- o
- r
-
- a
- l
- l
-
- P
-
- i
- n
-
- t
- h
- e
-
- e
- x
- a
- c
- t
-
- f
- a
- m
- i
- l
- y
- .


## D19 — Eq237 fixed-Z0prime product extraction via metric stitching

**Status:** `toy_lean_candidate`
**Risk:** low-medium: finite algebra; source dictionary remains separate.

```text
exp(-a*sum_i d_i) * exp(b*(n-1)) <= exp(-a*d(Y)) when d(Y) <= sum_i d_i + (n-1) and b<=a
```

**Why it matters:** Extracts the exact exponential price of Ω-connected stitching as a reusable finite inequality.

**Proof route:** Lean theorem over finite sums of natural metrics using `Real.exp_le_exp`.

**Blockers:**
- N
- e
- e
- d
-
- s
- i
- g
- n
-
- a
- s
- s
- u
- m
- p
- t
- i
- o
- n
- s
-
- a
- n
- d
-
- e
- x
- a
- c
- t
-
- c
- o
- e
- f
- f
- i
- c
- i
- e
- n
- t
- s
- .


## D20 — Second-Ursell Catalan radius comparator

**Status:** `experimental_idea`
**Risk:** high: may not match the actual source Ursell/tree class.

```text
If exact tree coefficient <= Catalan(n), then sum_n Catalan(n) x^n <= (1 - sqrt(1-4x))/(2x)
```

**Why it matters:** Could replace coarse 4^n by an exact stability radius and sensitivity bound.

**Proof route:** First prove a real-analysis toy comparator; only later attempt upstream tree coefficient identity.

**Blockers:**
- G
- e
- n
- e
- r
- a
- l
-
- L
- e
- a
- n
-
- p
- r
- o
- o
- f
-
- o
- f
-
- r
- o
- o
- t
- e
- d
-
- c
- h
- i
- l
- d
-
- f
- a
- c
- t
- o
- r
- i
- a
- l
-
- C
- a
- t
- a
- l
- a
- n
-
- i
- d
- e
- n
- t
- i
- t
- y
-
- r
- e
- m
- a
- i
- n
- s
-
- o
- p
- e
- n
- .


## D21 — hRpoly four-defect budget

**Status:** `source_shape_candidate`
**Risk:** medium: may only repackage the hard input unless sub-defects are source-grounded.

```text
|Rsc t k| <= (raw_source + covariance_defect + dictionary_defect + support_defect) * exp(-c0*t)*g_k^kappa0
```

**Why it matters:** Prevents a failed exact transport from killing the route; each defect can be attacked independently.

**Proof route:** Define a record with four nonnegative amplitudes and a sum theorem into existing `hRpoly` shape.

**Blockers:**
- M
- u
- s
- t
-
- p
- r
- o
- v
- e
-
- e
- a
- c
- h
-
- d
- e
- f
- e
- c
- t
-
- d
- e
- c
- a
- y
- s
-
- w
- i
- t
- h
-
- t
- h
- e
-
- s
- a
- m
- e
-
- o
- r
-
- s
- t
- r
- o
- n
- g
- e
- r
-
- p
- r
- o
- f
- i
- l
- e
- .


## D22 — covariance-root Laplace discretization toy

**Status:** `toy_lean_candidate`
**Risk:** medium-high: exact square root identity is not obtained by approximation.

```text
K^(-1/2) approx sum_j w_j*(K+s_j I)^(-1), w_j>=0, s_j>=0 -> positivity and kernel decay inherited termwise
```

**Why it matters:** Gives a finite bridge from resolvent localization to root localization.

**Proof route:** In finite-dimensional abstract form, prove nonnegativity and weighted-sum decay inheritance.

**Blockers:**
- A
- p
- p
- r
- o
- x
- i
- m
- a
- t
- i
- o
- n
-
- e
- r
- r
- o
- r
-
- a
- n
- d
-
- p
- h
- y
- s
- i
- c
- a
- l
-
- K
-
- d
- i
- c
- t
- i
- o
- n
- a
- r
- y
- .


## D23 — source-package anti-vacuity witness

**Status:** `toy_lean_candidate`
**Risk:** low: audit-only; should not be required by theorem consumers.

```text
exists Z D P, D in DIndex Z and P in PIndex Z D and P.Nonempty
```

**Why it matters:** Stops source-package fields from being discharged by an empty family.

**Proof route:** Add optional witness fields to experimental source packages and prove consumers do not need them but audits do.

**Blockers:**
- A
-
- r
- e
- a
- l
-
- w
- i
- t
- n
- e
- s
- s
-
- r
- e
- q
- u
- i
- r
- e
- s
-
- s
- o
- u
- r
- c
- e
-
- d
- i
- c
- t
- i
- o
- n
- a
- r
- y
-
- a
- n
- d
-
- e
- x
- a
- m
- p
- l
- e
- s
- .


## D24 — finite-fiber duplicate target audit

**Status:** `toy_lean_candidate`
**Risk:** low.

```text
sum_{x in index} f(target x) = sum_{y in targets} fiberCard(y)*f(y)
```

**Why it matters:** Detects false injectivity assumptions when target unions collide.

**Proof route:** Finite reindex theorem with fiber cardinality. Use it before replacing dependent sums by target sums.

**Blockers:**
- N
- o
- n
- e
-
- f
- o
- r
-
- t
- o
- y
-
- t
- h
- e
- o
- r
- e
- m
- .


## D25 — P-family carrier count with orientation quotient

**Status:** `source_shape_candidate`
**Risk:** medium.

```text
card(gapCubes x Fin4) = 4*card(gapCubes); orientedCarrier embeds source bonds into this carrier
```

**Why it matters:** Turns the 4-direction count into a dictionary lemma instead of repeating ad hoc card_product arguments.

**Proof route:** Define `PositiveBondCarrier` with map sourceBond -> Cube x Fin 4 and prove injective/card bound.

**Blockers:**
- E
- x
- a
- c
- t
-
- s
- o
- u
- r
- c
- e
-
- b
- o
- n
- d
-
- o
- r
- i
- e
- n
- t
- a
- t
- i
- o
- n
-
- c
- o
- n
- v
- e
- n
- t
- i
- o
- n
- .


## D26 — CMP116 Eq229 threshold interface from Cammarota

**Status:** `source_extraction_candidate`
**Risk:** high but high payoff.

```text
small(alpha6, kappa, metric constants) -> sum_D prod_Y alpha6*exp(-delta*kappa*d(Y)) <= 1
```

**Why it matters:** This is one of the remaining source theorem feeds, not just wiring.

**Proof route:** Extract exact theorem statement and create an honest threshold record with all constants.

**Blockers:**
- C
- l
- e
- a
- n
-
- p
- r
- i
- m
- a
- r
- y
-
- t
- h
- e
- o
- r
- e
- m
-
- e
- x
- t
- r
- a
- c
- t
- i
- o
- n
-
- f
- r
- o
- m
-
- C
- a
- m
- m
- a
- r
- o
- t
- a
- .


## D27 — Dimock/Balaban exponent-loss ledger

**Status:** `source_shape_candidate`
**Risk:** medium.

```text
loss_total = cover_loss + first_cluster_loss + second_ursell_loss + source_dictionary_loss
```

**Why it matters:** Makes exponent losses auditable instead of magic constants.

**Proof route:** Create a finite ledger record with theorem `effective_kappa = kappa - loss_total`; connect to Appendix F estimates.

**Blockers:**
- E
- x
- a
- c
- t
-
- m
- a
- t
- c
- h
- i
- n
- g
-
- o
- f
-
- e
- a
- c
- h
-
- l
- o
- s
- s
-
- t
- o
-
- s
- o
- u
- r
- c
- e
-
- t
- h
- e
- o
- r
- e
- m
- .


## D28 — local homotopy boundary defect for gauge cancellation

**Status:** `experimental_idea`
**Risk:** very high/speculative.

```text
P h d + d h P - P = [P,h]d + d[h,P] + boundary(P)
```

**Why it matters:** Possible route to keep cancellations before norms in gauge activity estimates.

**Proof route:** Toy finite cochain-complex matrix identity; no physical claim.

**Blockers:**
- N
- e
- e
- d
-
- a
- c
- t
- u
- a
- l
-
- g
- a
- u
- g
- e
-
- h
- o
- m
- o
- t
- o
- p
- y
- /
- p
- r
- o
- j
- e
- c
- t
- i
- o
- n
-
- a
- n
- d
-
- m
- e
- a
- s
- u
- r
- e
-
- c
- o
- m
- p
- a
- t
- i
- b
- i
- l
- i
- t
- y
- .


## D29 — Appendix-F half-budget split for target-card tilt

**Status:** `toy_lean_candidate`
**Risk:** low-medium.

```text
exp(-a*d(Y))*card(targetFiber Y) <= exp(-(a/2)*d(Y)) if card <= exp((a/2)*d(Y))
```

**Why it matters:** A reusable absorption lemma for finite target-card tilts.

**Proof route:** Simple exponential inequality; instantiate with repository target-card theorem later.

**Blockers:**
- N
- e
- e
- d
-
- t
- a
- r
- g
- e
- t
- -
- c
- a
- r
- d
-
- b
- o
- u
- n
- d
- .


## D30 — single-scale source theorem adapter with explicit projection loss

**Status:** `source_shape_candidate`
**Risk:** medium-high.

```text
PhysicalRawDecay A -> CMP116RawMetricDecay (A*C_proj*C_metric) when eval/support/metric projections hold
```

**Why it matters:** Makes the physical-to-CMP116 conversion measurable as constants instead of an opaque transport package.

**Proof route:** Refactor transport theorem into three projection constants and prove multiplication of constants.

**Blockers:**
- A
- c
- t
- u
- a
- l
-
- p
- h
- y
- s
- i
- c
- a
- l
-
- r
- a
- w
-
- e
- s
- t
- i
- m
- a
- t
- e
-
- a
- n
- d
-
- m
- e
- t
- r
- i
- c
-
- n
- o
- r
- m
- a
- l
- i
- z
- a
- t
- i
- o
- n
- .


## D31.eq231_source_package_field_splitter — Eq231 source package field splitter

**Status:** `experimental_derived_formula_post_integration`
**Risk:** medium; low Lean risk, high source-transcription risk

```text
SourcePackage = mem_iff_source ∧ source_subset_gapCarrier ∧ admissible_iff_source; progress metric = discharge exactly one field without changing the other two.
```

**Why it matters:** The repo now has a source package. The next useful commit should remove one field, not add another consumer of the package.

**Proof route:** Open only the CMP116/CMP109 source keys for the chosen field. Prove a narrow theorem whose conclusion matches the exact source-package field.

**Blockers:**
- exact source predicate
- positive-oriented bond dictionary
- avoid circular admissible := decide(P in PIndex)


## D32.eq231_bond_fst_mem_gapCubes_from_b0_corridor — Eq231 bond first-coordinate in gap cubes

**Status:** `experimental_derived_formula_post_integration`
**Risk:** medium; probably the best next source-shaped theorem

```text
sourceAdmissible(Z,D,P) -> forall b in P, fst(b) in gapCubes(Z,D)
```

**Why it matters:** This is the narrow premise needed by cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes; it can remove source_subset_gapCarrier before the full iff is solved.

**Proof route:** Treat CMP109 as orientation convention only and CMP116 as ownership of the first coordinate. Do not use a cardinality bound as membership evidence.

**Blockers:**
- which endpoint/base cube is encoded as fst
- whether b0(c) exclusion changes carrier
- exact gapCubes dictionary


## D33.eq231_admissible_bool_not_vacuous — Eq231 admissible boolean with non-vacuity witness

**Status:** `experimental_derived_formula_post_integration`
**Risk:** medium; primarily an anti-vacuity check

```text
admissible Z D P = true <-> sourceAdmissible Z D P, plus exists P sourceAdmissible Z D P in a toy/nonempty source window.
```

**Why it matters:** Prevents the cheap but useless definition admissible := decide(sourceAdmissible) from hiding an empty or circular source predicate.

**Proof route:** State the iff only after sourceAdmissible is transcribed independently; add a witness or source-side inhabited condition separately.

**Blockers:**
- source predicate transcribed
- nonempty window not always needed for theorem, but needed for audit


## D34.eq231_mem_iff_source_from_source_family_definition — Eq231 mem_iff_source from Balaban family definition

**Status:** `experimental_derived_formula_post_integration`
**Risk:** medium-high; large source-dictionary risk

```text
P in PIndex(Z,D) <-> sourceAdmissible(Z,D,P) from the printed definition of the P-family, before carrier/admissible boolean are used.
```

**Why it matters:** This is the highest-value field but must not be proved by unfolding the Lean filtered family; it has to come from the source family definition.

**Proof route:** Make sourceAdmissible contain exactly the printed P-family restrictions, then prove extensional equality to PIndex.

**Blockers:**
- exact PIndex source definition
- minimal Z0 convention
- D-dependent source parameters


## D35.eq231_pointwise_residual_factorization — Eq231 pointwise residual factorization before entropy

**Status:** `experimental_derived_formula_post_integration`
**Risk:** high; analytic blocker

```text
pResidualWeight(Z,D,P) <= A231 * pGeometryWeight(Z,D,P) and pGeometryWeight(Z,D,P) <= exp(-rho*gapMass)*exp(-2*rho*|P|)
```

**Why it matters:** The finite entropy theorem is already available; the missing analytic piece is matching the actual residual term to the Eq. (2.31) geometry weight.

**Proof route:** Extract factors surrounding Eq. (2.31) and name the residual/geometry weights separately; never infer termwise domination from the final sum.

**Blockers:**
- source pResidualWeight identification
- source pGeometryWeight identification
- constant A231 normalization


## D36.eq231_bracket_condition_as_only_scalar_gate — Eq231 bracket condition as the only scalar gate

**Status:** `experimental_derived_formula_post_integration`
**Risk:** low as a guardrail

```text
4*M^4*exp(-2*rho) <= rho is the scalar gate; hsmall is only a sufficient reducer, not the source theorem.
```

**Why it matters:** Keeps the source-bracket interface primary and prevents agents from replacing it with a stronger non-source smallness condition as if it were Balaban's statement.

**Proof route:** Use the bracket theorem already in Lean; add no new analytic claim unless source confirms the stronger hierarchy.

**Blockers:**
- none for bookkeeping
- source hierarchy if trying to discharge bracket


## D37.eq237_source_index_equality_before_estimate — Eq237 source Z0prime index equality before estimate

**Status:** `experimental_derived_formula_post_integration`
**Risk:** medium

```text
sourceZ0PrimeIndex(Z) = globalUnion_{D in DIndex Z, P in PIndex Z D} Z0PrimeIndex(Z,D,P) from a source membership iff.
```

**Why it matters:** The Eq. (2.37) estimate should not be proved over the wrong summation family; identify the index first.

**Proof route:** Prove membership iff for the source Z0prime family; then reuse the existing finite extensionality theorem.

**Blockers:**
- D/P/Z0/Z0prime dictionary
- source finite family exact shape


## D38.eq237_component_product_common_majorant — Eq237 component product common-majorant theorem

**Status:** `experimental_derived_formula_post_integration`
**Risk:** medium-high

```text
prod_i (A237*exp(-eta*d_i)) * exp(Calpha5*alpha5*|Z|) <= C3*epsilon1*exp(-eta_final*d(Z)) after source restrictions.
```

**Why it matters:** This names the exact absorption that sits between fixed-Z0prime Eq. (2.37) and the final Lemma 3 amplitude.

**Proof route:** Separate pure real absorption from source dictionary. The pure theorem takes all source inequalities as hypotheses.

**Blockers:**
- alpha5 restrictions
- C3 formula
- component metric comparison


## D39.eq229_cammarota_threshold_record — Eq229 Cammarota threshold record

**Status:** `experimental_derived_formula_post_integration`
**Risk:** high if used as theorem; low as honest interface

```text
CammarotaThreshold(K, alpha6, delta, kappa, metric, DFamily) -> CMP116Eq229Summability DIndex DParts alpha6 delta kappa metric.
```

**Why it matters:** Turns the external-source blocker into a precise interface without pretending the Cammarota theorem has already been extracted.

**Proof route:** First create record only. Populate it after clean primary source extraction.

**Blockers:**
- clean Cammarota theorem text
- constants and uniformity
- D-family dictionary


## D40.source_status_promotion_gate_formula — Source status promotion gate formula

**Status:** `experimental_derived_formula_post_integration`
**Risk:** low; governance

```text
source_pending -> source_extracted only after formulas + hypotheses + quantifiers + convention + local artifact hash; source_extracted -> theorem_checked only after Lean target compiles/oracle.
```

**Why it matters:** Batch 003 has many lean_linked operational cards. This formula prevents navigation records from becoming proof evidence.

**Proof route:** Use scripts/source_db.py verify/build and a human extraction checklist; not a Lean theorem.

**Blockers:**
- no raw OCR dumps in public repo
- source artifact provenance


## D41.r_operation_polymer_to_scalar_bridge — R-operation polymer-local to scalar R_k bridge

**Status:** `experimental_derived_formula_post_integration`
**Risk:** high; core hRpoly-adjacent blocker

```text
polymerLocalBound(X,k) + rooted summability over X containing r -> |Rsc(t,k)| <= A*exp(-c0*t)*g_k^kappa0.
```

**Why it matters:** The repo warns that |R_k| <= M r^k is not the same as polymer-local R-operation bounds. This card isolates the missing summation bridge.

**Proof route:** Do not collapse X-local bounds into scalar Rsc until the rooted/pinned sum and exact Rsc identity are proved.

**Blockers:**
- Rsc identity
- rooted polymer summability
- CMP119/CMP122 dictionary


## D42.gaussian_root_hessian_order_guard — Gaussian-root/Hessian order-of-operations guard

**Status:** `experimental_derived_formula_post_integration`
**Risk:** low; governance

```text
Hessian identification -> coercivity -> covariance inverse -> root localization -> Gaussian pushforward -> activity construction; do not reverse arrows.
```

**Why it matters:** Prevents agents from using a covariance-root certificate to justify the physical Hessian or Gaussian measure that should precede it.

**Proof route:** Use as checklist in proof sprints and source audit; not source evidence.

**Blockers:**
- physical Hessian source theorem
- covariance localization
- Jacobian/coordinate dictionary


## D43.no_new_consumers_detector — No-new-consumers detector

**Status:** `experimental_derived_formula_post_integration`
**Risk:** low; process

```text
A commit is cosmetic if it adds theorem A_of_B where B is still the same live source hypothesis and no source status/field/hypothesis is removed.
```

**Why it matters:** The repo is saturated on routing. This prevents more wrappers and forces source-hypothesis removal.

**Proof route:** Run before accepting constructor output; compare live hypothesis list before/after.

**Blockers:**
- requires manually maintained live-hypothesis list


## D44.source_key_router_as_agent_prompt — Source-key router as agent prompt

**Status:** `experimental_derived_formula_post_integration`
**Risk:** low

```text
Given proof key K, load only source keys router(K), then produce theorem shape + blockers + forbidden shortcuts.
```

**Why it matters:** Keeps agents from broad OCR/search loops and locks them to bounded source windows.

**Proof route:** Use in prompts; not a theorem.

**Blockers:**
- router can be operational metadata only


## D45.one_commit_one_hypothesis_invariant — One-commit-one-hypothesis invariant

**Status:** `experimental_derived_formula_post_integration`
**Risk:** low; process

```text
Each accepted commit must name exactly one removed or narrowed live source hypothesis; otherwise it is a docs/idea-only commit.
```

**Why it matters:** Transforms vague creativity into measurable source-hypothesis removal.

**Proof route:** Add to constructor checklist and PR template; not a mathematical theorem.

**Blockers:**
- some honest commits may only create an extraction interface; mark them as interface-only


## D46.obligation_contract_state_machine — Proof-obligation state machine: source_pending → source_extracted → theorem_feedable → theorem_checked

**Status:** `experimental_operational_formula`
**Risk:** low; operational only

```text
A proof card advances only if evidence(field) >= required_evidence(field) and removed_hypotheses != empty. State transitions: pending -> extracted -> lean_linked -> theorem_checked; no transition is allowed from idea_db directly to theorem_checked.
```

**Why it matters:** Prevents agents from treating operational cards, crosswalks, or idea cards as proof. It makes status movement auditable and commit-sized.

**Proof route:** Pure metadata/CI gate. Validate a JSON contract against required fields, source keys, proof-card status, and changed-file class.

**Blockers:**
- Need actual repo script integration if used inside CI
- Cannot infer theorem_checked without real Lean build/oracle logs


## D47.eq231_three_field_burndown_vector — Eq. (2.31) source package burn-down vector

**Status:** `experimental_operational_formula`
**Risk:** low-medium

```text
P-family dictionary debt = [mem_iff_source, source_subset_gapCarrier, admissible_iff_source]. A commit succeeds if it discharges at least one component without redefining admissible tautologically.
```

**Why it matters:** The full iff is hard; field-level burndown lets agents make real progress on the source package.

**Proof route:** Use the existing package fields; implement dedicated source keys and theorem names for one field at a time.

**Blockers:**
- Need primary extraction for each package field
- Need avoid defining sourceAdmissible as membership


## D48.eq231_base_cube_projection_certificate — Eq. (2.31) base-cube projection certificate

**Status:** `experimental_derived_formula`
**Risk:** medium

```text
If every encoded bond b in source-admissible P has b.1 in gapCubes(Z,D), then P subset gapCubes(Z,D) x Fin 4.
```

**Why it matters:** This is the smallest nontrivial field currently reachable by Lean's existing reducer for Eq. (2.31).

**Proof route:** Formal proof already has a generic reducer; source work only needs the base-cube projection theorem.

**Blockers:**
- Primary CMP116/CMP109 extraction of base-cube ownership
- Direction/orientation convention must be positive, not unoriented


## D49.eq231_carrier_equality_vs_upper_bound_split — Split carrier equality from carrier upper bound

**Status:** `experimental_derived_formula`
**Risk:** medium

```text
Route A: BalabanCarrier = gapCubes x Fin4 gives exact count 4*|gapCubes|. Route B: injection BalabanCarrier -> gapCubes x Fin4 gives only <=. Choose B unless source gives equality.
```

**Why it matters:** Avoids overclaiming exact equality when source may only support an injection; enough for Eq. (2.31) entropy.

**Proof route:** Add an injection-shaped boundary alternative if equality is not source-grounded.

**Blockers:**
- Need decide whether current boundary should accept injection carrier
- Need not weaken already theorem-fed filtered route


## D50.admissible_non_tautology_test — Admissible non-tautology test

**Status:** `experimental_operational_formula`
**Risk:** low

```text
Reject if admissible(Z,D,P) is defined as decide(P in PIndex Z D), or sourceAdmissible is definitionally equivalent to membership without a primary source dictionary.
```

**Why it matters:** The easiest fake proof of the membership iff is circular. This test makes the circularity machine-detectable in review.

**Proof route:** Static grep plus manual review of definition sites; record failure in falsification results.

**Blockers:**
- Static detection is heuristic
- Legitimate wrappers may mention PIndex in comments


## D51.eq231_pointwise_after_dictionary_only — Eq. (2.31) pointwise residual only after P dictionary

**Status:** `experimental_planning_formula`
**Risk:** medium-high

```text
Do not attempt hgeometry until PIndex and carrier dictionary are fixed. Then factor residual <= amplitude * geometryWeight and geometryWeight <= PWeight.
```

**Why it matters:** Keeps analytic work from being done against the wrong P family.

**Proof route:** Gate pointwise sprint on completion or explicit blocker status of proof.eq231.membership-iff.source-package.

**Blockers:**
- Actual residual term surrounding Eq. (2.31) still needs extraction


## D52.patch_acceptance_delta_metric — Patch acceptance delta: one field/hypothesis removed per commit

**Status:** `experimental_operational_formula`
**Risk:** low

```text
score(patch)=10*removed_fields+6*source_promotions+4*new_toy_theorems-8*new_consumers_without_removed_fields-5*new_opaque_props. Accept if score>=10 and removed_fields+source_promotions>=1.
```

**Why it matters:** Turns “looks useful” into a reviewable numerical filter for agents.

**Proof route:** Use check_patch_contract.py with changed-file metadata and contract JSON.

**Blockers:**
- Needs manual calibration
- Heuristic cannot replace Lean build


## D53.source_key_router_prompt_compiler — Compile source-key router entries into exact agent prompts

**Status:** `experimental_operational_formula`
**Risk:** low

```text
Given proof_card key, prompt = allowed_source_keys + exact target shape + do_not + required_output_schema. Any source key not routed to the card is forbidden in first pass.
```

**Why it matters:** Prevents broad, expensive, error-prone paper browsing and forces bounded extraction.

**Proof route:** Generate prompts from mission_contracts/*.json.

**Blockers:**
- Requires updating contracts as Batch 004+ evolves


## D54.eq237_two_premise_source_boundary — Eq. (2.37) two-premise boundary: fixed-Z0' estimate plus final summation

**Status:** `experimental_derived_formula`
**Risk:** medium

```text
Post-P closure requires exactly two source premises: heq237_fixed over fibers and hpost_eq237 over sourceZ0PrimeIndex/globalIndex. Do not split further unless source does.
```

**Why it matters:** Keeps agents from inventing unsupported intermediate lemmas while still giving a precise Lean target.

**Proof route:** Use cmp116PostPResidualSourceBound_of_eq237 or _globalIndex once two premises are source-extracted.

**Blockers:**
- Need exact fixed-Z0' formula
- Need final summation source paragraph


## D55.common_majorant_for_O1_constants — Common-majorant theorem for distinct O(1) constants

**Status:** `experimental_derived_formula`
**Risk:** low-medium

```text
If each source O_i(1) <= C_* and all prefactors are nonnegative, then product/sum constants can be replaced by C_*^m times explicit prefactors.
```

**Why it matters:** Allows safe C3 consolidation without pretending all O(1) symbols are the same constant.

**Proof route:** Pure real inequality plus source record listing each O(1) occurrence.

**Blockers:**
- Need source-specific count of distinct O(1) constants


## D56.activity_termwise_no_backfill — No backfill: final Lemma 3 cannot prove termwise activity estimates

**Status:** `experimental_operational_formula`
**Risk:** low

```text
Reject any proof of termwise_estimate that cites final |H(Z)| bound as input. Termwise estimates must come before summation/resummation.
```

**Why it matters:** Prevents circular proof of the activity route.

**Proof route:** Patch reviewer checks imports and theorem dependencies; oracle alone cannot detect conceptual circularity if hypotheses are renamed.

**Blockers:**
- Needs dependency audit if imported through several wrappers


## D57.gaussian_root_hessian_order_guard — Gaussian/root/Hessian order-of-operations guard

**Status:** `experimental_planning_formula`
**Risk:** medium

```text
Order: Wilson-Hessian identification -> strict precision/coercivity -> covariance inverse -> covariance root -> Gaussian pushforward -> activity construction. Do not swap pushforward before root/covariance identity.
```

**Why it matters:** Separates physical operator construction from measure transport and avoids assuming a root with no identified covariance.

**Proof route:** Use source assumptions fields as a dependency graph; require a dependency edge for each promotion.

**Blockers:**
- Full physical YM Hessian remains open


## D58.r_operation_local_to_scalar_quantifier_split — R-operation local-to-scalar quantifier split

**Status:** `experimental_derived_formula`
**Risk:** medium-high

```text
Local bound |R_k(X)| <= A_k exp(-κ d(X)) plus pinned/intersection summability implies scalar |Rsc(t,k)| <= A'_k exp(-c t) only after a target/root summation dictionary.
```

**Why it matters:** Prevents rewriting polymer-local bounds as scalar geometric tails without the missing summation bridge.

**Proof route:** Create a record with local_decay, target_dictionary, pinned_sum, scalar_identity fields.

**Blockers:**
- Exact Rsc identity and target relation remain open


## D59.flow_ir_decoupler — Flow/IR decoupler: marginal logarithmic flow is not irrelevant geometric flow

**Status:** `experimental_planning_formula`
**Risk:** medium

```text
Keep two lanes: irrelevant geometric g_k <= C r^k for existing lattice closure; marginal asymptotic freedom g_k ~ 1/log k for continuum-facing route. Do not substitute one for the other.
```

**Why it matters:** Protects the existing strong lattice assembly while acknowledging the real 4D marginal coupling issue.

**Proof route:** Require theorem names to include geometric or marginal; reject ambiguous coupling-flow claims.

**Blockers:**
- Continuum/marginal route remains open


## D60.final_frontier_vector_norm — Final hRpoly frontier as a vector norm, not one opaque hypothesis

**Status:** `experimental_operational_formula`
**Risk:** low as audit; high if treated as theorem progress

```text
hRpoly debt vector = [gaussian_pushforward, root_localization, wilson_hessian, local_activity, raw_pointwise_decay, support, ultralocal_integral, rooted_remainder_identity, profile_bound, flow]. Progress is L0 decrease in this vector.
```

**Why it matters:** Turns the huge frontier into auditable components and avoids claiming full hRpoly from one component.

**Proof route:** Map each BalabanCMP116SourceAssumptions field to proof cards and contracts; require explicit remaining debt after each patch.

**Blockers:**
- Some fields are much harder than others; weight vector should be calibrated



# v5 cards D61-D75

## D61.closed_loop_patch_intake — Patch intake as the unit of agent output

```text
Delta_patch -> score_patch
```

Every agent output is represented as a JSON delta vector with removed_fields, source_promotions, theorem_checked_promotions, toy_theorems and penalties.

## D62.source_lock_before_promotion — Source lock before source_extracted promotion

```text
source_pending + lock_complete => source_extracted_candidate
```

A formula promotion requires exact printed/PDF page, equation range, assumptions, constants, dictionary and use_for/do_not_use_for.

## D63.router_sync_invariant — Source-key router sync invariant

```text
source_key -> proof_card -> lean_targets
```

Every source key used by a patch maps to exactly the intended proof card and Lean target subset.

## D64.build_oracle_gate_vector — Build/oracle gate as evidence vector

```text
theorem_checked = theorem ∧ removed_premise ∧ build ∧ oracle
```

A theorem_checked promotion is a triple: theorem name, removed premise, build/oracle evidence.

## D65.eq231_three_skeletons_before_proof — Eq. (2.31) three skeletons before proof

```text
S = {mem_iff, subset, admissible_iff}
```

Write separate skeletons for mem_iff_source, source_subset_gapCarrier and admissible_iff_source before filling any of them.

## D66.no_ocr_formula_component — No OCR-derived formula component

```text
OCR_only(component) => blocker(component)
```

Any sign, exponent, constant or summation domain whose only evidence is OCR remains a blocker, not a formula.

## D67.patch_score_lower_bound — Patch score lower bound

```text
score>=10 ∧ positive_delta>=1
```

A patch is acceptable only if the positive delta beats penalties and contains at least one real hypothesis/source movement.

## D68.failed_extraction_is_progress_if_blocker_sharpens — Failed extraction can be progress if blocker sharpens

```text
failure + sharper_blocker > wrapper
```

No-patch output is useful only when it narrows the missing source lemma and updates remaining_blockers.

## D69.theorem_statement_checksum — Theorem statement checksum

```text
sha256(statement_before)=sha256(statement_after)
```

Hash theorem statement text before proof attempts so agents do not silently change the target after failing.

## D70.eq237_two_premise_lock — Eq. (2.37) two-premise lock

```text
fixed_Z0p ∧ final_sum => postP_bound
```

Keep fixed-Z0' estimate and final Z0' summation as two source premises feeding one consumer; do not split beyond source order.

## D71.cammarota_threshold_dependency_vector — Cammarota threshold dependency vector

```text
threshold = f(dim, metric, activities, constants)
```

Record all threshold dependencies for K large / alpha6 small before attempting a Lean scale-bound theorem.

## D72.termwise_before_final_sum_dependency — Termwise before final sum dependency

```text
termwise -> resummation -> final
```

Activity termwise estimates must appear upstream of Lemma 3 final bound, never backfilled from it.

## D73.r_operation_target_root_sum_needed — R-operation target/root sum needed

```text
local_R + target_sum + Rsc_identity => scalar_Rsc
```

A polymer-local R bound becomes scalar Rsc only after target dictionary and root/pinned summation.

## D74.pr_template_as_guardrail — PR template as mathematical guardrail

```text
PR = proof_card + delta + evidence + blockers
```

A PR must name the proof card, source keys, removed field, build/oracle status and remaining blocker vector.

## D75.hypothesis_burndown_as_dashboard — Hypothesis burndown dashboard

```text
progress = -Δ unresolved_fields
```

Track hRpoly as a vector of component fields; progress is a decrease in unresolved components, not a new wrapper count.
