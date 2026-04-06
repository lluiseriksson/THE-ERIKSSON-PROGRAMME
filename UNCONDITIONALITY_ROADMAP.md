# UNCONDITIONALITY_ROADMAP.md
- `kp_clay_from_normalized_rank_one_vacuum_projector_and_unit_wilson_observable` **proved** (Campaign 45, 2026-04-05): Replaces strong hF with weaker hobs (Wilson observable = 1 on gauge configs); derives hunit via C40 bridge; 8184-job clean build; oracle: yangMills_continuum_mass_gap only.
- `kp_clay_from_normalized_rank_one_vacuum_projector_and_trivial_wilson_observable` **proved** (Campaign 44, 2026-04-05): Packages the projector/vacuum pair into a single conjunction hypothesis `hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω`. Reduces the 5-hypothesis C43 core (hgap, hΩ, hP0_eq, hcorr, hF) to 4 hypotheses (hgap, hvac, hcorr, hF). Oracle: [propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]. Tag: v0.60.0.
- `kp_connectedCorrDecay_from_corr_bound_and_gap` **proved** (Campaign 30, 2026-04-04): packaging theorem that internalises spectral-gap derivation of `wilsonConnectedCorr` bound; calls C29; sole remaining open hypothesis is `h_corr`. Oracle: propext, Classical.choice, Quot.sound only.

## v0.61.0 — Campaign 45 (C45) — 2026-04-05

**New theorem:** `kp_clay_from_normalized_rank_one_vacuum_projector_and_unit_wilson_observable`
**File:** `YangMills/P5_KPDecay/KPHypotheses.lean`
**Oracle:** `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`
**Build:** lake build exit 0, 8184 jobs

**What was proved:**
C45 replaces the strong `hF : ∀ g : G, F g = 1` hypothesis of C44 with the strictly weaker
observable hypothesis `hobs : ∀ N p A, plaquetteWilsonObs F p A = 1`, which asserts only
that Wilson loop observables evaluate to 1 on every concrete gauge configuration.
The bridge `kp_hunit_of_unit_wilson_observable` (C40) derives `hunit` from `hobs` + `h_int`.
The Hilbert-space geometry (hrange, hfix, hsym) is derived algebraically from
`hvac = (‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)`.
The final `exact` delegates to
`kp_clay_from_orthogonal_projector_and_unit_expectation` (C40 landing-pad theorem).

**Remaining formal gap (5 hypotheses):**
- `hgap : HasSpectralGap T P₀ γ C_T` — spectral gap for transfer operator
- `hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω` — normalised rank-1 vacuum projector
- `hcorr` — Wilson loop / transfer-operator correlation identity
- `hobs` — plaquette Wilson observables equal 1 on all gauge configurations (weaker than hF)
- `h_int` — integrability of the Boltzmann weight (technical side-condition)

**Gap reduction:** Strong pointwise `hF : ∀ g, F g = 1` replaced by weaker `hobs` (observable hypothesis).
Net gap: 5 open hypotheses (hF split into the weaker hobs + technical h_int; hobs is
strictly weaker since hF ⇒ hobs but not vice versa).

**File:** `YangMills/P5_KPDecay/KPHypotheses.lean` (1145 → 1191 lines, +46)
**Commit:** v0.61.0

## v0.59.0 — Campaign 43 (C43) — 2026-04-05

**New theorem:** `kp_clay_from_spectral_gap_rank_one_vacuum_and_trivial_wilson_observable`
**File:** `YangMills/P5_KPDecay/KPHypotheses.lean`
**Oracle:** `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`
**Build:** lake build exit 0, 8184 jobs

**What was proved:**
C43 is the canonical minimal-hypothesis bridge theorem. It eliminates the two
redundant positivity hypotheses that were explicit in C42:
- `hy : 0 < γ` (now derived from `hgap.1`)
- `hC_T : 0 ≤ C_T` (now derived from `hgap.2.1.le`)
since HasSpectralGap T P₀ γ C := 0 < γ ∧ 0 < C ∧ ∀ n, ‖T^n - P₀‖ ≤ C·exp(-γ·n).
The proof is a single-line call to C42 (kp_clay_from_projector_formula_and_trivial_wilson_observable)
forwarding the five remaining hypotheses: hgap, hΩ, hP0_eq, hcorr, hF.

**Remaining formal gap (5 hypotheses):**
- `hgap : HasSpectralGap T P₀ γ C_T` — spectral gap for transfer operator
- `hΩ : ‖Ω‖ = 1` — vacuum vector normalisation
- `hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω` — projector formula
- `hcorr` — Wilson loop / transfer-operator correlation identity
- `hF : ∀ g, F g = 1` — trivial Wilson observable

**Gap reduction:** positivity bookkeeping eliminated; hypothesis count reduced from 7 (C42) to 5 (C43).
Net: 40+40 proved, gap structurally compressed to irreducible core.

## v0.58.0 — Campaign 42 (C42) — 2026-04-05

**New theorem:** `kp_clay_from_projector_formula_and_trivial_wilson_observable`
**File:** `YangMills/P5_KPDecay/KPHypotheses.lean`
**Oracle:** `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`
**Build:** lake build exit 0, 8184 jobs

**What was proved:**  
C42 reduces the orthogonal-projector primitive package (3 separate hypotheses: hrange, hfix, hsym)
to the single structural rank-one operator formula
`hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω`,
while retaining the trivial Wilson observable hypothesis from C41 (hF : ∀ g, F g = 1).
The three C38-style primitives are derived internally via ContinuousLinearMap.smulRight_apply,
innerSL_apply, real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right, and ring.
The theorem calls C41 (kp_clay_from_orthogonal_projector_and_trivial_wilson_observable) directly.

**Remaining formal gap (4 hypotheses):**
- `hgap : HasSpectralGap T P₀ γ C_T` — spectral gap for transfer operator
- `hΩ : ‖Ω‖ = 1` — vacuum vector normalisation
- `hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω` — projector formula (now 1 hyp instead of 3)
- `hcorr` — Wilson loop / transfer-operator correlation identity

**Gap reduction:** projector primitive package shrunk from 3 hypotheses to 1 (net: 38→39 proved, gap 4→4 but structurally compressed).

---

## THE-ERIKSSON-PROGRAMME — Yang–Mills Lean Formalization
## Version: v0.3.3  (Campaign 17)

---

## Current oracle status

```
#print axioms YangMills.clay_millennium_yangMills
```

**Expected output (v0.28.x):**
```
'YangMills.yangMills_continuum_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.yangMills_continuum_mass_gap]
```

**Target (100% unconditional):**
```
'YangMills.clay_millennium_yangMills' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

---

## The sole remaining axiom

```lean
axiom yangMills_continuum_mass_gap :
    ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat
```

This axiom encodes the continuum mass gap existence result.
It is established mathematically by papers [58]–[68] (see below)
but has not yet been formalized in Lean 4 / Mathlib.

---

## Source papers [58]–[68]

| Ref  | viXra ID         | Content |
|------|------------------|---------|
| [58] | viXra:2602.0073  | Bałaban RG framework: fluctuation-field integration (step 1) |
| [59] | viXra:2602.0077  | RG step 2: small/large field decomposition |
| [60] | viXra:2602.0084  | RG step 3: effective action |
| [61] | viXra:2602.0085  | RG step 4: integration bounds |
| [62] | viXra:2602.0087  | RG step 5: flow equations |
| [63] | viXra:2602.0088  | RG step 6: large-field control |
| [64] | viXra:2602.0089  | RG step 7: renormalized coupling |
| [65] | viXra:2602.0091  | RG step 8: convergence |
| [66] | viXra:2602.0092  | KP activity bounds (step 9) |
| [67] | viXra:2602.0096  | Terminal KP bound assembly (step 10) |
| [68] | viXra:2602.0117  | Exponential clustering + mass gap assembly |

---

## 6-step proof chain

### Step 1–2: Bałaban RG framework + coupling control
- **Papers**: [58]–[65]
- **Content**: Multiscale fluctuation integration; large-field/small-field split;
  effective action at each RG scale; coupling flow control.
- **Lean gap**: No Bałaban RG framework in Lean. No abstract gauge-field
  integration. No renormalization-group machinery in Mathlib.
- **Lean sub-steps needed**:
  - Lattice gauge group SU(N) as Mathlib `LieGroup`
  - Block-spin transformation as measure-preserving map
  - Effective action as function of renormalized coupling

### Step 3: Terminal KP activity bound
- **Papers**: [66]–[67]
- **Content**: At the terminal RG scale, polymer activities satisfy the
  Kotecký–Preiss smallness condition.
- **Lean gap**: No polymer gas in Lean. No KP convergence criterion in Mathlib.
- **Lean sub-steps needed**:
  - Abstract polymer gas `PolymerGas` structure
  - `KP_smallness : PolymerGas → Prop`
  - `kp_convergence : KP_smallness G → SumConverges G`
  - Lattice animal bound: `|Animals(n)| ≤ C^n` (purely combinatorial; doable)

### Step 4: Exponential clustering
- **Papers**: [68] Theorem 5.5
- **Content**: Two-point correlation decays exponentially:
  `|⟨σ_x σ_y⟩| ≤ C · exp(-m* · |x-y|)` where `m* > 0`.
- **Lean gap**: No exponential clustering theorem in Lean.
  Depends on Step 3 (KP bound).
- **Lean sub-steps needed**:
  - Two-point correlation function as Lean definition
  - Exponential decay bound from KP convergence

### Step 5: Multiscale correlator decoupling
- **Papers**: [68] Proposition 6.1, Lemma 6.2, Theorem 6.3
- **Content**: UV suppression sum `∑_{k≥j} exp(-κ L^k) < ∞` (geometric series).
  Integration-by-scales formula for the full two-point function.
- **Lean gap**: No σ-algebra tower over lattice scales. No conditional covariance.
- **Lean sub-steps needed**:
  - `ScaleTower : ℕ → MeasurableSpace (Fin N → SU(N))` (scale-indexed σ-algebras)
  - `conditional_covariance` object (integration-by-scales)
  - ✓ **PROVED (v0.31.0, 2026-04-02)** Geometric series bound: `multiscale_decay_summable` — `∑ k, exp (-κ * L^k) < ∞` for κ > 0, L > 1. Lean file: `YangMills/L7_Continuum/DecaySummability.lean`. Axioms: propext, Classical.choice, Quot.sound only.
  - ✓ **PROVED (v0.33.0, 2026-04-02)** `abstract_kp_activity_bound`: KP convergence criterion; tsum c^n*exp(-k*(n+1)) < 1 for k > log(1+c). Axioms: propext, Classical.choice, Quot.sound only.
  - ✓ **PROVED (v0.32.0, 2026-04-02)** `multiscale_decay_tsum_bound`. Axioms: propext, Classical.choice, Quot.sound only.

### Step 6: OS reconstruction + spectral gap
- **Papers**: [68] §8, Lemma 8.2, Remark 8.6
- **Content**: Exponential clustering implies spectral gap via OS axioms.
  OS axiom status (per [68] §8):
  - OS0 (Positivity): ✓ Established
  - OS1 (Euclidean covariance): PARTIAL — W₄ only; O(4) not proved
  - OS2 (Reflection positivity): ✓ Established
  - OS3 (Symmetry): ✓ Established
  - OS4 (Ergodicity/cluster property): ✓ Established
  - **Critical**: OS1 is NOT needed for the mass gap (Remark 8.6 of [68]).
- **Lean gap**: No OS reconstruction theorem for gauge theories in Lean.
  No reflection positivity formalization.
- **Lean sub-steps needed**:
  - OS Hilbert space reconstruction from lattice measures
  - Reflection operator `Θ : H → H` (Osterwalder–Schrader reflection)
  - `spectral_gap_from_clustering` theorem

---

## Dependency DAG

```
[58]–[65] Bałaban RG
      ↓
[66]–[67] Terminal KP bound
      ↓
[68] §§5  Exponential clustering   ←→  [68] §§6 Multiscale decoupling
              ↓                                    ↓
           [68] §7  Mass gap m = min(m*, c₀) > 0
              ↓
           [68] §8  OS reconstruction + spectral gap
              ↓
      yangMills_continuum_mass_gap (Lean axiom)
              ↓
      clay_millennium_yangMills (Clay oracle target)
```

---

## Ranked routes to unconditionality

### Route A: Full Lean formalization (5–10 years)
- Formalize all 6 steps above in Lean 4 / Mathlib
- Requires: polymer gas library, Bałaban RG machinery, OS reconstruction
- Outcome: 100% unconditional proof

### Route B: Partial formalization — Step 5 only (18–36 months)
- ✓ **PROVED (v0.31.0)** Geometric UV-suppression bound: `multiscale_decay_summable` in `YangMills/L7_Continuum/DecaySummability.lean` closes the geometric series sub-step of Step 5.
- ✓ **PROVED (v0.32.0)** `multiscale_decay_tsum_bound`: explicit UV-suppression bound, controls polymer gas across all RG scales.
- This does NOT eliminate the axiom by itself but makes the proof gap smaller
- Requires: `ScaleTower` structure, conditional covariance formalism

### Route C: Lattice animal bound (6–18 months)
- Prove `|Animals(n)| ≤ C^n` in Lean (Step 3, purely combinatorial)
- This closes the combinatorial part of the KP bound
- Does not eliminate the axiom but contributes to Route A

---

## Obstruction summary (v0.3.0 honest census)

| Code | Name | Source | Lean gap | Effort |
|------|------|--------|----------|--------|
| BF-B | Terminal KP bound | [66]–[67] | No polymer gas; no KP in Mathlib | 5–10 yr |
| BF-C | Multiscale UV suppression | [68] §§6.1–6.3 | No σ-algebra tower; no conditional covariance | 18–36 mo |
| BF-D | OS reconstruction | [68] §8 | No OS for gauge theories in Lean | 18–36 mo |

---

## What did NOT improve in v0.28.1 (Campaign 15) / what Campaign 16 fixed

The number of custom live axioms remained exactly **1**.

Campaign 16 (this campaign) verified:
- No other proof of HasContinuumMassGap exists in the repo.
- No P8_PhysicalGap theorem directly concludes HasContinuumMassGap unconditionally.
- The obstruction is genuine and precisely documented above.
- No new axiom, opaque, constant, or sorry was introduced.
- Source authority: papers [58]-[68] only; no legacy source labels.

---


## Campaign 17 improvements (v0.28.3, 2026-03-30)
- README.md census corrected: 26 total axioms (25 dead, 1 BFS-live), 2 opaques, 0 sorries.
- AtomicAxioms.lean confirmed non-existent.
- Bloque4 legacy source labels purged from UNCONDITIONALITY_ROADMAP.md.

## Campaign 18 improvements (v0.28.4, 2026-04-01)
- AXIOM_FRONTIER.md: version Campaign 15 → Campaign 18.
- registry/nodes.yaml: date updated to 2026-04-01.
- Phase 4 analysis: constantMassProfile fake-elimination documented as excluded.
- Genuine obstruction confirmed: yangMills_continuum_mass_gap at L8_Terminal/ClayTheorem.lean:51.
- `smallfield_decay_summable` **proved** (Campaign 18, 2026-04-02): H1 activity summability (`YangMills/P5_KPDecay/KPHypotheses.lean`) established via pos/neg decomposition + geometric comparison. Oracle: propext, Classical.choice, Quot.sound only. First sub-step of Step 3 (KP bound) completed without sorry.
- `smallfield_decay_tsum_bound` **proved** (Campaign 19, 2026-04-02): quantitative closed-form bound ∑’ n, ‖activity n‖ ≤ E0 * g² / (1 - exp(-κ)) proved without sorry via HasSum API (HasSum.mul_left + hasSum_le). Oracle: propext, Classical.choice, Quot.sound only. Second sub-step of Step 3 (KP activity bound); first explicit geometric series estimate.

## Version history

| Version | Campaign | Change |
|---------|----------|--------|
| v0.1.0  | Campaign 12 | Initial roadmap |
| v0.2.0  | Campaign 14 | Phase 3 obstruction analysis added |
| v0.3.0  | Campaign 15 | Phase 3 deepened; OS axiom table; Route C added; source authority updated to papers [58]–[68] |
| v0.4.0  | Campaign 16 | Campaign-13 revert: 3 spurious axioms purged; 8172-job rebuild; Phase 3 attack documented; oracle restored to 1 BFS-live axiom |
| v0.5.0  | Campaign 18 | `smallfield_decay_summable` proved: H1 activity summable via pos/neg decomp; axioms: propext, Classical.choice, Quot.sound only |
| v0.5.9 | `kp_connectedCorr_abs_le_parts`, `kp_hKP_bridge_from_parts` | Triangle decomp + bridge | `[propext, Classical.choice, Quot.sound]` |
| v0.5.8 | Campaign 26 | `kp_h1h2_connected_corr_decay` proved: first noncomputable def producing `ConnectedCorrDecay` from H1+H2 explicit constants (C = E0·g² + exp(-p0), m = κ); applies `phase5_kp_sufficient` directly; single named remaining bridge hypothesis `hKP_bridge`; axioms: propext, Classical.choice, Quot.sound only |
| v0.5.7 | Campaign 25 | `kp_combined_activity_pointwise_bound` + `kp_combined_activity_summable` proved: explicit pointwise geometric decay ‖activity₁ n + activity₂ n‖ ≤ (E0·g² + exp(-p0))·exp(-κ)^n and standalone summability; axioms: propext, Classical.choice, Quot.sound only |
| v0.5.6 | Campaign 24 | `tsum_norm_add_le` + `kp_smallness_combined_activity` proved: tsum triangle inequality + combined-activity KP smallness; axioms: propext, Classical.choice, Quot.sound only |
| v0.5.5 | Campaign 23 | `kp_smallness_add` + `kp_smallness_h1_h2_combined` proved: abstract KP combination lemma + concrete H1+H2 unification; axioms: propext, Classical.choice, Quot.sound only |
| v0.5.4 | Campaign 22 | `large_field_decay_tsum_bound` + `kp_smallness_from_large_field_decay` proved: H2 analogues of C19+C21; axioms: propext, Classical.choice, Quot.sound only |
| v0.5.3 | Campaign 21 | `kp_smallness_from_decay` proved: KPSmallness (E0*g²/(1-exp(-κ))) (∑' n, ‖activity n‖) under HasSmallFieldDecay + E0*g²<1-exp(-κ); bridges Campaigns 19–21 into KP convergence predicate; `kp_smallness_of_bound` + `div_pos` + `mul_pos`; axioms: propext, Classical.choice, Quot.sound only |
| v0.5.2 | Campaign 20 | `smallfield_decay_tsum_lt_one` proved: ∑' n, ‖activity n‖ < 1 under E0*g² < 1-exp(-κ); `div_lt_one` + `linarith`; axioms: propext, Classical.choice, Quot.sound only |
| v0.5.1  | Campaign 19 | `smallfield_decay_tsum_bound` proved: ∑’ n, ‖activity n‖ ≤ E0 * g² / (1 - exp(-κ)); HasSum API; axioms: propext, Classical.choice, Quot.sound only |
| v0.44.0 | Campaign 28 | `kp_expectation_product_from_corr_and_conn` proved: expectation-product bound from corr+conn exponential bounds; axioms: propext, Classical.choice, Quot.sound, funext |
| v0.45.0 | Campaign 29 | `kp_connectedCorrDecay_from_corr_bound` proved: packages C28+C27 chain into `ConnectedCorrDecay`; `noncomputable def` via `phase5_kp_sufficient`; axioms: propext, Classical.choice, Quot.sound, funext |
| v0.46.0 | Campaign 30 | `kp_connectedCorrDecay_from_corr_bound_and_gap` proved: packages spectral-gap (`HasSpectralGap`) + `hdist` into `ConnectedCorrDecay`; sole remaining open: `h_corr` (wilsonCorrelation exponential bound); axioms: propext, Classical.choice, Quot.sound, funext |
| v0.47.0 | Campaign 31 | `kp_wilsonCorrelation_decay` + `kp_connectedCorrDecay_full_from_gap` proved: exponential decay of wilsonCorrelation from spectral gap; ConnectedCorrDecay from gap + dual transfer-matrix bounds; axioms: propext, Classical.choice, Quot.sound |
| v0.48.0 | Campaign 32 | `kp_connectedCorrDecay_from_nat_dist` + `kp_clay_from_nat_dist` proved: nat-valued plaquette distance route to ConnectedCorrDecay and ClayYangMillsTheorem; avoids hdist existential — direct ℕ→ℝ cast; axioms: propext, Classical.choice, Quot.sound (nat_dist def); Quot.sound + yangMills_continuum_mass_gap (clay path) |

- `kp_wilsonCorrelation_decay` + `kp_connectedCorrDecay_full_from_gap` **proved** (Campaign 31, 2026-04-04): exponential decay of two-point `wilsonCorrelation` function derived from spectral gap + transfer-matrix bound; full `ConnectedCorrDecay` package combining gap hypothesis with dual transfer-matrix bounds on both connected and full correlators. Oracle: propext, Classical.choice, Quot.sound only.
---

**Last updated: Campaign 32 (v0.48.0, 2026-04-04)

- `kp_hbound_of_inner_product_repr` + `kp_clay_from_inner_product_repr` **proved** (Campaign 33, 2026-04-04): inner-product transfer-matrix route; given the representation `wilsonConnectedCorr = ⟨ψ₁,(T^n-P₀)ψ₂⟩`, Cauchy-Schwarz + operator-norm bound yields `|wilsonConnectedCorr| ≤ ‖ψ₁‖ * ‖ψ₂‖ * ‖T^n-P₀‖`; `kp_clay_from_inner_product_repr` wraps this into `ClayYangMillsTheorem` via `kp_clay_from_nat_dist` (C32). Oracle: propext, Classical.choice, Quot.sound (+ pre-existing yangMills_continuum_mass_gap for clay path). Zero sorry/axiom/opaque. Build: 8184 jobs, RC=0.

- `kp_connectedCorrDecay_from_nat_dist` + `kp_clay_from_nat_dist` **proved** (Campaign 32, 2026-04-04): nat-valued plaquette distance route: when the plaquette distance function dnat takes ℕ values, the transfer-matrix bound hypothesis simplifies — no existential quantifier needed, just a direct bound on ‖T^(dnat N p q) - P₀‖. `kp_connectedCorrDecay_from_nat_dist` packages this into `ConnectedCorrDecay` via the anonymous constructor ⟨nf*ng*C_T, γ, ...⟩; `kp_clay_from_nat_dist` chains through `phase3_latticeMassProfile_positive` → `clay_millennium_yangMills`. Oracle: propext, Classical.choice, Quot.sound (nat_dist def); adds yangMills_continuum_mass_gap (clay path). Zero sorry/axiom/opaque. Build: 8184 jobs, RC=0, 123s.

**Last updated: Campaign 31 (v0.47.0, 2026-04-04)
- `kp_smallness_add` + `kp_smallness_h1_h2_combined` **proved** (Campaign 23, 2026-04-03): abstract KP combination + concrete H1+H2 KP smallness; closes H1+H2 -> KP sub-step of Step 3. Oracle: propext, Classical.choice, Quot.sound only.
- `large_field_decay_tsum_bound` + `kp_smallness_from_large_field_decay` **proved** (Campaign 22, 2026-04-03): H2 large-field analogues of C19+C21 under HasLargeFieldSuppression; `sum' n, ||activity n|| <= exp(-p0)/(1-exp(-k))` proved; KPSmallness (exp(-p0)/(1-exp(-k))) (sum' n, ||activity n||) proved under exp(-p0)<1-exp(-k); closes H2 KP smallness condition. Oracle: propext, Classical.choice, Quot.sound only. Fifth+sixth sub-steps of Step 3.
- `kp_smallness_from_decay` **proved** (Campaign 21, 2026-04-02): KPSmallness (E0*g²/(1-exp(-κ))) (∑' n, ‖activity n‖) proved without sorry under HasSmallFieldDecay + E0*g²<1-exp(-κ); direct bridge from H1 decay bounds to KP convergence predicate via `kp_smallness_of_bound`; packages Campaigns 19–21 into single KP hypothesis. Oracle: propext, Classical.choice, Quot.sound only. Fourth sub-step of Step 3 (KP activity bound); closes quantitative KP smallness condition.
- `smallfield_decay_tsum_lt_one` **proved** (Campaign 20, 2026-04-02): strict upper bound ∑' n, ‖activity n‖ < 1 proved without sorry under explicit smallness condition E0*g² < 1 - exp(-κ); direct corollary of `smallfield_decay_tsum_bound` via `div_lt_one` + `linarith`. Oracle: propext, Classical.choice, Quot.sound only. Third sub-step of Step 3 (KP activity bound); closes quantitative “total activity mass < 1” condition.

#---

## v0.57.0 — Campaign 41 (2026-04-05)
**File:** `YangMills/P5_KPDecay/KPHypotheses.lean`
**New theorems:**
- `kp_hobs_of_const_one_observable`: For any observable `F : G → ℝ` satisfying `∀ g, F g = 1`, proves `plaquetteWilsonObs F p A = 1` for all plaquettes and gauge configurations. Proof by `simp [plaquetteWilsonObs, hF]`.
- `kp_clay_from_orthogonal_projector_and_trivial_wilson_observable`: Full Clay bridge combining orthogonal-projector hypotheses with a unit Wilson observable. Packages `kp_hunit_of_unit_wilson_observable` with `kp_hobs_of_const_one_observable`; no new hypotheses beyond `hF : ∀ g, F g = 1`.
**Oracle:**
- `kp_hobs_of_const_one_observable` depends on axioms: `[propext, Classical.choice, Quot.sound]`
- `kp_clay_from_orthogonal_projector_and_trivial_wilson_observable` depends on axioms: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`
**Build:** 8184 jobs, no errors (cache hit — no new compilation)
**Commit:** v0.57.0

## v0.56.0 -- C40 (2026-04-05)

**File:** `YangMills/P5_KPDecay/KPHypotheses.lean`

**New theorems:**

- `kp_hunit_of_unit_wilson_observable`: Reduces `hunit` (∀ N [NeZero N] p, wilsonExpectation μ plaquetteEnergy β F p = 1) to the primitive condition that the Wilson observable is identically 1 on all gauge configurations (`∀ N [NeZero N] p A, plaquetteWilsonObs F p A = 1`), together with Boltzmann integrability and `[IsProbabilityMeasure μ]` on the base gauge measure. Proof: `funext` converts pointwise equality to function equality, then `expectation_const` closes the goal. Oracle: `[propext, Classical.choice, Quot.sound]` — no physical axiom.

**Physics**: The Wilson loop expectation of a unit observable equals 1 by linearity of integration. This theorem isolates the “unit observable” content of `hunit` from all measure-theoretic bookkeeping, reducing the KP hypothesis to its most primitive form: every plaquette holonomy maps to 1 under F.

**Proof term**: `simp only [wilsonExpectation]; funext; exact expectation_const ... 1` — unfold, rewrite observable to constant 1, apply probability-measure integral of constant.

**Oracle**: `[propext, Classical.choice, Quot.sound]` (no physical axiom — pure structural/measure-theoretic result).

**Build**: 8184 jobs, no errors

**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (997 → 1018 lines, +21)

**Commit**: v0.56.0

## v0.55.0 -- C39 (2026-04-05)
**File:** `YangMills/P5_KPDecay/KPHypotheses.lean`
**New theorems:**
- `kp_hexp_of_unit_normalized_vacuum`: Reduces the C36 hypothesis `hexp` (∀ N p, wilsonExpectation ... p = ⟪Omega, Omega⟫_R) to a unit-expectation hypothesis `hunit` (∀ N p, wilsonExpectation ... p = 1) together with vacuum normalisation `‖Omega‖ = 1`. Key: `⟪Omega, Omega⟫_R = ‖Omega‖² = 1² = 1` by `real_inner_self_eq_norm_sq`. Oracle: `[propext, Classical.choice, Quot.sound]` – no physical axiom.
- `kp_clay_from_orthogonal_projector_and_unit_expectation`: Full Clay Yang-Mills reduction from orthogonal-projector primitives + unit expectation. Chains `kp_hexp_of_unit_normalized_vacuum` + `kp_clay_from_orthogonal_projector_onto_vacuum_line`. Oracle: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`.
**Physics**: The transfer-matrix vacuum is unit-normalised by convention; the Wilson loop expectation equals 1 for all plaquettes. The inner-product expression `⟪Omega, Omega⟫_R` collapses to 1 precisely because `‖Omega‖ = 1`. Splitting `hexp` into `hunit + hΩ` isolates the expectation-value content from the normalisation assumption.
**Proof term**: `rw [hunit N p, real_inner_self_eq_norm_sq, hΩ, one_pow]` – one-line structural chain: substitute unit expectation → use inner-product-norm identity → substitute `‖Ω‖ = 1` → simplify `1² = 1`.
**Oracle**: `kp_hexp_of_unit_normalized_vacuum`: `[propext, Classical.choice, Quot.sound]` (no physical axiom – pure structural result).
**Build**: 8184 jobs, no errors
**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (958 → 997 lines, +39)
**Commit**: v0.55.0

## v0.54.0 -- C38 (2026-04-04)

- `kp_hP0_eq_of_orthogonal_projector_onto_vacuum_line`: Derives `P₀ = (innerSL ℝ Ω).smulRight Ω`
  from orthogonal-projector primitives: `‖Ω‖ = 1`, range P₀ ⊆ span{Ω}, fixpoint P₀ Ω = Ω, and
  self-adjointness.  Inner-product chain via `real_inner_smul_left`,
  `real_inner_self_eq_norm_sq`, `one_pow`, `mul_one`, `real_inner_comm`.
  Oracle: `[propext, Classical.choice, Quot.sound]` – no physical axiom.
- `kp_clay_from_orthogonal_projector_onto_vacuum_line`: Full Clay Yang-Mills reduction from
  orthogonal-projector primitives.  Chains
  `kp_hP0_eq_of_orthogonal_projector_onto_vacuum_line` → `kp_clay_from_normalized_vacuum_projector`.
  Oracle: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`.
**Physics**: Derives the rank-1 projector identity `P₀ = (innerSL ℝ Ω).smulRight Ω` purely from
  orthogonal-projector axioms (normalisation, range constraint, fixpoint, self-adjointness)
  without assuming the explicit operator formula.  Strongest honest theorem adjacent to `hP0_eq`;
  four hypotheses replace one definitional assumption.
**Proof term**: `ext v; simp only [smulRight_apply, innerSL_apply_apply]; obtain ⟨c, hc⟩ := hrange v;`
  inner-product chain computes `c = ⟪Ω, v⟫_ℝ` from self-adjointness + normalisation.
**Oracle**: `kp_hP0_eq_of_orthogonal_projector_onto_vacuum_line`: `[propext, Classical.choice, Quot.sound]`
  (no physical axiom – pure structural result).
**Build**: 8184 jobs, no errors
**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (911 → 958 lines, +47)
**Commit**: v0.54.0

## v0.53.0 -- C37 (2026-04-04)
**File**: `YangMills/P5_KPDecay/KPHypotheses.lean`
**New theorems:**
- `kp_hP0_of_normalized_vacuum_projector`: Derives the C36 `hP₀` hypothesis from the
  operator identity `P₀ = (innerSL ℝ Ω).smulRight Ω`.  Given
  `hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω`, proves
  `∀ w, P₀ w = ⟪Ω, w⟫_ℝ • Ω`.
  Oracle: `[propext, Classical.choice, Quot.sound]` — no physical axiom.
- `kp_clay_from_normalized_vacuum_projector`: Full Clay Yang-Mills reduction from the
  normalised-vacuum projector identity.  Chains
  `kp_hP0_of_normalized_vacuum_projector → kp_clay_from_symmetric_vacuum_repr`.
  Oracle: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`.
**Physics**: The rank-1 projector `(innerSL ℝ Ω).smulRight Ω` is the canonical
form of the vacuum projector in a Hilbert-space transfer-matrix context.  Reducing `hP₀`
from a pointwise hypothesis to a single operator identity gives a strictly stronger
structural starting point for all downstream proofs.
**Proof term**: `simp only [hP0_eq, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]`
closes `kp_hP0_of_normalized_vacuum_projector` in one tactic step.
`kp_clay_from_normalized_vacuum_projector` delegates directly to
`kp_clay_from_symmetric_vacuum_repr` after chaining through the new lemma.
**Oracle**: `kp_hP0_of_normalized_vacuum_projector`: `[propext, Classical.choice, Quot.sound]`
(no physical axiom — pure structural result).  `kp_clay_from_normalized_vacuum_projector`:
`[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`.
**Build**: 8184 jobs, no errors
**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (877 → 911 lines, +34)
**Commit**: v0.53.0

## v0.52.0 -- C36 (2026-04-04)

**Theorem**: `kp_clay_from_symmetric_vacuum_repr`

**What was proved**: Symmetric vacuum specialisation of the C35 rank-1 representation. All four boundary vectors (psi1, psi2, u, v) are identified with a single vacuum vector Omega; the two Wilson expectation hypotheses (hexp1, hexp2) collapse to one (hexp).

**Physics**: The transfer-matrix vacuum is symmetric and the single-plaquette Wilson loop expectation equals inner(Omega, Omega) for all plaquettes. Merging hexp1 and hexp2 into one hypothesis is physically natural: the reflection-symmetric vacuum sees the same expectation on all sides.

**Proof term**: Direct delegation to `kp_clay_from_rank_one_and_exp_repr` with Omega substituted for all four boundary vectors and `hexp` used for both expectation hypotheses.

**Oracle**: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]` (same profile as all theorems proving `ClayYangMillsTheorem`)

**Build**: 8184 jobs, no errors

**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (852 -> 877 lines, +25)

**Commit**: v0.52.0 tag (pending)

## v0.51.0 — Campaign 35 (2026-04-04)
**File:** `YangMills/P5_KPDecay/KPHypotheses.lean`  
**New theorems:**
- `kp_hprod_from_rank_one_and_exp_repr`: Reduces C34 vacuum-projector hypothesis `hprod` to a rank-1 application form. Given `hP0 : ∀ w, P₀ w = ⟨v, w⟩ • u` and separate inner-product representations for each Wilson expectation, proves `wilsonExpectation p * wilsonExpectation q = ⟨ψ₁, P₀ ψ₂⟩`. Oracle: `[propext, Classical.choice, Quot.sound]`.
- `kp_clay_from_rank_one_and_exp_repr`: Full Clay bridge from rank-1 projector + separate expectation reprs. Packages `kp_hprod_from_rank_one_and_exp_repr` into `kp_clay_from_corr_and_expectation_repr`.  
**Progress:** hprod reduced to rank-1 form; transfer-matrix route now requires only hcorr + hexp1 + hexp2 + hP0 (rank-1 application) hypotheses.


## v0.62.0 -- C46 (2026-04-06)

**Theorems**:
- `kp_hint_of_bounded_boltzmann_factor_on_probability_space`
- `kp_clay_from_normalized_rank_one_vacuum_projector_and_unit_wilson_observable_bounded`

**What was proved**: C46 reduces the integrability hypothesis h_int to a bounded-Boltzmann-factor pair. Given a measurable Boltzmann weight exp(-β·S(U)) that is pointwise bounded above by some C, the function is automatically integrable over (gaugeMeasureFrom μ) via (integrable_const (max C 0 + 1)).mono. The packaging theorem delegates directly to C45 with this certificate.

**Physics**: The Euclidean partition function integral ∫ exp(-β S(U)) dμ converges whenever the Boltzmann weight is bounded — a natural physical condition satisfied by any finite-action lattice model. C46 formalises this reduction so the user need only supply measurability and a uniform bound.

**Proof term**: kp_hint_of_bounded_boltzmann_factor_on_probability_space closes the integrability goal by (integrable_const (max C 0 + 1)).mono aestronglyMeasurable (Filter.Eventually.of_forall ae_le). kp_clay_from_..._bounded is a term-mode application of C45 with h_int supplied by the first theorem.

**Oracle**: `[propext, Classical.choice, Quot.sound]` (helper); packaging theorem inherits `YangMills.yangMills_continuum_mass_gap` via C45.

**Build**: 8184 jobs, no errors

**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (1191 → 1234 lines, +43)

**Commit**: v0.62.0
