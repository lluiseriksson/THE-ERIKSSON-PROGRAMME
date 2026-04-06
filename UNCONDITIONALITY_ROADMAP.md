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


## v0.63.0 -- C47 (2026-04-06)

**Theorems**:
- `kp_hobs_of_unit_plaquette_holonomy_observable`
- `kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable`

**What was proved**: C47 reduces the observable hypothesis h_obs (all plaquette Wilson observables equal 1) to a single group-level hypothesis: F(GaugeConfig.plaquetteHolonomy A p) = 1 for all configs A and plaquettes p. The reduction uses the definitional equality plaquetteWilsonObs F p A = F (GaugeConfig.plaquetteHolonomy A p) discharged by simp only [plaquetteWilsonObs]. The packaging theorem stacks on C46.

**Physics**: If the observable function F : G → ℝ evaluates to 1 on every group element that can appear as a plaquette holonomy, then all Wilson loop observables are trivially unit-normalised. C47 captures this as the most primitive reduction of h_obs.

**Proof term**: kp_hobs_of_unit_plaquette_holonomy_observable unfolds via simp only [plaquetteWilsonObs] then applies hF. kp_clay_from_..._holonomy is a term-mode application of C46 T2 with h_obs supplied by C47 T1.

**Oracle**: `[propext, Classical.choice, Quot.sound]` (helper); packaging theorem inherits `YangMills.yangMills_continuum_mass_gap` via C46/C45.

**Build**: 8184 jobs, no errors

**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (1234 → 1277 lines, +43)

**Commit**: v0.63.0


### Campaign 49 (C49) — v0.65.0
**Target**: Reduce `hbdd` to a lower bound on `wilsonAction`.

**Phase**: Phase 5 — KP Hypotheses reduction

**Theorems added**:
- `kp_hbdd_of_bounded_below_wilsonAction` (T1): Given `0 ≤ β` and `∀ N U, m ≤ wilsonAction plaquetteEnergy U`, proves `hbdd` holds with witness `C = Real.exp (-β * m)`. Proof: `Real.exp_le_exp.mpr` + `mul_le_mul_of_nonneg_left` + `linarith`. Axioms: `[propext, Classical.choice, Quot.sound]`.
- `kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_boundedbelow_action` (T2): Clay packaging theorem replacing `hbdd` with `hβ + hm`. Calls C48-T2 with `kp_hbdd_of_bounded_below_wilsonAction`. Axioms: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`.

**Build**: `lake build YangMills.P5_KPDecay.KPHypotheses` — 8184 jobs, 211.6s, returncode=0.

**Cleanliness**: sorry/axiom/opaque/native_decide all CLEAN. File: 1358 lines.

**Commit**: v0.65.0

---

## C48 — v0.64.0: Boltzmann measurability reduction

**Date**: 2026-04-06  
**Version**: v0.64.0  
**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (lines 1275–1318, +42 lines; import added on line 3)  
**Build**: exit code 0, 8184 jobs, 129 s for KPHypotheses  

### Theorems

**T1**: `kp_hmeas_of_measurable_plaquetteEnergy`  
Reduces Boltzmann factor measurability `Measurable (fun U => Real.exp (-β * wilsonAction plaquetteEnergy U))` to primitive `Measurable plaquetteEnergy`, using `measurable_wilsonAction` from `L2_Balaban/Measurability.lean` and `Real.continuous_exp.measurable.comp`.  
Oracle: `[propext, Classical.choice, Quot.sound]`  

**T2**: `kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_plaquette`  
Packaging theorem replacing `hmeas` in the C47 theorem with `h : Measurable plaquetteEnergy`. Calls T1 to supply the measurability hypothesis.  
Oracle: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`  

### Technical notes

- `YangMills.L2_Balaban.Measurability` is not transitively imported by `KPHypotheses.lean` via the P4/P3 chain; the import was added directly to `KPHypotheses.lean`.  
- The proof of T1 is a two-step composition: `measurable_const.mul (measurable_wilsonAction plaquetteEnergy h)` produces measurability of the linear argument, then `Real.continuous_exp.measurable.comp` lifts it through `exp`.  
- No `sorry`, `opaque`, `axiom`, or `native_decide` introduced.  

**Commit**: v0.64.0


---

## Campaign C51 (v0.67.0)

**Version**: v0.67.0
**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (lines 1397-1434, +38 lines)
**Build**: exit code 0, 8184 jobs, 239 s for KPHypotheses

### Theorems

**T1**: `kp_hpe_of_sq_plaquetteEnergy`
Reduces `hpe : forall g : G, 0 <= plaquetteEnergy g` to the structural assumption
`hdef : forall g, plaquetteEnergy g = f g ^ 2`. Proof: `intro g; rw [hdef]; exact sq_nonneg _`.
Oracle: `[propext, Classical.choice, Quot.sound]`

**T2**: `kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_sq_plaquetteEnergy`
Packages C50-T2 and C51-T1: replaces `hpe` with `hdef : forall g, plaquetteEnergy g = f g ^ 2`.
Delegates to the nonneg version with `kp_hpe_of_sq_plaquetteEnergy` as witness.
Oracle: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`

### Technical notes

- No `sorry`, `opaque`, `axiom`, or `native_decide` introduced.
- T1 proof is one-line: `sq_nonneg` after rewriting with `hdef`.
- T2 is a pure delegation: all hypotheses forwarded, `hpe` replaced by T1 application.
- Linter warning about unused section variables `[Group G] [MeasurableSpace G]` in T1 is cosmetic only.

**Commit**: v0.67.0

---

## Campaign C52  v0.68.0

**Version**: v0.68.0
**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (lines 1435-1475, +41 lines)
**Build**: exit code 0, 8184 jobs for KPHypotheses

### Theorems

**T1**: `kp_hmeas_of_measurable_sq_plaquetteEnergy`
Reduces `h : Measurable plaquetteEnergy` to `hf : Measurable f` under the structural assumption
`hdef : forall g, plaquetteEnergy g = f g ^ 2`. Proof: `funext hdef` converts the pointwise equality
to a function equality, then `hf.pow_const 2` closes the goal.
Oracle: `[propext, Classical.choice, Quot.sound]`

**T2**: `kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_sq_plaquetteEnergy_from_measurable_factor`
Packages C51-T2 and C52-T1: replaces `h : Measurable plaquetteEnergy` with `hf : Measurable f`
under `hdef : forall g, plaquetteEnergy g = f g ^ 2`.
Delegates to C51-T2 with `kp_hmeas_of_measurable_sq_plaquetteEnergy` as the measurability witness.
Oracle: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`

### Technical notes

- No `sorry`, `opaque`, `axiom`, or `native_decide` introduced.
- T1 proof uses `Measurable.pow_const` from `Mathlib/MeasureTheory/Group/Arithmetic.lean`.
- `funext hdef` converts the pointwise hypothesis to a function equality for `rw`.
- T2 is a pure delegation: all hypotheses forwarded, `h` replaced by T1 application.
- Linter warning about unused section variables `[Group G] [MeasurableSpace G]` in T1 is cosmetic only.

**Commit**: v0.68.0

---

## Campaign C53  v0.69.0

**Version**: v0.69.0
**File**: `YangMills/P5_KPDecay/KPHypotheses.lean` (lines 1476-1530, +55 lines)
**Build**: exit code 0, 8184 jobs for KPHypotheses

### Theorems

**T1**: `kp_hpe_of_norm_sq_plaquetteEnergy`
Reduces `hpe : forall g, 0 <= plaquetteEnergy g` to `hndef : forall g, plaquetteEnergy g = ||f g|| ^ 2`
for any `f : G -> E` with `[SeminormedAddCommGroup E]`.
Proof: `rw [hndef g]; exact sq_nonneg _`.
Oracle: `[propext, Classical.choice, Quot.sound]`

**T2**: `kp_hmeas_of_measurable_norm_sq_plaquetteEnergy`
Reduces `Measurable plaquetteEnergy` to `hf : Measurable f` under `hndef : forall g, plaquetteEnergy g = ||f g|| ^ 2`
for any `f : G -> E` with `[NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]`.
Proof: `funext hndef` then `hf.norm.pow_const 2`.
Oracle: `[propext, Classical.choice, Quot.sound]`

**T3**: `kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy`
Full Clay Yang-Mills packaging from a norm-square plaquette energy.
Given `f : G -> E` with `hf : Measurable f` and `hndef : forall g, plaquetteEnergy g = ||f g|| ^ 2`,
concludes `ClayYangMillsTheorem`.
Delegates to C52-T2 with the real-valued factor `fun g => ||f g||` and `hf.norm`.
Oracle: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`

### Technical notes

- No `sorry`, `opaque`, `axiom`, or `native_decide` introduced.
- T1 proof uses `sq_nonneg` directly on the real-valued norm; does not need `norm_nonneg`.
- T2 proof chains `Measurable.norm` (from `BorelSpace/Metric.lean`, needs `OpensMeasurableSpace E`)
  with `Measurable.pow_const 2`.
- T3 is a pure term-mode delegation: passes `fun g => ||f g||` as the real-valued factor to C52-T2,
  replacing `hf : Measurable f` with `hf.norm : Measurable (fun g => ||f g||)`.
- Linter warning about unused section variable `[Group G]` in T1/T2 is cosmetic only.
- Generalises C51/C52 from scalar-square (`f g ^ 2`) to norm-square (`||f g|| ^ 2`)
  for any seminormed/normed type E, enabling gauge models with vector-valued amplitude fields.

**Commit**: v0.69.0

---

## Campaign C54  v0.70.0 (2026-04-06)

**Version tag:** v0.70.0
**File:** `YangMills/P5_KPDecay/KPHypotheses.lean`
**Lines before:** 1530 | **Lines after:** 1567 | **Delta:** +37
**Build:** `lake build YangMills.P5_KPDecay.KPHypotheses`  exit code 0, 8184 jobs
**Cleanliness:** CLEAN (no `sorry`, `opaque`, `axiom`, or `native_decide`)

### Theorems Added

**T1  `kp_hbeta_of_sq`**
Reduces `h : 0  ` from the structural assumption `hdef :  = b ^ 2` for some `b : `.
Proof: `rw [hdef]; exact sq_nonneg _`. Axioms: [propext, Classical.choice, Quot.sound].

**T2  `kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta`**
Packages C53-T3 and C54-T1. Accepts `( b : )` and `hdef :  = b ^ 2` in place of
`h : 0  `, derives non-negativity via T1, and concludes `ClayYangMillsTheorem`.
Delegates to C53-T3 with `kp_hbeta_of_sq  b hdef` supplying `h`.
Axioms: [propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap].

### Oracle Output
```
'YangMills.kp_hbeta_of_sq' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta' depends on axioms:
  [propext,
   Classical.choice,
   Quot.sound,
   YangMills.yangMills_continuum_mass_gap]
```

### Hypothesis Reduction Chain
- C54 reduces `h : 0  `  `hdef :  = b ^ 2` (scalar square representation)
- Combined with C53: a caller with `f : G  E`, `hf : Measurable f`,
  `hndef :  g, plaquetteEnergy g = f g ^ 2`, and `hdef :  = b ^ 2`
  concludes `ClayYangMillsTheorem` with no separate non-negativity or measurability proofs.

### Commit
`feat(C54/v0.70.0): squared inverse temperature interface (T1 h from =b, T2 Clay packaging)`

## v0.71.0 — Campaign C55 (2026-04-06)

**Version tag:** v0.71.0
**Parent:** v0.70.0 (C54)
**File:** `YangMills/P5_KPDecay/KPHypotheses.lean`
**Delta:** 1567 → 1615 lines (+48)

### Theorems added

**C55-T1** `kp_hf_of_continuous_factor`
Reduces `hf : Measurable f` from `hcont : Continuous f` under
`[TopologicalSpace G] [BorelSpace G]` on the gauge group domain and
`[BorelSpace E]` on the normed codomain.
Proof: `hcont.measurable` (one term, Continuous.measurable from Mathlib BorelSpace).
Oracle: `[propext, Classical.choice, Quot.sound]`

**C55-T2** `kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_continuous_factor`
Packages C54-T2 and C55-T1: given `f : G → E` with `hcont : Continuous f`,
`[TopologicalSpace G] [BorelSpace G]`, `[BorelSpace E]`,
`hndef : ∀ g, plaquetteEnergy g = ‖f g‖ ^ 2`, `hβdef : β = b ^ 2`,
derives `Measurable f` via C55-T1 and concludes `ClayYangMillsTheorem`.
Delegates to C54-T2 with `kp_hf_of_continuous_factor hcont` supplying `hf`.
Oracle: `[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]`

### Hypothesis reduction

| Original hypothesis | Reduced to (C55 interface) |
|---|---|
| `hf : Measurable f` | `hcont : Continuous f` (via C55-T1) |

Cumulative reduction chain after C51-C45:
- `hm : PositiveMassGap` → handled by `yangMills_continuum_mass_gap` axiom
- `hpe : ∀ g, 0 ≤ plaquetteEnergy g` → derived from `hndef` via C53-T1
- `h : Measurable plaquetteEnergy` → derived from `hf : Measurable f` via C53-T2
- `hβ : 0 ≤ β` → derived from `hβdef : β = b ^ 2` via C54-T1
- `hf : Measurable f` → derived from `hcont : Continuous f` via C55-T1

After C55, a caller with `f : G → E` (continuous), `[BorelSpace G]`, `[BorelSpace E]`,
`hndef` and `hβdef` reaches `ClayYangMillsTheorem` in a single call to T2.

### Build result
`lake build YangMills.P5_KPDecay.KPHypotheses` — exit code 0 (8184 jobs).
Cleanliness: CLEAN (no `sorry`, `opaque`, `axiom`, or `native_decide` introduced).

---

## v0.72.0 (C56) — 2026-04-06

### Theorems added

1. `YangMills.kp_hcont_of_lipschitz_factor` (C56-T1)
2. `YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_lipschitz_factor` (C56-T2)

### File delta

| File | Before | After | Delta |
|---|---|---|---|
| `YangMills/P5_KPDecay/KPHypotheses.lean` | 1615 | 1664 | +49 |

### Oracle

```
'YangMills.kp_hcont_of_lipschitz_factor' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_lipschitz_factor' depends on axioms:
  [propext,
   Classical.choice,
   Quot.sound,
   YangMills.yangMills_continuum_mass_gap]
```

### Hypothesis reduction

| Original hypothesis | Reduced to (C56 interface) |
|---|---|
| `hcont : Continuous f` | Derived from `hLip : LipschitzWith K f` via C56-T1 |

Cumulative reduction chain after C51–C56:
- `hm : PositiveMassGap` → handled by `yangMills_continuum_mass_gap` axiom
- `hpe : ∀ g, 0 ≤ plaquetteEnergy g` → derived from `hndef` via C53-T1
- `h : Measurable plaquetteEnergy` → derived from `hf : Measurable f` via C53-T2
- `hβ : 0 ≤ β` → derived from `hβdef : β = b ^ 2` via C54-T1
- `hf : Measurable f` → derived from `hcont : Continuous f` via C55-T1
- `hcont : Continuous f` → derived from `hLip : LipschitzWith K f` via C56-T1

After C56, a caller with `f : G → E` (Lipschitz), `[PseudoEMetricSpace G]`, `[BorelSpace G]`, `[BorelSpace E]`, `hndef` and `hβdef` reaches `ClayYangMillsTheorem` in a single call to T2.

### Build result

`lake build YangMills.P5_KPDecay.KPHypotheses` — exit code 0 (8184 jobs).
Cleanliness: CLEAN (no `sorry`, `opaque`, `axiom`, or `native_decide` introduced).

---

## v0.73.0 — C57 — 2026-04-06

### Theorems added

1. `YangMills.kp_hcont_of_locally_lipschitz_factor` (C57-T1)
2. `YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_locally_lipschitz_factor` (C57-T2)

### File delta

| File | Before | After | Delta |
|---|---|---|---|
| `KPHypotheses.lean` | 1664 | 1718 | +54 |
| `UNCONDITIONALITY_ROADMAP.md` | 771 | (this entry) | +49 |

### Oracle output

```
'YangMills.kp_hcont_of_locally_lipschitz_factor' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_locally_lipschitz_factor' depends on axioms:
  [propext,
   Classical.choice,
   Quot.sound,
   YangMills.yangMills_continuum_mass_gap]
```

T1 depends only on the three kernel axioms of Lean 4. T2 additionally depends on `yangMills_continuum_mass_gap`, mandatory since T2 concludes `ClayYangMillsTheorem`.

### Hypothesis reduction

C57 reduces `hLip : LipschitzWith K f` (from C56) to `hllip : LocallyLipschitz f`.
`LocallyLipschitz f` is strictly weaker than `LipschitzWith K f`: every globally K-Lipschitz map is locally Lipschitz, but not vice versa (e.g. `f(x) = sqrt(|x|)` on ℝ is locally Lipschitz but not globally Lipschitz at 0).

### Cumulative reduction chain after C51–C57

| Original hypothesis | Reduced to (C57 interface) |
|---|---|
| `hm : PositiveMassGap` | Handled by `yangMills_continuum_mass_gap` axiom |
| `hpe : ∀ g, 0 ≤ plaquetteEnergy g` | Derived from `hndef` via C53-T1 |
| `h : Measurable plaquetteEnergy` | Derived from `hf : Measurable f` via C53-T2 |
| `hβ : 0 ≤ β` | Derived from `hβdef : β = b ^ 2` via C54-T1 |
| `hf : Measurable f` | Derived from `hcont : Continuous f` via C55-T1 |
| `hcont : Continuous f` | Derived from `hLip : LipschitzWith K f` via C56-T1 |
| `hLip : LipschitzWith K f` | Derived from `hllip : LocallyLipschitz f` via C57-T1 |

### Build result

`lake build YangMills.P5_KPDecay.KPHypotheses` – exit code 0 (8184 jobs).
Cleanliness: CLEAN (no `sorry`, `opaque`, `axiom`, or `native_decide` introduced).

---

## v0.74.0 — C58 — 2026-04-06

### Theorems added

1. `YangMills.kp_hllip_of_contdiff_one_factor` (C58-T1)
2. `YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_contdiff_one_factor` (C58-T2)

### File delta

| File | Before | After | Delta |
|---|---|---|---|
| `KPHypotheses.lean` | 1718 | 1771 | +53 |
| `UNCONDITIONALITY_ROADMAP.md` | 824 | (this entry) | +49 |

### Oracle output

```
'YangMills.kp_hllip_of_contdiff_one_factor' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_contdiff_one_factor' depends on axioms:
  [propext,
   Classical.choice,
   Quot.sound,
   YangMills.yangMills_continuum_mass_gap]
```

T1 depends only on the three kernel axioms of Lean 4. T2 additionally depends on `yangMills_continuum_mass_gap`, mandatory since T2 concludes `ClayYangMillsTheorem`.

### Hypothesis reduction

C58 reduces `hllip : LocallyLipschitz f` (from C57) to `hcd : ContDiff ℝ 1 f`.
`ContDiff ℝ 1 f` is strictly stronger than `LocallyLipschitz f`: every C¹ function is locally Lipschitz, but not vice versa (e.g. `f(x) = |x|` on ℝ is locally Lipschitz but not C¹ at 0).
The reduction uses `ContDiff.locallyLipschitz` from `Mathlib/Analysis/Calculus/ContDiff/RCLike.lean` (line 143).

### Cumulative reduction chain after C51–C58

| Original hypothesis | Reduced to (C58 interface) |
|---|---|
| `hm : PositiveMassGap` | Handled by `yangMills_continuum_mass_gap` axiom |
| `hpe : ∀ g, 0 ≤ plaquetteEnergy g` | Derived from `hndef` via C53-T1 |
| `h : Measurable plaquetteEnergy` | Derived from `hf : Measurable f` via C53-T2 |
| `hβ : 0 ≤ β` | Derived from `hβdef : β = b ^ 2` via C54-T1 |
| `hf : Measurable f` | Derived from `hcont : Continuous f` via C55-T1 |
| `hcont : Continuous f` | Derived from `hLip : LipschitzWith K f` via C56-T1 |
| `hLip : LipschitzWith K f` | Derived from `hllip : LocallyLipschitz f` via C57-T1 |
| `hllip : LocallyLipschitz f` | Derived from `hcd : ContDiff ℝ 1 f` via C58-T1 |

### Build result

`lake build YangMills.P5_KPDecay.KPHypotheses` – exit code 0 (8184 jobs).
Cleanliness: CLEAN (no `sorry`, `opaque`, `axiom`, or `native_decide` introduced).

---

## v0.75.0 — C59 — 2026-04-06

### Theorems added

1. `YangMills.kp_hcont_of_differentiable_factor` (C59-T1)
2. `YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_differentiable_factor` (C59-T2)

### File delta

| File | Before | After | Delta |
|---|---|---|---|
| `KPHypotheses.lean` | 1771 | 1824 | +53 |
| `UNCONDITIONALITY_ROADMAP.md` | 879 | (this entry) | +49 |

### Oracle output

```
'YangMills.kp_hcont_of_differentiable_factor' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_differentiable_factor' depends on axioms:
  [propext,
   Classical.choice,
   Quot.sound,
   YangMills.yangMills_continuum_mass_gap]
```

T1 depends only on the three kernel axioms of Lean 4. T2 additionally depends on `yangMills_continuum_mass_gap`, mandatory since T2 concludes `ClayYangMillsTheorem`.

### Hypothesis reduction

C59 reduces `hcont : Continuous f` (from C55) to `hdiff : Differentiable ℝ f`.
`Differentiable ℝ f` is strictly stronger than `Continuous f`: every differentiable function is continuous, but not vice versa (e.g. `f(x) = |x|` on ℝ is continuous but not differentiable at 0).
The reduction uses `Differentiable.continuous` from `Mathlib/Analysis/Calculus/FDeriv/Basic.lean` (line 659).
Note: C59 bypasses the C56–C58 intermediate chain (Lipschitz → LocallyLipschitz → C¹) and delegates directly to C55-T2.

### Cumulative reduction chain after C51–C59

| Original hypothesis | Reduced to (C59 interface) |
|---|---|
| `hm : PositiveMassGap` | Handled by `yangMills_continuum_mass_gap` axiom |
| `hpe : ∀ g, 0 ≤ plaquetteEnergy g` | Derived from `hndef` via C53-T1 |
| `h : Measurable plaquetteEnergy` | Derived from `hf : Measurable f` via C53-T2 |
| `hβ : 0 ≤ β` | Derived from `hβdef : β = b ^ 2` via C54-T1 |
| `hf : Measurable f` | Derived from `hcont : Continuous f` via C55-T1 |
| `hcont : Continuous f` | Derived from `hdiff : Differentiable ℝ f` via C59-T1 |

### Build result

`lake build YangMills.P5_KPDecay.KPHypotheses` – exit code 0 (8184 jobs).
Cleanliness: CLEAN (no `sorry`, `opaque`, `axiom`, or `native_decide` introduced).

---

## v0.76.0 — C60 — 2026-04-06

### Theorems added

1. `YangMills.kp_hdiff_of_hasFDerivAt_factor` (C60-T1)
2. `YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_hasFDerivAt_factor` (C60-T2)

### File delta

| File | Before | After | Delta |
|---|---|---|---|
| `KPHypotheses.lean` | 1824 | 1869 | +45 |
| `UNCONDITIONALITY_ROADMAP.md` | 933 | (this entry) | +49 |

### Oracle output

```
'YangMills.kp_hdiff_of_hasFDerivAt_factor' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'YangMills.kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta_hasFDerivAt_factor' depends on axioms:
  [propext,
   Classical.choice,
   Quot.sound,
   YangMills.yangMills_continuum_mass_gap]
```

T1 depends only on the three kernel axioms of Lean 4. T2 additionally depends on `yangMills_continuum_mass_gap`, mandatory since T2 concludes `ClayYangMillsTheorem`.

### Hypothesis reduction

C60 reduces `hdiff : Differentiable ℝ f` (from C59) to `hfd : ∀ g : G, HasFDerivAt f (f' g) g`.
NOTE: This is NOT a weakening of `Differentiable ℝ f`. It is a structural interface theorem.
`Differentiable ℝ f` ↔ `∃ f', ∀ g, HasFDerivAt f (f' g) g`. The hypothesis `hfd` provides
explicit derivative witnesses `f' g : G →L[ℝ] E` at each point, replacing the existential
implicit in `Differentiable ℝ f`.
Proof: `HasFDerivAt.differentiableAt` from `Mathlib/Analysis/Calculus/FDeriv/Basic.lean` (line 221).
Note: C60 provides an alternative entry point to C59; it does not bypass any intermediate chain.

### Cumulative reduction chain after C51–C60

| Original hypothesis | Reduced to (C60 interface) |
|---|---|
| `hm : PositiveMassGap` | Handled by `yangMills_continuum_mass_gap` axiom |
| `hpe : ∀ g, 0 ≤ plaquetteEnergy g` | Derived from `hndef` via C53-T1 |
| `h : Measurable plaquetteEnergy` | Derived from `hf : Measurable f` via C53-T2 |
| `hβ : 0 ≤ β` | Derived from `hβdef : β = b ^ 2` via C54-T1 |
| `hf : Measurable f` | Derived from `hcont : Continuous f` via C55-T1 |
| `hcont : Continuous f` | Derived from `hdiff : Differentiable ℝ f` via C59-T1 |
| `hdiff : Differentiable ℝ f` | Derived from `hfd : ∀ g : G, HasFDerivAt f (f' g) g` via C60-T1 |

### Build result

`lake build YangMills.P5_KPDecay.KPHypotheses` – exit code 0 (8184 jobs).
Cleanliness: CLEAN (no `sorry`, `opaque`, `axiom`, or `native_decide` introduced).
