# UNCONDITIONALITY_ROADMAP.md
## THE-ERIKSSON-PROGRAMME — Yang–Mills Lean Formalization
## Version: v0.3.0  (Campaign 15)

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
  - Geometric series bound: `∑ k, exp (-κ * L^k) < ∞` (Mathlib `tsum_geometric_of_lt_one`)

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
- Formalize the geometric UV-suppression sum (Step 5, largely elementary)
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

## What did NOT improve in v0.28.x (Campaign 15)

The number of custom live axioms remained exactly **1**.

Campaign 15 (this campaign) verified:
- No other proof of HasContinuumMassGap exists in the repo.
- No P8_PhysicalGap theorem directly concludes HasContinuumMassGap unconditionally.
- The obstruction is genuine and precisely documented above.
- No new axiom, opaque, constant, or sorry was introduced.
- All "Bloque4" references replaced with proper [58]–[68] citations.

---

## Version history

| Version | Campaign | Change |
|---------|----------|--------|
| v0.1.0  | Campaign 12 | Initial roadmap |
| v0.2.0  | Campaign 14 | Phase 3 obstruction analysis added |
| v0.3.0  | Campaign 15 | Phase 3 deepened; OS axiom table; Route C added; Bloque4 → [58]–[68] |

---

*Last updated: Campaign 15. Source papers: [58]–[68] as listed above.*
