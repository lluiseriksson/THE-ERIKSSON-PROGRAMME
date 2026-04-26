# BLUEPRINT_MultiscaleDecoupling.md

**Author**: Cowork agent (Claude), Phase 84
**Date**: 2026-04-25 (very late session)
**Status**: strategic blueprint
**Companion blueprints**: `BLUEPRINT_BalabanRG.md`,
`BLUEPRINT_F3Count.md`, `BLUEPRINT_F3Mayer.md`,
`BLUEPRINT_ContinuumLimit.md`, `BLUEPRINT_ReflectionPositivity.md`
**Source paper**: Eriksson "Exponential Clustering and Mass Gap for
Four-Dimensional SU(N) Lattice Yang–Mills Theory", §6 (the new
contribution of Bloque-4).

---

## 0. Why this blueprint exists

Eriksson's Bloque-4 paper assembles three pillars to prove the
lattice mass gap:

1. **Balaban's RG framework** (CMP 1984–1989) → captured by Codex's
   massive `YangMills/ClayCore/BalabanRG/` push (~222 files).
2. **Terminal cluster expansion / KP** (Eriksson Paper [1]) → captured
   by Codex's F3 chain (`F3Count`, `F3Mayer`, `ConnectingClusterCountExp`,
   `ClusterRpowBridge`, etc.).
3. **Multiscale correlator decoupling** (Bloque-4 §6, the new
   contribution) → **NOT yet explicitly captured in the project**.

This blueprint is for the third pillar. It is the **clearest
immediate contribution opportunity** for Cowork (per Finding 017).

---

## 1. The mathematical content of Bloque-4 §6

### 1.1 Proposition 6.1 (Multiscale Telescoping Identity)

For bounded gauge-invariant observables `F, G`:

```
Cov_{µ_η}(F, G)
  = Cov_{µ_{a_*}}(F̃, G̃)
  + Σ_{k=0}^{k*-1} R_k(F, G),
```

where:
* `F̃ = E_{µ_η}[F | σ_{a_*}]` and `G̃ = E_{µ_η}[G | σ_{a_*}]` are the
  conditional expectations onto the terminal-scale σ-algebra.
* `R_k(F, G) = E_{µ_{a_{k+1}}}[Cov_{µ_{a_k} | σ_{a_{k+1}}}(F_k, G_k)]`
  is the **conditional covariance term** at scale `a_k`.

**Proof tool**: iterative application of the Law of Total Covariance
along the σ-algebra chain `σ_{a_0} ⊃ σ_{a_1} ⊃ ⋯ ⊃ σ_{a_*}`.

### 1.2 Lemma 6.2 (Single-Scale UV Error Bound)

For supports separated by distance `R`:

```
|R_k(F, G)| ≤ C ‖F‖_∞ ‖G‖_∞ exp(-κ R / a_k).
```

**Proof tool**: cluster expansion at scale `a_k` plus random-walk
decay of the propagator `G_k = ∆_k^{-1}` (via Balaban's propagator
estimates [4, 5]).

### 1.3 Theorem 6.3 (UV Suppression via Geometric Sum)

For `R ≥ a_*`:

```
| Σ_{k=0}^{k*-1} R_k(F, G) | ≤ C' ‖F‖_∞ ‖G‖_∞ exp(-c_0 R / a_*).
```

**Proof tool**: each scale contributes `exp(-κ L^j R / a_*)`, and the
geometric series converges.

### 1.4 Theorem 7.1 (Mass Gap Bound) — the assembly

Combining the IR clustering (Theorem 5.5) and UV suppression
(Theorem 6.3):

```
| Cov_{µ_η}(O(0), O(x)) | ≤ C exp(-m |x| / a_*),

where m = min(m_*, c_0) > 0.
```

This is the **lattice mass gap statement**, uniform in `η` and
`L_phys`.

---

## 2. What's already available in Mathlib / project

| Component | Status | Where |
|-----------|--------|-------|
| Conditional expectation `condExp m μ` | ✓ Mathlib | `Mathlib.MeasureTheory.Function.ConditionalExpectation` |
| Covariance `cov[X, Y; μ]` | ✓ Mathlib | `Mathlib.Probability.Moments.Covariance` |
| Tower property (`integral_condExp`) | ✓ Mathlib | same |
| Law of Total Covariance | ❌ Mathlib gap | **PR draft in this project**: `YangMills/MathlibUpstream/LawOfTotalCovariance.lean` (Phase 82) |
| Random-walk decay of propagator at scale `a_k` | ❌ Mathlib gap | covered by Balaban [4, 5] in the analytic argument |
| Geometric series `Σ exp(-κ L^j R)` | ✓ Mathlib | standard `tsum`/`Geometric.sum` |
| Cluster expansion at scale `a_k` | ❌ Mathlib gap | covered by Codex's F3 / Mayer chain |

**The single Mathlib upstream contribution needed**: Law of Total
Covariance (Phase 82 in this project).

**The single project-internal contribution needed**: a
`MultiscaleTelescopingPackage` structure that bundles the σ-algebra
chain, the LTC application, and the single-scale error bounds.

---

## 3. Proposed project structure

### 3.1 New file: `YangMills/L7_Multiscale/MultiscaleDecoupling.lean`

```
YangMills/
  L7_Multiscale/                        ← NEW directory (level 7, between
                                           the L6 OS layer and the L8
                                           terminal endpoints)
    MultiscaleDecoupling.lean           ← THIS FILE
    MultiscaleSigmaAlgebraChain.lean    ← σ-algebra chain abstraction
    SingleScaleUVError.lean             ← Lemma 6.2 abstract form
    GeometricUVSummation.lean           ← Theorem 6.3 abstract form
    MassGapAssembly.lean                ← Theorem 7.1 endpoint
```

### 3.2 Key Lean structures

```lean
/-- A descending chain of σ-algebras representing block-spin
    coarsenings at scales a₀ > a₁ > ⋯ > a_*. -/
structure MultiscaleSigmaAlgebraChain
    {Ω : Type*} [MeasurableSpace Ω] (k_star : ℕ) where
  σ : Fin (k_star + 1) → MeasurableSpace Ω
  σ_descending : ∀ k : Fin k_star, σ k.succ ≤ σ k.castSucc
  σ_below_top : ∀ k, σ k ≤ ‹MeasurableSpace Ω›

/-- Single-scale UV error: the conditional covariance at scale k
    decays exponentially in R/a_k. -/
def SingleScaleUVErrorBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (chain : MultiscaleSigmaAlgebraChain k_star)
    (a : Fin (k_star + 1) → ℝ) (κ : ℝ) (C : ℝ) : Prop :=
  ∀ (k : Fin k_star) (F G : Ω → ℝ) (R : ℝ),
    |∫ ω, condExp (chain.σ k.succ) μ
      (condExp (chain.σ k.castSucc) μ (F * G) -
       (condExp (chain.σ k.castSucc) μ F) *
       (condExp (chain.σ k.castSucc) μ G)) ω ∂μ|
    ≤ C * ‖F‖∞ * ‖G‖∞ * Real.exp (-κ * R / a k.castSucc)

/-- The full multiscale telescoping package. -/
structure MultiscaleDecouplingPackage
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  k_star : ℕ
  chain : MultiscaleSigmaAlgebraChain k_star
  a : Fin (k_star + 1) → ℝ
  ha_descending : ∀ k : Fin k_star, a k.succ < a k.castSucc
  L : ℝ
  hL_gt_one : 1 < L
  ha_geometric : ∀ k : Fin k_star, a k.succ = a k.castSucc / L
  κ : ℝ
  hκ_pos : 0 < κ
  C : ℝ
  hC_pos : 0 < C
  uv_error : SingleScaleUVErrorBound μ chain a κ C
```

### 3.3 The endpoint theorem

```lean
/-- Bloque-4 Theorem 7.1: combining the multiscale UV suppression
    with terminal-scale exponential clustering yields the lattice
    mass gap. -/
theorem lattice_mass_gap_of_multiscale_decoupling_and_terminal_clustering
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (mdpkg : MultiscaleDecouplingPackage μ)
    (terminal_cluster : OSClusterProperty
      (...)  -- terminal-scale clustering, supplied by Branch I
      (...)  -- observable type
      (...)  -- evaluation
      (...)  -- distance) :
    ∃ m > 0, ∃ C : ℝ, 0 < C ∧
      ∀ (F G : Ω → ℝ) (R : ℝ), R ≥ ... →
        |cov[F, G; μ]| ≤ C * ‖F‖∞ * ‖G‖∞ * Real.exp (-m * R / mdpkg.a 0) := by
  sorry  -- combines telescoping identity + Theorem 6.3 + terminal cluster
```

---

## 4. Strategic placement

The multiscale-decoupling layer fits into the project as:

```
Branch I (Codex, F3 / cluster expansion, terminal scale)
      ↓
Terminal exp clustering (OSClusterProperty at µ_a*)
      ↓
[L7_Multiscale/MultiscaleDecoupling.lean] ←── NEW LAYER
      ↓
Lattice mass gap (Theorem 7.1, on µ_η)
      ↓
Branch III (Cowork, RP + transfer matrix, OS reconstruction)
      ↓
Wightman QFT (Bloque-4 §8.4, conditional on OS1)
```

The L7_Multiscale layer is **independent of Branch II** (Bałaban RG)
in the sense that it does not require the BalabanRG/ infrastructure;
it only requires the terminal-scale clustering output, which can come
from any source (Branch I via F3, or Branch II via Bałaban
+ ClayCoreLSIToSUNDLRTransfer, or even a future direct argument).

---

## 5. Estimated effort

| Component | Effort | Dependencies |
|-----------|--------|--------------|
| `MultiscaleSigmaAlgebraChain` | ~30 LOC | Mathlib `MeasurableSpace` |
| `SingleScaleUVErrorBound` | ~50 LOC | Phase 82 (LTC), Mathlib `condExp` |
| `MultiscaleDecouplingPackage` | ~60 LOC | above + geometric series |
| `lattice_mass_gap_of_multiscale_decoupling_and_terminal_clustering` | ~150 LOC | full LTC chain + telescoping identity |
| **Total** | **~290 LOC** | Phase 82 + standard Mathlib |

Comparable in scope to Cowork's Phase 17 dimensional-transmutation
witness, well within Cowork's reach in a future session.

---

## 6. What this blueprint does NOT do

* Does NOT prove Lemma 6.2's single-scale error bound from physical
  inputs. That requires Balaban's propagator estimates [4, 5] which
  are outside the multiscale-decoupling layer proper.
* Does NOT prove the terminal clustering. That's Branch I (Codex's
  F3 chain) or Branch II (Codex's BalabanRG/ via
  `ClayCoreLSIToSUNDLRTransfer`).
* Does NOT prove OS1 (full O(4) covariance). That's the **single
  uncrossed barrier** to Wightman QFT, even within Eriksson's
  Bloque-4 paper itself.

The multiscale-decoupling layer is a **structural composer** — it
takes terminal clustering as input and produces the lattice mass
gap as output, via the LTC + telescoping + geometric summation
machinery.

---

## 7. Open questions / future work

1. **Does the σ-algebra chain need to be measurable in a strong
   sense?** Bloque-4 §6 uses `σ_{a_k}` as the σ-algebra generated by
   block-spin variables. Formally, this requires defining the
   block-spin map and showing measurability. Codex's `BalabanRG/`
   has some of this infrastructure.

2. **Is the random-walk propagator decay (Balaban [4, 5]) needed in
   Lean, or can it be black-boxed?** For Cowork's contribution, the
   decay should be supplied as a hypothesis. For full closure, it
   needs Lean-side proof.

3. **How does this interact with Branch II (`BalabanRGPackage`)?**
   The terminal scale `a_*` corresponds to Bałaban's terminal RG
   step; the conditional covariance R_k(F,G) is conditioned on the
   block-spin σ-algebra at the next coarser scale. Both can be
   formalised through the same chain abstraction.

4. **Should `MultiscaleDecouplingPackage` live inside `BalabanRG/`
   or as a sibling layer `L7_Multiscale/`?** I lean toward sibling,
   since the multiscale layer is conceptually orthogonal to
   Bałaban's RG (Bałaban produces the polymer activities at each
   scale; multiscale telescoping uses the resulting σ-algebra
   chain).

---

## 8. Relation to the other blueprints

| Blueprint | Pillar | Status |
|-----------|--------|--------|
| `BLUEPRINT_BalabanRG.md` | Branch II (Bałaban RG) | scaffold-complete (Codex BalabanRG/) |
| `BLUEPRINT_F3Count.md` | Branch I sub-pillar (combinatorial counts) | active (Codex Priority 1.2) |
| `BLUEPRINT_F3Mayer.md` | Branch I sub-pillar (cluster activities) | active (Codex Priority 2.x) |
| `BLUEPRINT_ContinuumLimit.md` | Branch VII (continuum) | analytical-closure achieved (Phase 17) |
| `BLUEPRINT_ReflectionPositivity.md` | Branch III (RP) | scaffold-complete + SU(1) closed (Phase 22 + Phase 46-50) |
| **`BLUEPRINT_MultiscaleDecoupling.md` (THIS)** | **multiscale telescoping** | **blueprint, no Lean yet** |

The project now has 6 active blueprints. The multiscale-decoupling
blueprint is the **most under-developed** but also the **closest to
Cowork's natural skill set** (probability-theoretic, combines existing
Mathlib infrastructure rather than requiring new gauge theory).

---

## 9. Action plan (recommended for next Cowork session)

1. **Stage A** (1 phase): finalise the LTC PR draft (Phase 82) for
   submission to Mathlib upstream.
2. **Stage B** (2-3 phases): implement
   `YangMills/L7_Multiscale/MultiscaleSigmaAlgebraChain.lean` and
   `SingleScaleUVErrorBound.lean`.
3. **Stage C** (1 phase): assemble the
   `MultiscaleDecouplingPackage` structure + the endpoint theorem
   `lattice_mass_gap_of_multiscale_decoupling_and_terminal_clustering`.
4. **Stage D** (1 phase): wire it into the project's existing
   terminal endpoints (`physicalStrong_of_*`).

Total estimate: **5-7 phases**, comparable to a single-day Cowork
session.

---

*Blueprint complete 2026-04-25 evening (Phase 84) by Cowork agent.
Cross-references: `ERIKSSON_BLOQUE4_INVESTIGATION.md` (Phase 81),
`COWORK_FINDINGS.md` Finding 017,
`YangMills/MathlibUpstream/LawOfTotalCovariance.lean` (Phase 82),
`YangMills/L6_OS/ClusteringImpliesSpectralGap.lean` (Phase 83).*
