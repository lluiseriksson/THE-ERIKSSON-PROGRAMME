/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.AbelianU1Unconditional
import YangMills.P8_PhysicalGap.LSIDefinitions

/-!
# SU(1) discharge of the LSI / Poincaré / clustering predicate set

This module provides **unconditional discharges** of the four
Branch III analytic predicates defined in
`P8_PhysicalGap/LSIDefinitions.lean`:

| Predicate                  | SU(1) reduction                          |
|----------------------------|------------------------------------------|
| `IsDirichletForm`          | trivial with `E := fun _ => 0`           |
| `PoincareInequality`       | LHS variance = 0 (Subsingleton)          |
| `LogSobolevInequality`     | LHS entropy = 0 (Subsingleton)           |
| `ExponentialClustering`    | LHS connected corr = 0 (Subsingleton)    |

## Why all four are trivial at SU(1)

Every real-valued function on `GaugeConfig d L SU(1)` is constant
(equal to `f default` — the Subsingleton structure). Under any
probability measure on the gauge-config space:

* `∫ f = f default`
* `∫ f² = (f default)²`
* `∫ f² · log(f²) = (f default)² · log((f default)²)`
* `∫ F · G = F default · G default`

Hence the **variance** `∫(f - ∫f)²` is `0`, the **entropy excess**
`∫f²log(f²) - (∫f²)log(∫f²)` is `0`, and the **connected correlator**
`∫FG - (∫F)(∫G)` is `0`. Every analytic inequality of the form
`(zero) ≤ (positive constant) · (something nonnegative)` is then
trivially satisfied with arbitrary positive parameters
`α, lam, C, ξ`.

## Implication for Branch III

The Branch III pipeline composes:

```
Dirichlet form + LSI + Poincaré → spectral gap → mass gap
```

This file shows that **every input** to that pipeline admits a
trivial unconditional inhabitant at SU(1). Combined with Phases
46–50 (OS-axiom quartet), this means the Branch III pipeline is
structurally non-vacuous at every layer.

## Caveat

Per `COWORK_FINDINGS.md` Findings 003 + 011, this is the trivial
group SU(1) = `{1}`, so the witnesses are physics-degenerate. For
`N_c ≥ 2`, the LSI/Poincaré/clustering inequalities become
substantive measure-theoretic / functional-analytic obligations
(BalabanToLSI / Bakry-Emery / Holley-Stroock infrastructure).

## Oracle target

`[propext, Classical.choice, Quot.sound]` per project discipline.

-/

namespace YangMills.P8

open MeasureTheory Real

variable {d L : ℕ} [NeZero d] [NeZero L]

abbrev SU1Config (d L : ℕ) [NeZero d] [NeZero L] : Type :=
  GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)

/-! ## §0. Subsingleton-integral helper for SU(1)

(Same shape as `integral_eq_default_su1` in
`L6_OS/AbelianU1ClusterProperty.lean`; restated here to keep this
module independent of the L6_OS branch.) -/

private lemma integral_eq_default_su1_p8
    {μ : Measure (SU1Config d L)} [IsProbabilityMeasure μ]
    (f : SU1Config d L → ℝ) :
    (∫ U, f U ∂μ) = f default := by
  have h : (fun U : SU1Config d L => f U) = (fun _ => f default) := by
    funext U; rw [Subsingleton.elim U default]
  rw [h]; simp

/-! ## §1. IsDirichletForm — trivial via the zero form -/

/-- The zero form `E := fun _ => 0` is a Dirichlet form on any measure
    space. This is the canonical "trivial" Dirichlet-form witness. -/
theorem isDirichletForm_zero
    (μ : Measure (SU1Config d L)) :
    IsDirichletForm (fun _ : (SU1Config d L → ℝ) => (0 : ℝ)) μ :=
  ⟨fun _ => le_refl 0, fun _ _ => by norm_num⟩

#print axioms isDirichletForm_zero

/-! ## §2. PoincareInequality — unconditional for SU(1) -/

/-- **PoincareInequality discharged unconditionally for SU(1)**, with
    arbitrary `λ > 0` and arbitrary nonneg form `E`. The variance
    `∫(f - ∫f)²` vanishes identically because `f` is constant on the
    Subsingleton, so the inequality reduces to `0 ≤ (1/λ) · E f`,
    which holds when `E f ≥ 0` and `λ > 0`. -/
theorem poincareInequality_su1
    (β : ℝ) (E : (SU1Config d L → ℝ) → ℝ)
    (h_E_nonneg : ∀ f, 0 ≤ E f)
    (lam : ℝ) (h_lam : 0 < lam) :
    PoincareInequality
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      E lam := by
  refine ⟨h_lam, ?_⟩
  intro f _hf
  -- LHS: ∫(f - ∫f)² = 0 because f is constant.
  have h_const_diff :
      (fun U : SU1Config d L =>
        (f U - ∫ y, f y ∂(gibbsMeasure (d := d) (N := L)
          (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) ^ 2)
        = (fun _ => 0) := by
    funext U
    have hfU : f U = f default := by rw [Subsingleton.elim U default]
    have hInt :
        (∫ y, f y ∂(gibbsMeasure (d := d) (N := L)
          (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) = f default :=
      integral_eq_default_su1_p8 f
    rw [hfU, hInt]; ring
  rw [h_const_diff]
  simp only [integral_zero]
  exact mul_nonneg (one_div_pos.mpr h_lam).le (h_E_nonneg f)

#print axioms poincareInequality_su1

/-! ## §3. LogSobolevInequality — unconditional for SU(1) -/

/-- **LogSobolevInequality discharged unconditionally for SU(1)**, with
    arbitrary `α > 0` and arbitrary nonneg form `E`. The entropy excess
    `∫ f²·log(f²) - (∫f²)·log(∫f²)` vanishes because `f² · log(f²)` is
    constant, so the inequality reduces to `0 ≤ (2/α) · E f`. -/
theorem logSobolevInequality_su1
    (β : ℝ) (E : (SU1Config d L → ℝ) → ℝ)
    (h_E_nonneg : ∀ f, 0 ≤ E f)
    (α : ℝ) (h_α : 0 < α) :
    LogSobolevInequality
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      E α := by
  refine ⟨h_α, ?_⟩
  intro f _hf
  -- Both ∫ f²·log(f²) and (∫f²)·log(∫f²) equal (f default)² · log((f default)²)
  have h_int_sq_log :
      (∫ U, f U ^ 2 * Real.log (f U ^ 2) ∂(gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β))
        = (f default) ^ 2 * Real.log ((f default) ^ 2) := by
    have h : (fun U : SU1Config d L => f U ^ 2 * Real.log (f U ^ 2)) =
             (fun _ => (f default) ^ 2 * Real.log ((f default) ^ 2)) := by
      funext U; rw [Subsingleton.elim U default]
    rw [h]; simp
  have h_int_sq :
      (∫ U, f U ^ 2 ∂(gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β))
        = (f default) ^ 2 := by
    have h : (fun U : SU1Config d L => f U ^ 2) =
             (fun _ => (f default) ^ 2) := by
      funext U; rw [Subsingleton.elim U default]
    rw [h]; simp
  rw [h_int_sq_log, h_int_sq]
  -- Goal: (f default)² · log((f default)²) - (f default)² · log((f default)²) ≤ (2/α) · E f
  have hZero : (f default) ^ 2 * Real.log ((f default) ^ 2) -
               (f default) ^ 2 * Real.log ((f default) ^ 2) = 0 := by ring
  rw [hZero]
  exact mul_nonneg (by positivity) (h_E_nonneg f)

#print axioms logSobolevInequality_su1

/-! ## §4. ExponentialClustering — unconditional for SU(1) -/

/-- **ExponentialClustering discharged unconditionally for SU(1)**, with
    arbitrary `C > 0` and `ξ > 0`. The connected correlator
    `∫FG - (∫F)(∫G)` vanishes (Subsingleton + probability measure),
    so the inequality reduces to `0 ≤ (positive)`. -/
theorem exponentialClustering_su1
    (β : ℝ) (C : ℝ) (h_C : 0 < C) (ξ : ℝ) (h_ξ : 0 < ξ) :
    ExponentialClustering
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      C ξ := by
  refine ⟨h_ξ, h_C, ?_⟩
  intro F G_obs
  -- LHS connected correlator = 0
  have h_FG :
      (∫ U, F U * G_obs U ∂(gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β))
        = F default * G_obs default := by
    have h : (fun U : SU1Config d L => F U * G_obs U) =
             (fun _ => F default * G_obs default) := by
      funext U; rw [Subsingleton.elim U default]
    rw [h]; simp
  have h_F : (∫ U, F U ∂(gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β))
        = F default := integral_eq_default_su1_p8 F
  have h_G : (∫ U, G_obs U ∂(gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β))
        = G_obs default := integral_eq_default_su1_p8 G_obs
  rw [h_FG, h_F, h_G]
  -- Goal: |F default * G_obs default - F default * G_obs default| ≤ ...
  simp only [sub_self, abs_zero]
  -- Goal: 0 ≤ C * sqrt(∫F²) * sqrt(∫G²) * exp(-1/ξ)
  have h_sq_F :
      Real.sqrt (∫ U, F U ^ 2 ∂(gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) =
      Real.sqrt ((F default) ^ 2) := by
    congr 1
    have h : (fun U : SU1Config d L => F U ^ 2) =
             (fun _ => (F default) ^ 2) := by
      funext U; rw [Subsingleton.elim U default]
    rw [h]; simp
  have h_sq_G :
      Real.sqrt (∫ U, G_obs U ^ 2 ∂(gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) =
      Real.sqrt ((G_obs default) ^ 2) := by
    congr 1
    have h : (fun U : SU1Config d L => G_obs U ^ 2) =
             (fun _ => (G_obs default) ^ 2) := by
      funext U; rw [Subsingleton.elim U default]
    rw [h]; simp
  rw [h_sq_F, h_sq_G]
  positivity

#print axioms exponentialClustering_su1

/-! ## §5. Bundle theorem — Branch III analytic predicates at SU(1) -/

/-- **Bundle: Branch III analytic-predicate completeness at SU(1)**.

    All four Branch III spectral-gap-pipeline predicates admit
    unconditional inhabitants for the SU(1) Wilson Gibbs measure,
    discharged simultaneously via Subsingleton-collapse. -/
theorem branchIII_LSI_bundle_su1
    (β : ℝ) (lam α C ξ : ℝ)
    (h_lam : 0 < lam) (h_α : 0 < α) (h_C : 0 < C) (h_ξ : 0 < ξ) :
    let μ := gibbsMeasure (d := d) (N := L)
              (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β
    let E0 : (SU1Config d L → ℝ) → ℝ := fun _ => 0
    IsDirichletForm E0 μ ∧
    PoincareInequality μ E0 lam ∧
    LogSobolevInequality μ E0 α ∧
    ExponentialClustering μ C ξ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isDirichletForm_zero _
  · exact poincareInequality_su1 (d := d) (L := L) β _ (fun _ => le_refl 0) lam h_lam
  · exact logSobolevInequality_su1 (d := d) (L := L) β _ (fun _ => le_refl 0) α h_α
  · exact exponentialClustering_su1 (d := d) (L := L) β C h_C ξ h_ξ

#print axioms branchIII_LSI_bundle_su1

/-! ## §6. Coordination note -/

/-
Status of the SU(1) **Branch III analytic-predicate frontier**
after Phase 53:

```
Predicate              SU(1) inhabitant?    Witness file
-------------------------------------------------------------
IsDirichletForm        ✓ (trivial form)     AbelianU1LSIDischarge (here)
PoincareInequality     ✓                    AbelianU1LSIDischarge (here)
LogSobolevInequality   ✓                    AbelianU1LSIDischarge (here)
ExponentialClustering  ✓                    AbelianU1LSIDischarge (here)
```

Combined with Phases 46–50 (OS axioms) and Phases 43–45 (Clay
hierarchy), this brings the SU(1) **structural-completeness** total
to the following inhabited predicate set:

* **OS axioms (4)**: OSCovariant, OSReflectionPositive,
  OSClusterProperty, HasInfiniteVolumeLimit.
* **LSI / spectral-gap inputs (4)**: IsDirichletForm,
  PoincareInequality, LogSobolevInequality, ExponentialClustering.
* **Clay-grade predicates (4+)**: ClayYangMillsTheorem,
  ClayYangMillsMassGap, ClayYangMillsPhysicalStrong,
  ClayYangMillsPhysicalStrong_Genuine.
* **Auxiliary structural witnesses (4+)**: ClusterCorrelatorBound,
  ClayWitnessHyp, CharacterExpansionData, SUNWilsonClusterMajorisation.

The trivial-group physics-degeneracy caveat (Finding 003) carries
forward.

Cross-references:
- `P8_PhysicalGap/LSIDefinitions.lean` — the four predicate
  definitions discharged here.
- `ClayCore/AbelianU1Unconditional.lean` — `Subsingleton` instance and
  `gibb_su1_isProbability` shared by all SU(1) discharges.
- `L6_OS/AbelianU1ClusterProperty.lean` (Phase 49) — companion file
  using the same `integral_eq_default_su1` helper pattern.
- `COWORK_FINDINGS.md` Finding 011 — OS-quartet completeness;
  this file extends the same logic to the Branch III analytic layer.
-/

end YangMills.P8
