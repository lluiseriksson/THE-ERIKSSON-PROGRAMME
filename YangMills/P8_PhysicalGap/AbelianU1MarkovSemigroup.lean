/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.AbelianU1Unconditional
import YangMills.P8_PhysicalGap.MarkovSemigroupDef

/-!
# SU(1) discharge of the Markov-semigroup framework

This module constructs an unconditional inhabitant of:
* `SymmetricMarkovTransport μ` (semigroup transport structure).
* `HasVarianceDecay sg` (Layer C: spectral gap).
* `MarkovSemigroup μ` (full transport + spectral gap).

for the SU(1) Wilson Gibbs measure on `GaugeConfig d L SU(1)`.

## Why it is trivial for SU(1)

The trick is the **identity transport**:

```
T : ℝ → (X → ℝ) → (X → ℝ) := fun t f => f
```

This satisfies every `SymmetricMarkovTransport` field by trivial
inspection (composition with identity, etc.), and it gives a Markov
semigroup with arbitrary positive spectral gap because the variance
`∫(f - ∫f)²` already vanishes for SU(1) (Subsingleton + probability
measure), so the decay inequality
`0 ≤ exp(-2γt) · 0` holds with arbitrary `γ > 0`.

## Caveat

The trivial-group physics-degeneracy of `COWORK_FINDINGS.md`
Findings 003 + 011 + 012 carries forward. The identity transport
is NOT a physical Yang-Mills heat semigroup — it has no time
evolution. For `N_c ≥ 2`, the Markov semigroup must come from the
honest C₀-semigroup theory (Hille-Yosida + Beurling-Deny), which
is a Mathlib upstream gap (frozen).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.P8

open MeasureTheory Real

variable {d L : ℕ} [NeZero d] [NeZero L]

abbrev SU1Cfg (d L : ℕ) [NeZero d] [NeZero L] : Type :=
  GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)

/-! ## §0. Subsingleton-integral helper -/

private lemma su1_integral_eq_default
    {μ : Measure (SU1Cfg d L)} [IsProbabilityMeasure μ]
    (f : SU1Cfg d L → ℝ) :
    (∫ U, f U ∂μ) = f default := by
  have h : (fun U : SU1Cfg d L => f U) = (fun _ => f default) := by
    funext U; rw [Subsingleton.elim U default]
  rw [h]; simp

/-! ## §1. Identity transport — the SU(1) `SymmetricMarkovTransport` witness -/

/-- The **identity transport** on the SU(1) Wilson Gibbs measure.

    `T t f = f` for every `t`. This satisfies every
    `SymmetricMarkovTransport` field by trivial inspection. -/
noncomputable def YangMills.identitySymmetricMarkovTransport_su1
    (β : ℝ) :
    SymmetricMarkovTransport
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β) where
  T             := fun _t f => f
  T_zero        := fun _ => rfl
  T_add         := fun _ _ _ => rfl
  T_const       := fun _ _ => rfl
  T_linear      := fun _ _ _ _ _ => rfl
  T_stat        := fun _ _ _ => rfl
  T_integrable  := fun _ _ h => h
  T_sq_integrable := fun _ _ h => h
  T_symm        := fun _ _ _ _ => rfl

/-! ## §2. HasVarianceDecay — unconditional for SU(1) -/

/-- **`HasVarianceDecay` discharged unconditionally for SU(1)**, with
    the identity transport. The variance `∫(T_t f - ∫f)² = ∫(f - ∫f)²`
    vanishes because `f` is constant (Subsingleton), so the inequality
    `0 ≤ exp(-2γt) · 0` holds with any `γ > 0`. -/
theorem hasVarianceDecay_identityTransport_su1
    (β : ℝ) :
    HasVarianceDecay
      (YangMills.identitySymmetricMarkovTransport_su1 (d := d) (L := L) β) := by
  refine ⟨1, one_pos, ?_⟩
  intro f _hf _hf2 t _ht
  -- T t f = f is definitional (identity transport)
  have hT : (YangMills.identitySymmetricMarkovTransport_su1
              (d := d) (L := L) β).T t f = f := rfl
  -- Variance vanishes for SU(1)
  have hVar :
      (∫ U : SU1Cfg d L,
        (f U - ∫ y, f y ∂(gibbsMeasure (d := d) (N := L)
          (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) ^ 2
        ∂(gibbsMeasure (d := d) (N := L)
          (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) = 0 := by
    have h_eq : (fun U : SU1Cfg d L =>
        (f U - ∫ y, f y ∂(gibbsMeasure (d := d) (N := L)
          (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) ^ 2)
          = (fun _ => 0) := by
      funext U
      have hfU : f U = f default := by rw [Subsingleton.elim U default]
      have hInt : (∫ y, f y ∂(gibbsMeasure (d := d) (N := L)
          (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) = f default :=
        su1_integral_eq_default f
      rw [hfU, hInt]; ring
    rw [h_eq]
    simp only [integral_zero]
  -- Apply: T t f = f, then variance = 0 on both sides, then 0 ≤ exp(...) * 0 = 0.
  rw [hT, hVar, hVar, mul_zero]
  exact le_refl 0

#print axioms hasVarianceDecay_identityTransport_su1

/-! ## §3. Full MarkovSemigroup for SU(1) -/

/-- **Full `MarkovSemigroup` for SU(1)**, built from the identity
    transport and a trivial spectral-gap witness with `γ = 1`. -/
noncomputable def markovSemigroup_su1
    (β : ℝ) :
    MarkovSemigroup
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β) where
  toSymmetricMarkovTransport :=
    YangMills.identitySymmetricMarkovTransport_su1 (d := d) (L := L) β
  T_spectral_gap := by
    refine ⟨1, one_pos, ?_⟩
    intro f _hf t _ht
    -- T t f = f (identity transport, definitional)
    have hT : (YangMills.identitySymmetricMarkovTransport_su1
                (d := d) (L := L) β).T t f = f := rfl
    -- Variance vanishes for SU(1)
    have hVar :
        (∫ U : SU1Cfg d L,
          (f U - ∫ y, f y ∂(gibbsMeasure (d := d) (N := L)
            (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) ^ 2
          ∂(gibbsMeasure (d := d) (N := L)
            (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) = 0 := by
      have h_eq : (fun U : SU1Cfg d L =>
          (f U - ∫ y, f y ∂(gibbsMeasure (d := d) (N := L)
            (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) ^ 2)
            = (fun _ => 0) := by
        funext U
        have hfU : f U = f default := by rw [Subsingleton.elim U default]
        have hInt : (∫ y, f y ∂(gibbsMeasure (d := d) (N := L)
            (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)) = f default :=
          su1_integral_eq_default f
        rw [hfU, hInt]; ring
      rw [h_eq]
      simp only [integral_zero]
    -- T t f = f and variance = 0 on both sides → 0 ≤ exp(...) * 0 = 0.
    rw [hT, hVar, hVar, mul_zero]
    exact le_refl 0

#print axioms markovSemigroup_su1

/-! ## §4. Coordination note -/

/-
SU(1) Markov-semigroup-framework status after Phase 54:

```
Predicate                    SU(1) inhabitant?  Witness
-----------------------------------------------------------
SymmetricMarkovTransport     ✓                  Phase 54 (identity)
HasVarianceDecay             ✓                  Phase 54 (γ = 1)
MarkovSemigroup              ✓                  Phase 54 (full)
```

Combined with Phases 46–50 (OS quartet) and Phase 53 (LSI/Poincaré
quartet), the SU(1) **structural-completeness frontier** now
covers:

* **OS axioms (4)**.
* **LSI / Poincaré / clustering (4)**.
* **Markov semigroup framework (3)**.
* **Clay-grade ladder (4+)**.

The trivial-group physics-degeneracy caveat carries forward
(Findings 003 + 011 + 012). For `N_c ≥ 2`, the Markov semigroup
construction is gated on Mathlib upstream C₀-semigroup theory
(see `Experimental/Semigroup/HilleYosidaDecomposition.lean` and the
`gronwall_variance_decay` / `variance_decay_from_bridge_and_poincare_semigroup_gap`
axioms classified as MATHLIB_GAP).

Cross-references:
- `MarkovSemigroupDef.lean` — the three structures discharged here.
- `LSIDefinitions.lean` — companion analytic predicates (Phase 53).
- `AbelianU1Unconditional.lean` — SU(1) Subsingleton + probability
  measure infrastructure shared by all SU(1) discharges.
- `COWORK_FINDINGS.md` Findings 003 + 011 + 012 — physics-degeneracy.
-/

end YangMills.P8
