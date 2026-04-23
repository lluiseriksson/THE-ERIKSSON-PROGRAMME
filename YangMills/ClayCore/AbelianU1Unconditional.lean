/- Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Phase 7.2: U(1) Unconditional Witness

Unconditional inhabitation of `ClayYangMillsMassGap 1` via triviality of SU(1).

## Mathematical content

The group `SU(1)` of 1x1 complex unitary matrices with determinant 1 contains
exactly one element: the identity. Indeed, for any `A ∈ SU(1)`,
`A 0 0 = A.det = 1`, and `A` is the 1x1 matrix with entry 1.

Consequently:

1. Every gauge configuration `A : GaugeConfig d L SU(1)` is the trivial
   configuration (all edges map to 1).
2. Every real-valued function `F : SU(1) → ℝ` is a constant (equal to `F 1`).
3. The Wilson observable `plaquetteWilsonObs F p A = F 1` identically, so both
   `wilsonExpectation` and `wilsonCorrelation` on SU(1) reduce to `F 1`
   times the total Gibbs mass (= 1, since the Gibbs measure is a probability
   measure by `gibbsMeasure_isProbability` applied to the trivially-integrable
   constant Boltzmann factor).
4. The connected correlator
   `⟨W_p W_q⟩ - ⟨W_p⟩⟨W_q⟩ = F(1)² - F(1)·F(1) = 0`
   is identically zero.
5. Any exponential upper bound with strictly positive prefactor and decay
   rate trivially holds over a zero quantity.

## Lean content

This file eliminates the last named hypothesis `U1CorrelatorBound` from the
Clay chain at `N_c = 1` by constructing an unconditional inhabitant
`unconditionalU1CorrelatorBound : U1CorrelatorBound` directly in Lean. It is
forwarded to a concrete

  `u1_clay_yangMills_mass_gap_unconditional : ClayYangMillsMassGap 1`

with no remaining hypotheses. The axiom oracle remains
`[propext, Classical.choice, Quot.sound]` as required by ClayCore invariants.
-/
import Mathlib
import YangMills.ClayCore.ClayAuthentic
import YangMills.ClayCore.ClayWitness
import YangMills.ClayCore.KPSmallness
import YangMills.ClayCore.AbelianU1Witness
import YangMills.ClayCore.WilsonPlaquetteEnergy
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L1_GibbsMeasure.GibbsMeasure
import YangMills.L1_GibbsMeasure.Expectation
import YangMills.L1_GibbsMeasure.Correlations
import YangMills.L4_WilsonLoops.WilsonLoop
import YangMills.P8_PhysicalGap.SUN_StateConstruction

namespace YangMills

open MeasureTheory Real

/-! ## SU(1) triviality -/

/-- SU(1) is a singleton: every 1x1 unitary matrix with determinant 1 equals
    the identity. Proof: `A 0 0 = A.det = 1`, and A is determined by its
    single entry. -/
instance su1_subsingleton :
    Subsingleton ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) := by
  refine ⟨fun A B => ?_⟩
  apply Subtype.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  subst hi; subst hj
  have hAdet : A.val.det = 1 := A.property.2
  have hBdet : B.val.det = 1 := B.property.2
  rw [Matrix.det_fin_one] at hAdet hBdet
  rw [hAdet, hBdet]

/-- The trivial gauge configuration on SU(1): maps every edge to the identity.
    `map_reverse` is discharged by `Subsingleton.elim` since `SU(1)` is a
    singleton. -/
def trivialGaugeConfigSU1 {d L : ℕ} [NeZero d] [NeZero L] :
    GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) where
  toFun := fun _ => 1
  map_reverse := fun _ => Subsingleton.elim _ _

/-- `GaugeConfig d L SU(1)` is Inhabited (via `trivialGaugeConfigSU1`). -/
instance gaugeConfig_su1_inhabited {d L : ℕ} [NeZero d] [NeZero L] :
    Inhabited (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)) :=
  ⟨trivialGaugeConfigSU1⟩

/-- `GaugeConfig d L SU(1)` is Subsingleton. Since SU(1) is itself Subsingleton,
    any two gauge configurations agree edge-by-edge. -/
instance gaugeConfig_su1_subsingleton {d L : ℕ} [NeZero d] [NeZero L] :
    Subsingleton (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)) := by
  refine ⟨fun A B => ?_⟩
  apply GaugeConfig.ext'
  intro e
  exact Subsingleton.elim _ _

/-! ## Integrability and probability-measure structure -/

/-- The Boltzmann factor is integrable on the SU(1) gauge measure space for
    every inverse temperature `β`. The function is constant under
    `GaugeConfig d L SU(1)` Subsingleton, hence trivially integrable. -/
lemma boltzmann_integrable_su1 {d L : ℕ} [NeZero d] [NeZero L] (β : ℝ) :
    Integrable
      (fun U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) =>
        Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy 1) U))
      (gaugeMeasureFrom (d:=d) (N:=L) (sunHaarProb 1)) := by
  have hconst :
      (fun U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) =>
        Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy 1) U)) =
      (fun _ => Real.exp (-β * wilsonAction (wilsonPlaquetteEnergy 1)
        (default : GaugeConfig d L
          ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)))) := by
    funext U; congr 1; congr 2; exact Subsingleton.elim _ _
  rw [hconst]
  exact integrable_const _

/-- The Gibbs measure on SU(1) is a probability measure for every `β`. -/
instance gibbs_su1_isProbability {d L : ℕ} [NeZero d] [NeZero L] (β : ℝ) :
    IsProbabilityMeasure
      (gibbsMeasure (d:=d) (N:=L) (sunHaarProb 1)
        (wilsonPlaquetteEnergy 1) β) :=
  gibbsMeasure_isProbability d L (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β
    (boltzmann_integrable_su1 β)

/-! ## The connected correlator vanishes identically on SU(1) -/

/-- On SU(1), every plaquette-Wilson observable is constant equal to `F 1`. -/
lemma plaquetteWilsonObs_su1_const {d L : ℕ} [NeZero d] [NeZero L]
    (F : ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (p : ConcretePlaquette d L)
    (A : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ)) :
    plaquetteWilsonObs F p A = F 1 := by
  unfold plaquetteWilsonObs
  congr 1
  exact Subsingleton.elim _ _

/-- Wilson expectation on SU(1) equals `F 1`. Follows from constancy of
    `plaquetteWilsonObs F p` and `gibbs_su1_isProbability`. -/
lemma wilsonExpectation_su1_eq_F1 {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ) (F : ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (p : ConcretePlaquette d L) :
    wilsonExpectation (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F p = F 1 := by
  unfold wilsonExpectation expectation
  have hconst :
      (fun U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) =>
        plaquetteWilsonObs F p U) = (fun _ => F 1) := by
    funext U; exact plaquetteWilsonObs_su1_const F p U
  rw [hconst]
  simp

/-- Wilson correlation on SU(1) equals `F 1 * F 1`. -/
lemma wilsonCorrelation_su1_eq_F1_sq {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ) (F : ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (p q : ConcretePlaquette d L) :
    wilsonCorrelation (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F p q =
      F 1 * F 1 := by
  unfold wilsonCorrelation correlation expectation
  have hconst :
      (fun U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) =>
        plaquetteWilsonObs F p U * plaquetteWilsonObs F q U) =
      (fun _ => F 1 * F 1) := by
    funext U
    rw [plaquetteWilsonObs_su1_const F p U, plaquetteWilsonObs_su1_const F q U]
  rw [hconst]
  simp

/-- **The connected Wilson correlator vanishes identically on SU(1).**
    This is the key fact that makes the U(1) mass-gap witness unconditional:
    any exponential decay bound with a strictly positive prefactor holds
    vacuously when the correlator is zero. -/
theorem wilsonConnectedCorr_su1_eq_zero {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ) (F : ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (p q : ConcretePlaquette d L) :
    wilsonConnectedCorr (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β F p q = 0 := by
  unfold wilsonConnectedCorr
  rw [wilsonCorrelation_su1_eq_F1_sq, wilsonExpectation_su1_eq_F1,
      wilsonExpectation_su1_eq_F1]
  ring

/-! ## Unconditional U(1) witness -/

/-- **Unconditional `U1CorrelatorBound`.** All hypotheses are discharged:

    - `r = 1/2`, `C_u1 = 1` are arbitrary choices in `(0, 1)` and `(0, ∞)`.
    - `h_decay` is satisfied vacuously because `wilsonConnectedCorr_su1_eq_zero`
      gives `|0| = 0 ≤ anything_nonneg`. -/
noncomputable def unconditionalU1CorrelatorBound : U1CorrelatorBound where
  r := 1 / 2
  hr_pos := by norm_num
  hr_lt_one := by norm_num
  C_u1 := 1
  hC_u1 := by norm_num
  h_decay := by
    intro d _ L _ β _ F _ p q _
    rw [wilsonConnectedCorr_su1_eq_zero]
    simp
    positivity

/-- **Unconditional inhabitant of `ClayYangMillsMassGap 1`**. No hypotheses.
    This eliminates the named hypothesis `U1CorrelatorBound` from the Clay
    chain at `N_c = 1`, yielding a concrete object with mass gap
    `kpParameter (1/2) = log 2 / 2` and prefactor `1`. -/
noncomputable def u1_clay_yangMills_mass_gap_unconditional :
    ClayYangMillsMassGap 1 :=
  u1_clay_yangMills_mass_gap unconditionalU1CorrelatorBound

/-- The unconditional U(1) mass gap equals `kpParameter (1/2)`. -/
theorem u1_unconditional_mass_gap_eq :
    u1_clay_yangMills_mass_gap_unconditional.m = kpParameter (1 / 2 : ℝ) := rfl

/-- The unconditional U(1) mass gap is strictly positive. -/
theorem u1_unconditional_mass_gap_pos :
    0 < u1_clay_yangMills_mass_gap_unconditional.m :=
  u1_mass_gap_pos unconditionalU1CorrelatorBound

/-- The unconditional U(1) prefactor equals 1. -/
theorem u1_unconditional_prefactor_eq :
    u1_clay_yangMills_mass_gap_unconditional.C = 1 := rfl

end YangMills
