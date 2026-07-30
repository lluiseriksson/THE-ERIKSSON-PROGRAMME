/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.ThermodynamicLimit
import YangMills.L1_GibbsMeasure.WilsonObservable
import YangMills.ClayCore.SchurPhysicalBridge
import YangMills.ClayCore.WilsonPlaquetteEnergy
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Non-vacuity of the uniform local KP regime

The abstract thermodynamic-limit theorem is accompanied here by an explicit
strictly interacting witness.  We take `d = 2`, the physical group `SU(2)`
with normalized Haar measure, the plaquette energy `Re tr U`, and

`β = 10⁻¹⁰⁰ > 0`, `B = 2`, `t = ε = η = 1`.

Thus this is not the free `β = 0` theory.  The deliberately tiny rational
coupling leaves a large exact margin after the marked-set estimate, whose
largest exponential factor is bounded using `exp 1 < 3`.
-/

namespace YangMills

open MeasureTheory

namespace WindowPolymer

/-- A fixed, explicit and strictly positive coupling. -/
noncomputable def explicitStrongCouplingBeta : ℝ :=
  ((10 : ℝ) ^ 100)⁻¹

theorem explicitStrongCouplingBeta_pos :
    0 < explicitStrongCouplingBeta := by
  norm_num [explicitStrongCouplingBeta]

theorem explicitStrongCouplingBeta_ne_zero :
    explicitStrongCouplingBeta ≠ 0 :=
  ne_of_gt explicitStrongCouplingBeta_pos

/-- Integer exponential bound used to reduce the non-vacuity check to exact
rational arithmetic. -/
private theorem exp_nat_le_three_pow (n : ℕ) :
    Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
  calc
    Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
      rw [← Real.exp_nat_mul]
      simp
    _ ≤ (3 : ℝ) ^ n := by
      gcongr
      exact Real.exp_one_lt_three.le

/-- The physical `SU(2)` activity at the explicit nonzero coupling is at
most `4β`. -/
private theorem explicit_activity_le :
    Real.exp (|explicitStrongCouplingBeta| * 2) - 1 ≤
      4 * explicitStrongCouplingBeta := by
  have hβ0 : 0 ≤ explicitStrongCouplingBeta :=
    explicitStrongCouplingBeta_pos.le
  have hx0 : 0 ≤ |explicitStrongCouplingBeta| * 2 := by positivity
  have hx1 : |(|explicitStrongCouplingBeta| * 2)| ≤ 1 := by
    rw [abs_of_nonneg hx0, abs_of_nonneg hβ0]
    norm_num [explicitStrongCouplingBeta]
  have hy0 :
      0 ≤ Real.exp (|explicitStrongCouplingBeta| * 2) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hx0
  have h :=
    Real.abs_exp_sub_one_le
      (x := |explicitStrongCouplingBeta| * 2) hx1
  rw [abs_of_nonneg hy0, abs_of_nonneg hx0,
    abs_of_nonneg hβ0] at h
  calc
    Real.exp (|explicitStrongCouplingBeta| * 2) - 1 ≤
        2 * (explicitStrongCouplingBeta * 2) := by
      simpa [abs_of_pos explicitStrongCouplingBeta_pos] using h
    _ = 4 * explicitStrongCouplingBeta := by ring

private theorem explicit_activity_nonneg :
    0 ≤ Real.exp (|explicitStrongCouplingBeta| * 2) - 1 := by
  rw [sub_nonneg, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  positivity

/-- The common rational majorant for all exponentials occurring in the five
KP inequalities. -/
private noncomputable def explicitMasterWeight : ℝ :=
  (4 * explicitStrongCouplingBeta) * (3 : ℝ) ^ 129

/-- The exact arithmetic margin behind the non-vacuity witness. -/
private theorem explicitMasterWeight_margin :
    1121 * explicitMasterWeight < 1 := by
  norm_num [explicitMasterWeight, explicitStrongCouplingBeta]

private theorem activity_exp_le_master
    (k : ℕ) (hk : k ≤ 129) :
    (Real.exp (|explicitStrongCouplingBeta| * 2) - 1) *
        Real.exp (k : ℝ) ≤
      explicitMasterWeight := by
  have hβ0 : 0 ≤ explicitStrongCouplingBeta :=
    explicitStrongCouplingBeta_pos.le
  have hpow :
      Real.exp (k : ℝ) ≤ (3 : ℝ) ^ 129 := by
    exact (exp_nat_le_three_pow k).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hk)
  unfold explicitMasterWeight
  exact mul_le_mul explicit_activity_le hpow
    (Real.exp_pos _).le (by positivity)

private theorem radius_of_le_master
    (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ explicitMasterWeight) :
    1089 * z < 1 := by
  have h :=
    mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 1121)
  nlinarith [explicitMasterWeight_margin]

private theorem small_fraction_of_le_master
    (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ explicitMasterWeight) :
    32 * (z / (1 - 1089 * z)) ≤ 1 := by
  have h1121 :
      1121 * z < 1 := by
    have h :=
      mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 1121)
    exact h.trans_lt explicitMasterWeight_margin
  have hden : 0 < 1 - 1089 * z := by nlinarith
  rw [← mul_div_assoc, div_le_one hden]
  nlinarith

/-- **Explicit non-free inhabitant of `UniformLocalKPRegime`.**

All five fields are discharged from one rational master margin. -/
noncomputable def explicitSU2UniformLocalKPRegime :
    UniformLocalKPRegime 2 2 explicitStrongCouplingBeta where
  t := 1
  ε := 1
  η := 1
  t_nonneg := by norm_num
  ε_pos := by norm_num
  η_pos := by norm_num
  radius_tilt := by
    let z :=
      (Real.exp (|explicitStrongCouplingBeta| * 2) - 1) *
        Real.exp (1 + 1)
    have hz0 : 0 ≤ z := by
      dsimp only [z]
      exact mul_nonneg explicit_activity_nonneg (Real.exp_pos _).le
    have hz : z ≤ explicitMasterWeight := by
      dsimp only [z]
      norm_num
      exact activity_exp_le_master 2 (by norm_num)
    have hrad := radius_of_le_master z hz0 hz
    convert hrad using 1 <;> norm_num [z]
  small_tilt := by
    let z :=
      (Real.exp (|explicitStrongCouplingBeta| * 2) - 1) *
        Real.exp (1 + 1)
    have hz0 : 0 ≤ z := by
      dsimp only [z]
      exact mul_nonneg explicit_activity_nonneg (Real.exp_pos _).le
    have hz : z ≤ explicitMasterWeight := by
      dsimp only [z]
      norm_num
      exact activity_exp_le_master 2 (by norm_num)
    have hsmall := small_fraction_of_le_master z hz0 hz
    convert hsmall using 1 <;> norm_num [z]
  radius_unitTilt := by
    let z :=
      (Real.exp (|explicitStrongCouplingBeta| * 2) - 1) *
        Real.exp (1 + 1 + 1)
    have hz0 : 0 ≤ z := by
      dsimp only [z]
      exact mul_nonneg explicit_activity_nonneg (Real.exp_pos _).le
    have hz : z ≤ explicitMasterWeight := by
      dsimp only [z]
      norm_num
      exact activity_exp_le_master 3 (by norm_num)
    have hrad := radius_of_le_master z hz0 hz
    convert hrad using 1 <;> norm_num [z]
  small_unitTilt := by
    let z :=
      (Real.exp (|explicitStrongCouplingBeta| * 2) - 1) *
        Real.exp (1 + 1 + 1)
    have hz0 : 0 ≤ z := by
      dsimp only [z]
      exact mul_nonneg explicit_activity_nonneg (Real.exp_pos _).le
    have hz : z ≤ explicitMasterWeight := by
      dsimp only [z]
      norm_num
      exact activity_exp_le_master 3 (by norm_num)
    have hsmall := small_fraction_of_le_master z hz0 hz
    convert hsmall using 1 <;> norm_num [z]
  marked_radius := by
    let z :=
      localMarkedEffectiveWeight 2 2 explicitStrongCouplingBeta 1 *
        Real.exp 1
    have hz0 : 0 ≤ z := by
      dsimp only [z, localMarkedEffectiveWeight]
      exact mul_nonneg
        (mul_nonneg explicit_activity_nonneg (Real.exp_pos _).le)
        (Real.exp_pos _).le
    have hz : z ≤ explicitMasterWeight := by
      calc
        z =
            (Real.exp (|explicitStrongCouplingBeta| * 2) - 1) *
              Real.exp 65 := by
          dsimp only [z, localMarkedEffectiveWeight]
          rw [mul_assoc, ← Real.exp_add]
          norm_num
        _ ≤ explicitMasterWeight :=
          activity_exp_le_master 65 (by norm_num)
    have hrad := radius_of_le_master z hz0 hz
    convert hrad using 1 <;> norm_num [z]

end WindowPolymer

/-! ## Concrete physical endpoint -/

/-- The concrete gauge group used by the non-vacuity endpoint. -/
abbrev SU2GaugeGroup :=
  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)

/-- The nonconstant physical plaquette energy `Re tr U` on `SU(2)`. -/
noncomputable def su2FundamentalPlaquetteEnergy :
    SU2GaugeGroup → ℝ :=
  wilsonPlaquetteEnergy 2

theorem measurable_su2FundamentalPlaquetteEnergy :
    Measurable su2FundamentalPlaquetteEnergy := by
  exact (wilsonPlaquetteEnergy_continuous 2).measurable

theorem su2FundamentalPlaquetteEnergy_bounded
    (U : SU2GaugeGroup) :
    |su2FundamentalPlaquetteEnergy U| ≤ 2 := by
  simpa [su2FundamentalPlaquetteEnergy, wilsonPlaquetteEnergy,
    fundamentalObservable] using fundamentalObservable_bounded 2 U

/-- The chosen physical energy is genuinely nonzero, already at the
identity of `SU(2)`. -/
theorem su2FundamentalPlaquetteEnergy_nontrivial :
    su2FundamentalPlaquetteEnergy (1 : SU2GaugeGroup) ≠ 0 := by
  exact wilsonPlaquetteEnergy_nontrivial (by norm_num : 0 < 2)

/-- The chosen energy is not constant: its Haar mean is zero while its value
at the identity is two. -/
theorem su2FundamentalPlaquetteEnergy_not_constant :
    ¬ ∀ U V : SU2GaugeGroup,
        su2FundamentalPlaquetteEnergy U =
          su2FundamentalPlaquetteEnergy V := by
  intro hconst
  have hfun :
      su2FundamentalPlaquetteEnergy = fun _ : SU2GaugeGroup => 2 := by
    funext U
    calc
      su2FundamentalPlaquetteEnergy U =
          su2FundamentalPlaquetteEnergy (1 : SU2GaugeGroup) :=
        hconst U 1
      _ = 2 := wilsonPlaquetteEnergy_one 2
  have hmean :
      ∫ U, su2FundamentalPlaquetteEnergy U ∂(sunHaarProb 2) = 0 := by
    simpa [su2FundamentalPlaquetteEnergy, wilsonPlaquetteEnergy,
      fundamentalObservable] using
      fundamentalObservable_mean_zero 2 (by norm_num)
  rw [hfun] at hmean
  norm_num at hmean

/-- **Concrete non-free infinite-volume state.**

This endpoint discharges the abstract group, measurable-group, probability
measure, energy, bound and KP-regime parameters with `SU(2)`, normalized Haar
measure, `Re tr U`, and the explicit strictly positive coupling
`10⁻¹⁰⁰`. -/
noncomputable def explicitSU2InfiniteLocalGibbsState :
    WindowPolymer.PositiveNormalizedLocalState 2 SU2GaugeGroup :=
  WindowPolymer.infiniteLocalGibbsState
    (sunHaarProb 2)
    measurable_su2FundamentalPlaquetteEnergy
    su2FundamentalPlaquetteEnergy_bounded
    WindowPolymer.explicitSU2UniformLocalKPRegime

end YangMills
