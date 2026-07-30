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

The point witness is strengthened below to the explicit interval

`0 < |β| ≤ 10⁻⁵`,

using `t = ε = η = 10⁻²`.  The interval estimate uses the quadratic
remainder of the exponential, rather than the deliberately coarse pointwise
majorant used by the original witness.
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

/-- Explicit radius of the rigorously verified interacting interval. -/
noncomputable def explicitStrongCouplingRadius : ℝ :=
  ((10 : ℝ) ^ 5)⁻¹

theorem explicitStrongCouplingRadius_pos :
    0 < explicitStrongCouplingRadius := by
  norm_num [explicitStrongCouplingRadius]

private theorem interval_activity_nonneg (β : ℝ) :
    0 ≤ Real.exp (|β| * 2) - 1 := by
  rw [sub_nonneg, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (mul_nonneg (abs_nonneg β) (by norm_num))

/-- On the whole explicit interval, the physical Mayer activity is at most
`2.1 |β|`.  The improvement over the coarse factor `4` comes from the
quadratic remainder estimate for `exp`. -/
private theorem interval_activity_le
    (β : ℝ) (hβ : |β| ≤ explicitStrongCouplingRadius) :
    Real.exp (|β| * 2) - 1 ≤ (21 / 10 : ℝ) * |β| := by
  let b : ℝ := |β|
  let x : ℝ := b * 2
  have hb0 : 0 ≤ b := by simp [b]
  have hb : b ≤ (1 / 100000 : ℝ) := by
    calc
      b ≤ explicitStrongCouplingRadius := by simpa [b] using hβ
      _ = (1 / 100000 : ℝ) := by
        norm_num [explicitStrongCouplingRadius]
  have hx0 : 0 ≤ x := mul_nonneg hb0 (by norm_num)
  have hx1 : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    dsimp only [x]
    nlinarith
  have hrem := Real.abs_exp_sub_one_sub_id_le hx1
  have hupper :
      Real.exp x - 1 - x ≤ x ^ 2 :=
    (le_abs_self (Real.exp x - 1 - x)).trans hrem
  have hmul : 0 ≤ b * ((1 / 40 : ℝ) - b) :=
    mul_nonneg hb0 (by nlinarith)
  calc
    Real.exp (|β| * 2) - 1 = Real.exp x - 1 := by
      rfl
    _ ≤ x + x ^ 2 := by linarith
    _ ≤ (21 / 10 : ℝ) * |β| := by
      dsimp only [x, b]
      nlinarith

private theorem exp_one_fiftieth_le :
    Real.exp (1 / 50 : ℝ) ≤ (50 / 49 : ℝ) := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (x := (1 / 50 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

private theorem exp_fifty_one_fiftieth_le :
    Real.exp (51 / 50 : ℝ) ≤ (150 / 49 : ℝ) := by
  rw [show (51 / 50 : ℝ) = 1 + 1 / 50 by norm_num, Real.exp_add]
  calc
    Real.exp 1 * Real.exp (1 / 50 : ℝ)
        ≤ 3 * (50 / 49 : ℝ) := by
      exact mul_le_mul Real.exp_one_lt_three.le exp_one_fiftieth_le
        (Real.exp_pos _).le (by norm_num)
    _ = (150 / 49 : ℝ) := by ring

private theorem exp_two_hundredths_le :
    Real.exp (2 / 100 : ℝ) ≤ (150 / 49 : ℝ) := by
  calc
    Real.exp (2 / 100 : ℝ) = Real.exp (1 / 50 : ℝ) := by norm_num
    _ ≤ (50 / 49 : ℝ) := exp_one_fiftieth_le
    _ ≤ (150 / 49 : ℝ) := by norm_num

private theorem exp_sixty_five_hundredths_le :
    Real.exp (65 / 100 : ℝ) ≤ (150 / 49 : ℝ) := by
  calc
    Real.exp (65 / 100 : ℝ) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by norm_num)
    _ ≤ 3 := Real.exp_one_lt_three.le
    _ ≤ (150 / 49 : ℝ) := by norm_num

private noncomputable def intervalMasterWeight : ℝ :=
  (21 / 10 : ℝ) * explicitStrongCouplingRadius * (150 / 49 : ℝ)

private theorem intervalMasterWeight_margin :
    4289 * intervalMasterWeight < 1 := by
  norm_num [intervalMasterWeight, explicitStrongCouplingRadius]

private theorem interval_weight_le_master
    (β s : ℝ) (hβ : |β| ≤ explicitStrongCouplingRadius)
    (hs : Real.exp s ≤ (150 / 49 : ℝ)) :
    (Real.exp (|β| * 2) - 1) * Real.exp s ≤
      intervalMasterWeight := by
  unfold intervalMasterWeight
  have hactivity :
      Real.exp (|β| * 2) - 1 ≤
        (21 / 10 : ℝ) * explicitStrongCouplingRadius :=
    (interval_activity_le β hβ).trans
      (mul_le_mul_of_nonneg_left hβ (by norm_num))
  exact mul_le_mul hactivity hs
    (Real.exp_pos _).le
    (mul_nonneg (by norm_num) explicitStrongCouplingRadius_pos.le)

private theorem interval_radius_of_le_master
    (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ intervalMasterWeight) :
    1089 * z < 1 := by
  have h4289 : 4289 * z < 1 := by
    exact (mul_le_mul_of_nonneg_left hz (by norm_num)).trans_lt
      intervalMasterWeight_margin
  nlinarith

private theorem interval_small_of_le_master
    (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ intervalMasterWeight) :
    32 * (z / (1 - 1089 * z)) ≤ (1 / 100 : ℝ) := by
  have h4289 : 4289 * z < 1 := by
    exact (mul_le_mul_of_nonneg_left hz (by norm_num)).trans_lt
      intervalMasterWeight_margin
  have hden : 0 < 1 - 1089 * z := by nlinarith
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith

/-- **Uniform KP regime on a nontrivial interval.**

Every coupling with `|β| ≤ 10⁻⁵` satisfies all five uniform KP
inequalities for `d = 2`, `B = 2`, and
`t = ε = η = 10⁻²`.  The punctured interval gives genuinely interacting
models. -/
noncomputable def su2UniformLocalKPRegimeOfBound
    (β : ℝ) (hβ : |β| ≤ explicitStrongCouplingRadius) :
    UniformLocalKPRegime 2 2 β where
  t := 1 / 100
  ε := 1 / 100
  η := 1 / 100
  t_nonneg := by norm_num
  ε_pos := by norm_num
  η_pos := by norm_num
  radius_tilt := by
    let z := (Real.exp (|β| * 2) - 1) *
      Real.exp ((1 / 100 : ℝ) + 1 / 100)
    have hz0 : 0 ≤ z :=
      mul_nonneg (interval_activity_nonneg β) (Real.exp_pos _).le
    have hz : z ≤ intervalMasterWeight := by
      apply interval_weight_le_master β
        ((1 / 100 : ℝ) + 1 / 100) hβ
      convert exp_two_hundredths_le using 1 <;> norm_num
    have hrad := interval_radius_of_le_master z hz0 hz
    convert hrad using 1 <;> norm_num [z]
  small_tilt := by
    let z := (Real.exp (|β| * 2) - 1) *
      Real.exp ((1 / 100 : ℝ) + 1 / 100)
    have hz0 : 0 ≤ z :=
      mul_nonneg (interval_activity_nonneg β) (Real.exp_pos _).le
    have hz : z ≤ intervalMasterWeight := by
      apply interval_weight_le_master β
        ((1 / 100 : ℝ) + 1 / 100) hβ
      convert exp_two_hundredths_le using 1 <;> norm_num
    have hsmall := interval_small_of_le_master z hz0 hz
    convert hsmall using 1 <;> norm_num [z]
  radius_unitTilt := by
    let z := (Real.exp (|β| * 2) - 1) *
      Real.exp ((1 / 100 : ℝ) + 1 / 100 + 1)
    have hz0 : 0 ≤ z :=
      mul_nonneg (interval_activity_nonneg β) (Real.exp_pos _).le
    have hz : z ≤ intervalMasterWeight := by
      apply interval_weight_le_master β
        ((1 / 100 : ℝ) + 1 / 100 + 1) hβ
      convert exp_fifty_one_fiftieth_le using 1 <;> norm_num
    have hrad := interval_radius_of_le_master z hz0 hz
    convert hrad using 1 <;> norm_num [z]
  small_unitTilt := by
    let z := (Real.exp (|β| * 2) - 1) *
      Real.exp ((1 / 100 : ℝ) + 1 / 100 + 1)
    have hz0 : 0 ≤ z :=
      mul_nonneg (interval_activity_nonneg β) (Real.exp_pos _).le
    have hz : z ≤ intervalMasterWeight := by
      apply interval_weight_le_master β
        ((1 / 100 : ℝ) + 1 / 100 + 1) hβ
      convert exp_fifty_one_fiftieth_le using 1 <;> norm_num
    have hsmall := interval_small_of_le_master z hz0 hz
    convert hsmall using 1 <;> norm_num [z]
  marked_radius := by
    let z := localMarkedEffectiveWeight 2 2 β (1 / 100) *
      Real.exp (1 / 100)
    have hz0 : 0 ≤ z := by
      dsimp only [z, localMarkedEffectiveWeight]
      exact mul_nonneg
        (mul_nonneg (interval_activity_nonneg β) (Real.exp_pos _).le)
        (Real.exp_pos _).le
    have hz : z ≤ intervalMasterWeight := by
      calc
        z = (Real.exp (|β| * 2) - 1) *
            Real.exp (65 / 100 : ℝ) := by
          dsimp only [z, localMarkedEffectiveWeight]
          rw [mul_assoc, ← Real.exp_add]
          norm_num
        _ ≤ intervalMasterWeight :=
          interval_weight_le_master β (65 / 100) hβ
            exp_sixty_five_hundredths_le
    have hrad := interval_radius_of_le_master z hz0 hz
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

/-- **Concrete family on the punctured strong-coupling interval.**

For every real `β` with `0 < |β| ≤ 10⁻⁵`, this is the positive normalized
infinite-volume state of the nonconstant physical `SU(2)` plaquette energy.
The positivity hypothesis is recorded explicitly so this endpoint cannot be
mistaken for the free theory. -/
noncomputable def su2InfiniteLocalGibbsStateOnPuncturedInterval
    (β : ℝ) (_hβpos : 0 < |β|)
    (hβ : |β| ≤ WindowPolymer.explicitStrongCouplingRadius) :
    WindowPolymer.PositiveNormalizedLocalState 2 SU2GaugeGroup :=
  WindowPolymer.infiniteLocalGibbsState
    (sunHaarProb 2)
    measurable_su2FundamentalPlaquetteEnergy
    su2FundamentalPlaquetteEnergy_bounded
    (WindowPolymer.su2UniformLocalKPRegimeOfBound β hβ)

end YangMills
