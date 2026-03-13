import Mathlib
import YangMills.L0_Lattice.WilsonAction
import YangMills.L1_GibbsMeasure.GibbsMeasure

namespace YangMills

open MeasureTheory Classical

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-! ## L4.1: Large-field suppression

The contribution of large-field configurations to the partition function
is exponentially suppressed. The hard analytic bound (Bałaban estimate)
is assumed as a hypothesis `h_bound`; this file proves the integral
inequality given that pointwise bound.
-/

/-- The large-field threshold at RG scale k. -/
noncomputable def largeFieldThreshold (k : ℕ) : ℝ := Real.exp (-(k : ℝ))

/-- A configuration is small-field at scale k if its Wilson action
    is within the threshold. -/
def isSmallField (plaquetteEnergy : G → ℝ) (k : ℕ) (U : GaugeConfig d N G) : Prop :=
  wilsonAction plaquetteEnergy U ≤ largeFieldThreshold k

/-- The Boltzmann weight of a configuration. -/
noncomputable def boltzmannWeight (plaquetteEnergy : G → ℝ) (β : ℝ)
    (U : GaugeConfig d N G) : ℝ :=
  Real.exp (-β * wilsonAction plaquetteEnergy U)

/-- The large-field indicator times Boltzmann weight is nonneg. -/
lemma largeField_integrand_nonneg (plaquetteEnergy : G → ℝ) (β : ℝ)
    (U : GaugeConfig d N G) :
    0 ≤ (if isSmallField plaquetteEnergy k U then (0:ℝ) else 1) *
        boltzmannWeight plaquetteEnergy β U := by
  apply mul_nonneg
  · split_ifs <;> norm_num
  · exact le_of_lt (Real.exp_pos _)

/-- The exponential bound: exp(-a) ≤ exp(-b) iff b ≤ a. -/
lemma exp_le_exp_of_le {a b : ℝ} (h : b ≤ a) : Real.exp (-a) ≤ Real.exp (-b) :=
  Real.exp_le_exp.mpr (by linarith)

/-- L4.1: Large-field suppression (integral form).

    Given a pointwise bound on the large-field Boltzmann weight,
    the integral over all configurations is bounded by the constant C.
    The hard Bałaban estimate enters only through `h_bound`. -/
theorem largeField_suppression_integral
    (plaquetteEnergy : G → ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (β : ℝ) (k : ℕ) (C : ℝ)
    (h_int : Integrable (fun U : GaugeConfig d N G =>
        (if isSmallField plaquetteEnergy k U then (0:ℝ) else 1) *
        boltzmannWeight plaquetteEnergy β U)
      (gaugeMeasureFrom (d:=d) (N:=N) μ))
    (h_bound : ∀ U : GaugeConfig d N G,
        (if isSmallField plaquetteEnergy k U then (0:ℝ) else 1) *
        boltzmannWeight plaquetteEnergy β U ≤ C) :
    ∫ U : GaugeConfig d N G,
        (if isSmallField plaquetteEnergy k U then (0:ℝ) else 1) *
        boltzmannWeight plaquetteEnergy β U
      ∂(gaugeMeasureFrom (d:=d) (N:=N) μ) ≤ C := by
  calc ∫ U : GaugeConfig d N G,
          (if isSmallField plaquetteEnergy k U then (0:ℝ) else 1) *
          boltzmannWeight plaquetteEnergy β U
          ∂(gaugeMeasureFrom (d:=d) (N:=N) μ)
      ≤ ∫ _ : GaugeConfig d N G, C ∂(gaugeMeasureFrom (d:=d) (N:=N) μ) :=
        integral_mono h_int (integrable_const C) (fun U => h_bound U)
    _ = C := by simp [integral_const]

/-- Corollary: when C = card(Plaquettes) * exp(-c*β*k),
    the large-field contribution is exponentially small. -/
theorem largeField_suppression_explicit_bound
    (plaquetteEnergy : G → ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (β : ℝ) (hβ : 0 < β) (k : ℕ) (c : ℝ) (hc : 0 < c)
    (h_int : Integrable (fun U : GaugeConfig d N G =>
        (if isSmallField plaquetteEnergy k U then (0:ℝ) else 1) *
        boltzmannWeight plaquetteEnergy β U)
      (gaugeMeasureFrom (d:=d) (N:=N) μ))
    (h_bound : ∀ U : GaugeConfig d N G,
        (if isSmallField plaquetteEnergy k U then (0:ℝ) else 1) *
        boltzmannWeight plaquetteEnergy β U ≤
        Real.exp (-(c * β * (k : ℝ)))) :
    ∫ U : GaugeConfig d N G,
        (if isSmallField plaquetteEnergy k U then (0:ℝ) else 1) *
        boltzmannWeight plaquetteEnergy β U
      ∂(gaugeMeasureFrom (d:=d) (N:=N) μ)
    ≤ Real.exp (-(c * β * (k : ℝ))) :=
  largeField_suppression_integral plaquetteEnergy μ β k _ h_int h_bound

end YangMills
