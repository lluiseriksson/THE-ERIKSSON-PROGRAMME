import Mathlib
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L1_GibbsMeasure.GibbsMeasure
import YangMills.L2_Balaban.SmallLargeDecomposition

namespace YangMills

open MeasureTheory Set

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]
variable (κ : ℝ) (plaquetteEnergy : G → ℝ) (β : ℝ)

/-! ## L2.2: Bałaban RG block-spin flow -/

omit [MeasurableSpace G] in
theorem largeField_exp_bound (U : GaugeConfig d N G)
    (hU : U ∈ LargeFieldSet κ plaquetteEnergy) (hβ : 0 ≤ β) :
    Real.exp (-β * wilsonAction plaquetteEnergy U) ≤ Real.exp (-β * κ) := by
  apply Real.exp_le_exp.mpr
  have hS : κ < wilsonAction plaquetteEnergy U := hU
  nlinarith

private lemma integrableIndicatorMul (μ : Measure G) [IsProbabilityMeasure μ]
    (h_meas : MeasurableSet (SmallFieldSet (d:=d) (N:=N) κ plaquetteEnergy))
    (h_int : Integrable (fun U : GaugeConfig d N G =>
      Real.exp (-β * wilsonAction plaquetteEnergy U)) (gaugeMeasureFrom (d:=d) (N:=N) μ)) :
    Integrable (fun U : GaugeConfig d N G =>
      χ_small κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U))
      (gaugeMeasureFrom (d:=d) (N:=N) μ) := by
  apply Integrable.congr (h_int.indicator h_meas)
  filter_upwards with U
  simp [χ_small, SmallFieldSet, Set.indicator]

private lemma integrableIndicatorMulLarge (μ : Measure G) [IsProbabilityMeasure μ]
    (h_meas : MeasurableSet (LargeFieldSet (d:=d) (N:=N) κ plaquetteEnergy))
    (h_int : Integrable (fun U : GaugeConfig d N G =>
      Real.exp (-β * wilsonAction plaquetteEnergy U)) (gaugeMeasureFrom (d:=d) (N:=N) μ)) :
    Integrable (fun U : GaugeConfig d N G =>
      χ_large κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U))
      (gaugeMeasureFrom (d:=d) (N:=N) μ) := by
  apply Integrable.congr (h_int.indicator h_meas)
  filter_upwards with U
  simp [χ_large, LargeFieldSet, Set.indicator]

theorem partitionFunction_split (μ : Measure G) [IsProbabilityMeasure μ]
    (h_small_meas : MeasurableSet (SmallFieldSet (d:=d) (N:=N) κ plaquetteEnergy))
    (h_large_meas : MeasurableSet (LargeFieldSet (d:=d) (N:=N) κ plaquetteEnergy))
    (h_int : Integrable (fun U : GaugeConfig d N G =>
      Real.exp (-β * wilsonAction plaquetteEnergy U)) (gaugeMeasureFrom (d:=d) (N:=N) μ)) :
    partitionFunction (d:=d) (N:=N) μ plaquetteEnergy β =
    (∫ U : GaugeConfig d N G,
      χ_small κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U)
      ∂(gaugeMeasureFrom (d:=d) (N:=N) μ)) +
    (∫ U : GaugeConfig d N G,
      χ_large κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U)
      ∂(gaugeMeasureFrom (d:=d) (N:=N) μ)) := by
  have h_small_int := integrableIndicatorMul κ plaquetteEnergy β μ h_small_meas h_int
  have h_large_int := integrableIndicatorMulLarge κ plaquetteEnergy β μ h_large_meas h_int
  unfold partitionFunction
  rw [← integral_add h_small_int h_large_int]
  congr 1; ext U
  have hid := decomposition_identity κ plaquetteEnergy U
  linarith [show χ_small κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U) +
                 χ_large κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U) =
                 Real.exp (-β * wilsonAction plaquetteEnergy U) by rw [← add_mul, hid, one_mul]]

theorem largeField_suppression (μ : Measure G) [IsProbabilityMeasure μ]
    (h_large_meas : MeasurableSet (LargeFieldSet (d:=d) (N:=N) κ plaquetteEnergy))
    (hβ : 0 ≤ β)
    (h_int : Integrable (fun U : GaugeConfig d N G =>
      Real.exp (-β * wilsonAction plaquetteEnergy U)) (gaugeMeasureFrom (d:=d) (N:=N) μ)) :
    ∫ U : GaugeConfig d N G,
      χ_large κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U)
      ∂(gaugeMeasureFrom (d:=d) (N:=N) μ) ≤ Real.exp (-β * κ) := by
  have h_large_int := integrableIndicatorMulLarge κ plaquetteEnergy β μ h_large_meas h_int
  calc ∫ U : GaugeConfig d N G,
        χ_large κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U)
        ∂(gaugeMeasureFrom (d:=d) (N:=N) μ)
      ≤ ∫ _ : GaugeConfig d N G, Real.exp (-β * κ) ∂(gaugeMeasureFrom (d:=d) (N:=N) μ) := by
        apply integral_mono h_large_int (integrable_const _)
        intro U
        simp only [χ_large, LargeFieldSet, Set.indicator, Set.mem_setOf_eq]
        split_ifs with h
        · simp only [one_mul]
          apply Real.exp_le_exp.mpr; nlinarith
        · simp; exact (Real.exp_pos _).le
    _ = Real.exp (-β * κ) := by simp

end YangMills
