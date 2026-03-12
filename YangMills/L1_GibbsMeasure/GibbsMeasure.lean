import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.ProbabilitySpace
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L0_Lattice.GaugeInvariance
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

namespace YangMills

variable {d N : ℕ} {G : Type _} [Group G] [FiniteLatticeGeometry d N G]
variable [TopologicalGroup G] [CompactSpace G] [MeasureSpace G]
  [IsHaarMeasure (haarMeasure (1 : G))]

/-!
# L1.1: Finite-volume partition function Z_β
-/

/-- Partition function: ∫ e^{-β S_W[U]} dμ_0[U] over the product Haar measure. -/
noncomputable def partitionFunction (β : ℝ) : ℝ :=
  ∫ U : GaugeConfig d N G, Real.exp (-β * wilsonAction U) ∂gaugeMeasure

theorem partitionFunction_pos (β : ℝ) : 0 < partitionFunction β := by
  have h_pos : ∀ U, 0 < Real.exp (-β * wilsonAction U) := by intro _; simp [Real.exp_pos]
  refine MeasureTheory.integral_pos (f := fun _ => Real.exp (-β * wilsonAction _))
    (h_pos := h_pos) (h_meas := gaugeMeasure_isProbability.measure_univ)

theorem partitionFunction_finite (β : ℝ) : partitionFunction β < ∞ := by
  apply MeasureTheory.integral_bounded
  · exact wilsonAction_bounded (β := β)
  · exact gaugeMeasure_isProbability

/-!
# L1.2: Finite-volume Gibbs measure
-/

/-- Gibbs measure: normalized Boltzmann weight. -/
noncomputable def gibbsMeasure (β : ℝ) : Measure (GaugeConfig d N G) :=
  (1 / partitionFunction β) • (fun U => Real.exp (-β * wilsonAction U)) • gaugeMeasure

instance (β : ℝ) : IsProbabilityMeasure (gibbsMeasure β) := by
  constructor
  simp [gibbsMeasure, partitionFunction_pos]
  rw [MeasureTheory.smul_apply, MeasureTheory.smul_apply]
  simp [MeasureTheory.integral_smul]

theorem gibbsMeasure_gauge_invariant (β : ℝ) (u : GaugeTransform d N G) :
    (gibbsMeasure β).map (gaugeAct u) = gibbsMeasure β := by
  simp [gibbsMeasure]
  rw [MeasureTheory.map_smul, MeasureTheory.map_smul]
  congr
  · exact MeasureTheory.map_const_smul (gaugeMeasure_isLeftInvariant)
  · ext U; simp [wilsonAction_gaugeInvariant]

end YangMills
