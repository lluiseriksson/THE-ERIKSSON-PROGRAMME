import Mathlib
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L1_GibbsMeasure.GibbsMeasure
import YangMills.L2_Balaban.SmallLargeDecomposition

namespace YangMills

open MeasureTheory Set

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-! ## L2.3: Measurability of small/large field sets -/

/-- gaugeConfigEquiv.symm is measurable by definition of the comap measurable space. -/
lemma measurable_gaugeConfigEquiv_symm :
    Measurable (gaugeConfigEquiv (d:=d) (N:=N) (G:=G)).symm := by
  apply Measurable.of_comap_le
  simp [instMeasurableSpaceGaugeConfig]

/-- Evaluation at a positive edge is measurable. -/
lemma measurable_toFun_posEdge (e : PosEdge d N) :
    Measurable (fun U : GaugeConfig d N G => U.toFun e.val) := by
  have h_eq : (fun U : GaugeConfig d N G => U.toFun e.val) =
      (fun f : PosEdge d N → G => f e) ∘ gaugeConfigEquiv.symm := by
    ext U; simp [gaugeConfigEquiv, configToPos]
  rw [h_eq]
  exact (measurable_pi_apply e).comp measurable_gaugeConfigEquiv_symm

/-- Evaluation at any edge is measurable (positive or negative via inverse). -/
lemma measurable_toFun_edge [MeasurableInv G] [MeasurableMul₂ G] (e : ConcreteEdge d N) :
    Measurable (fun U : GaugeConfig d N G => U.toFun e) := by
  by_cases h : e.sign = true
  · exact measurable_toFun_posEdge ⟨e, h⟩
  · have h_neg : ∀ U : GaugeConfig d N G,
        U.toFun e = (U.toFun { e with sign := true })⁻¹ := by
      intro U
      have := U.map_reverse { e with sign := true }
      simp [finBoxGeometry_reverse] at this
      cases e; simp_all
    simp_rw [h_neg]
    exact (measurable_toFun_posEdge ⟨{ e with sign := true }, rfl⟩).inv

/-- Plaquette holonomy is measurable once multiplication and inversion on the
gauge group are measurable. -/
lemma measurable_plaquetteHolonomy [MeasurableInv G] [MeasurableMul₂ G]
    (p : ConcretePlaquette d N) :
    Measurable (fun U : GaugeConfig d N G => GaugeConfig.plaquetteHolonomy U p) := by
  unfold GaugeConfig.plaquetteHolonomy
  apply Measurable.mul
  apply Measurable.mul
  apply Measurable.mul
  · exact measurable_toFun_edge _
  · exact measurable_toFun_edge _
  · exact measurable_toFun_edge _
  · exact measurable_toFun_edge _

/-- wilsonAction is measurable given measurable plaquetteEnergy and MeasurableMul. -/
lemma measurable_wilsonAction [MeasurableInv G] [MeasurableMul₂ G]
    (plaquetteEnergy : G → ℝ) (h : Measurable plaquetteEnergy) :
    Measurable (fun U : GaugeConfig d N G => wilsonAction plaquetteEnergy U) := by
  unfold wilsonAction
  apply Finset.measurable_sum
  intro p _
  apply h.comp
  unfold GaugeConfig.plaquetteHolonomy
  apply Measurable.mul
  apply Measurable.mul
  apply Measurable.mul
  · exact measurable_toFun_edge _
  · exact measurable_toFun_edge _
  · exact measurable_toFun_edge _
  · exact measurable_toFun_edge _

/-- SmallFieldSet is measurable. -/
theorem measurableSet_smallFieldSet [MeasurableInv G] [MeasurableMul₂ G]
    (plaquetteEnergy : G → ℝ) (h : Measurable plaquetteEnergy) (κ : ℝ) :
    MeasurableSet (SmallFieldSet (d:=d) (N:=N) κ plaquetteEnergy) := by
  unfold SmallFieldSet
  exact measurableSet_le (measurable_wilsonAction plaquetteEnergy h) measurable_const

/-- LargeFieldSet is measurable. -/
theorem measurableSet_largeFieldSet [MeasurableInv G] [MeasurableMul₂ G]
    (plaquetteEnergy : G → ℝ) (h : Measurable plaquetteEnergy) (κ : ℝ) :
    MeasurableSet (LargeFieldSet (d:=d) (N:=N) κ plaquetteEnergy) := by
  unfold LargeFieldSet
  exact measurableSet_lt measurable_const (measurable_wilsonAction plaquetteEnergy h)

#print axioms measurable_plaquetteHolonomy

end YangMills
