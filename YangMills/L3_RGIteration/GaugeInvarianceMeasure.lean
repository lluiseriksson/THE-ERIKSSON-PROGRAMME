import Mathlib
import YangMills.L0_Lattice.GaugeInvariance
import YangMills.L1_GibbsMeasure.GibbsMeasure

namespace YangMills

open MeasureTheory Set

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-! ## L3.2: Gauge invariance of the Gibbs measure -/

section GaugeWeightInvariance
omit [MeasurableSpace G]

theorem gibbsWeight_gauge_invariant
    (plaquetteEnergy : G → ℝ) (β : ℝ)
    (hconj : ConjInvariant plaquetteEnergy)
    (u : GaugeTransform d N G) (U : GaugeConfig d N G) :
    -β * wilsonAction plaquetteEnergy (GaugeConfig.gaugeAct u U) =
    -β * wilsonAction plaquetteEnergy U := by
  congr 1; exact wilsonAction_gaugeInvariant plaquetteEnergy hconj u U

theorem gibbsTilt_gauge_invariant
    (plaquetteEnergy : G → ℝ) (β : ℝ)
    (hconj : ConjInvariant plaquetteEnergy)
    (u : GaugeTransform d N G) :
    (fun U : GaugeConfig d N G => -β * wilsonAction plaquetteEnergy (GaugeConfig.gaugeAct u U)) =
    (fun U : GaugeConfig d N G => -β * wilsonAction plaquetteEnergy U) := by
  ext U; exact gibbsWeight_gauge_invariant plaquetteEnergy β hconj u U

end GaugeWeightInvariance

private lemma lintegral_restrict_map_equiv'
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (g : α → ENNReal) (e : α ≃ᵐ α) (s : Set α) (hs : MeasurableSet s) :
    ∫⁻ a in e ⁻¹' s, (g ∘ e) a ∂ν = ∫⁻ a in s, g a ∂Measure.map e ν := by
  calc
    ∫⁻ a in e ⁻¹' s, (g ∘ e) a ∂ν
        = ∫⁻ a, g a ∂(Measure.map e (ν.restrict (e ⁻¹' s))) := by
          rw [lintegral_map_equiv g e]; rfl
    _ = ∫⁻ a, g a ∂((Measure.map e ν).restrict s) := by
          congr 1; ext t ht
          rw [Measure.map_apply e.measurable ht,
              Measure.restrict_apply (e.measurable ht),
              Measure.restrict_apply ht,
              Measure.map_apply e.measurable (ht.inter hs),
              preimage_inter]
    _ = ∫⁻ a in s, g a ∂Measure.map e ν := rfl

private lemma lintegral_restrict_invariant'
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (e : α ≃ᵐ α) (s : Set α) (hs : MeasurableSet s)
    (g : α → ENNReal) (hbase : Measure.map e ν = ν) (hg : g ∘ e = g) :
    ∫⁻ a in e ⁻¹' s, g a ∂ν = ∫⁻ a in s, g a ∂ν := by
  have h := lintegral_restrict_map_equiv' ν g e s hs
  rw [hg, hbase] at h; exact h

private lemma tilted_preimage_eq
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (f : α → ℝ) (e : α ≃ᵐ α)
    (hbase : Measure.map e ν = ν) (hf : f ∘ e = f)
    (s : Set α) (hs : MeasurableSet s) :
    (ν.tilted f) (e ⁻¹' s) = (ν.tilted f) s := by
  rw [tilted_apply' _ _ (e.measurable hs), tilted_apply' _ _ hs]
  apply lintegral_restrict_invariant' ν e s hs _ hbase
  ext x
  simp [congr_fun hf x]

/-- The Gibbs measure is gauge invariant.
    - hbase: Measure.map e (gaugeMeasureFrom μ) = gaugeMeasureFrom μ
      (holds when μ is Haar; proved in L3.3)
    - htilt: the Boltzmann weight is e-invariant
      (follows from gibbsTilt_gauge_invariant when e = gaugeAct u) -/
theorem gibbsMeasure_gauge_invariant
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (e : GaugeConfig d N G ≃ᵐ GaugeConfig d N G)
    (hbase : Measure.map e (gaugeMeasureFrom (d:=d) (N:=N) μ) =
             gaugeMeasureFrom (d:=d) (N:=N) μ)
    (htilt : (fun U : GaugeConfig d N G => -β * wilsonAction plaquetteEnergy (e U)) =
             (fun U => -β * wilsonAction plaquetteEnergy U)) :
    Measure.map e (gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β) =
    gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β := by
  unfold gibbsMeasure
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  exact tilted_preimage_eq (gaugeMeasureFrom μ)
    (fun U => -β * wilsonAction plaquetteEnergy U) e hbase
    (by ext U; exact congr_fun htilt U) s hs

end YangMills
