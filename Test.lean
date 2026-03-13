import Mathlib
open MeasureTheory Set

private lemma lintegral_restrict_map_equiv
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

lemma lintegral_restrict_invariant
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (e : α ≃ᵐ α) (s : Set α) (hs : MeasurableSet s)
    (g : α → ENNReal) (hbase : Measure.map e ν = ν) (hg : g ∘ e = g) :
    ∫⁻ a in e ⁻¹' s, g a ∂ν = ∫⁻ a in s, g a ∂ν := by
  have h := lintegral_restrict_map_equiv ν g e s hs
  rw [hg, hbase] at h; exact h

example {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (f : α → ℝ) (e : α ≃ᵐ α)
    (hbase : Measure.map e ν = ν) (hf : f ∘ e = f)
    (s : Set α) (hs : MeasurableSet s) :
    (ν.tilted f) (e ⁻¹' s) = (ν.tilted f) s := by
  rw [tilted_apply' _ _ (e.measurable hs), tilted_apply' _ _ hs]
  apply lintegral_restrict_invariant ν e s hs _ hbase
  ext x
  have hfx : f (e x) = f x := congr_fun hf x
  simp [hfx]
