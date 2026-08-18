import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory

noncomputable section

def reproNormalizedBrillouinMeasure : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) •
    volume.restrict (Set.Ioc 0 (2 * Real.pi))

theorem reproMeasurePreservingScale :
    MeasurePreserving
      (fun x : ℝ => (2 * Real.pi)⁻¹ * x)
      reproNormalizedBrillouinMeasure
      (volume.restrict (Set.Ioc 0 1)) := by
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hcinv : c⁻¹ ≠ 0 := inv_ne_zero hc0
  let e : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ c⁻¹ hcinv
  have hpreimage :
      (fun x : ℝ => c⁻¹ * x) ⁻¹' Set.Ioc 0 1 = Set.Ioc 0 c := by
    rw [Set.preimage_const_mul_Ioc₀ 0 1 (inv_pos.mpr hc)]
    field_simp [hc0]
    simp
  have hrestrict := e.measurableEmbedding.restrict_map
    (volume : Measure ℝ) (Set.Ioc 0 1)
  have hrestrict' :
      (Measure.map (fun x : ℝ => c⁻¹ * x) volume).restrict
          (Set.Ioc 0 1) =
        Measure.map (fun x : ℝ => c⁻¹ * x)
          (volume.restrict
            ((fun x : ℝ => c⁻¹ * x) ⁻¹' Set.Ioc 0 1)) := by
    simpa [e] using hrestrict
  have hmap :
      Measure.map (fun x : ℝ => c⁻¹ * x) volume =
        ENNReal.ofReal c • volume := by
    simpa [c, abs_of_pos hc] using
      (Real.map_volume_mul_left hcinv)
  refine ⟨measurable_const_mul _, ?_⟩
  unfold reproNormalizedBrillouinMeasure
  change Measure.map (fun x : ℝ => c⁻¹ * x)
      (ENNReal.ofReal c⁻¹ • volume.restrict (Set.Ioc 0 c)) =
    volume.restrict (Set.Ioc 0 1)
  rw [Measure.map_smul]
  rw [← hpreimage, ← hrestrict']
  rw [hmap, Measure.restrict_smul, smul_smul]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
  simp [hc0]

def reproPhysicalBrillouinToCircle (x : ℝ) : UnitAddCircle :=
  (((1 / 2 : ℝ) - (2 * Real.pi)⁻¹ * x : ℝ) : UnitAddCircle)

example :
    MeasurePreserving reproPhysicalBrillouinToCircle
      reproNormalizedBrillouinMeasure
      (volume : Measure UnitAddCircle) := by
  have hscale : MeasurePreserving
      (fun x : ℝ => (2 * Real.pi)⁻¹ * x)
      reproNormalizedBrillouinMeasure
      (volume.restrict (Set.Ioc 0 1)) := by
    exact reproMeasurePreservingScale
  have hquot := AddCircle.measurePreserving_mk (1 : ℝ) (0 : ℝ)
  have hquot' :
      MeasurePreserving
        (fun x : ℝ => (x : UnitAddCircle))
        (volume.restrict (Set.Ioc 0 1))
        (volume : Measure UnitAddCircle) := by
    simpa using hquot
  letI : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular
      (volume : Measure UnitAddCircle)
  have hneg := Measure.measurePreserving_neg
    (volume : Measure UnitAddCircle)
  have htranslate := measurePreserving_add_left
    (volume : Measure UnitAddCircle) ((1 / 2 : ℝ) : UnitAddCircle)
  have h := htranslate.comp (hneg.comp (hquot'.comp hscale))
  convert h using 1 <;>
    simp only [reproPhysicalBrillouinToCircle, sub_eq_add_neg,
      Function.comp_def, one_div, mul_inv_rev] <;>
    try (funext x; congr 1; ring)

theorem reproMeasurePiConstSmul
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (c : NNReal) (mu : Measure α) [SigmaFinite mu] :
    Measure.pi (fun _ : ι => c • mu) =
      c ^ Fintype.card ι • Measure.pi (fun _ : ι => mu) := by
  apply Measure.pi_eq
  intro s _
  simp [Measure.pi_pi, Measure.smul_apply, ENNReal.smul_def,
    Finset.prod_mul_distrib]

example (I : ℂ) :
    (ENNReal.ofReal ((2 * Real.pi)⁻¹)).toReal ^ 4 • I =
      (((2 * Real.pi) ^ 4)⁻¹ : ℝ) * I := by
  have hc : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  rw [ENNReal.toReal_ofReal hc, inv_pow, Complex.real_smul]

end
