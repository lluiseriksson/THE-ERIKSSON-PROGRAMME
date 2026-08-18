/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This scratch file factors the G23.4 measure dictionary through a normalized
one-dimensional physical Brillouin measure.  The normalization is part of
the source measure, so the four-dimensional product cannot lose or duplicate
the `(2*pi)^-4` Jacobian.

No Green value, Fourier coefficient, `B0`, window-15 attainment or terminal
field is asserted here.
-/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import YangMills.RG.BalabanCMP89Eq249NormalizedStabilizedEndpointIntegralBound
import YangMills.RG.BalabanCMP89CenteredTorusFourierPhase

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- One-dimensional source-normalized translated Brillouin measure. -/
def cmp89OneDimensionalNormalizedBrillouinMeasure : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) •
    volume.restrict (Set.Ioc 0 (2 * Real.pi))

/-- Scaling `x in (0,2*pi]` to `x/(2*pi) in (0,1]` transports the normalized
Brillouin measure exactly to the unit fundamental-domain measure. -/
theorem measurePreserving_cmp89NormalizedBrillouinScale :
    MeasurePreserving
      (fun x : ℝ => (2 * Real.pi)⁻¹ * x)
      cmp89OneDimensionalNormalizedBrillouinMeasure
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
  unfold cmp89OneDimensionalNormalizedBrillouinMeasure
  change Measure.map (fun x : ℝ => c⁻¹ * x)
      (ENNReal.ofReal c⁻¹ • volume.restrict (Set.Ioc 0 c)) =
    volume.restrict (Set.Ioc 0 1)
  rw [Measure.map_smul]
  rw [← hpreimage, ← hrestrict']
  rw [hmap, Measure.restrict_smul, smul_smul]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
  simp [hc0]

/-- Physical translated Brillouin coordinate mapped to the centered torus
parameter `t = 1/2 - x/(2*pi)`. -/
def cmp89PhysicalBrillouinToUnitAddCircle (x : ℝ) : UnitAddCircle :=
  (((1 / 2 : ℝ) - (2 * Real.pi)⁻¹ * x : ℝ) : UnitAddCircle)

/-- The normalized physical coordinate maps exactly to Haar measure.  The
proof composes scaling, quotienting, negation and translation; none of those
symmetries is assumed for the physical Green integrand. -/
theorem measurePreserving_cmp89PhysicalBrillouinToUnitAddCircle :
    MeasurePreserving cmp89PhysicalBrillouinToUnitAddCircle
      cmp89OneDimensionalNormalizedBrillouinMeasure
      (volume : Measure UnitAddCircle) := by
  have hscale := measurePreserving_cmp89NormalizedBrillouinScale
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
  simpa [cmp89PhysicalBrillouinToUnitAddCircle, sub_eq_add_neg,
    Function.comp_def, mul_inv_rev] using h

/-- Four-dimensional physical Brillouin coordinate mapped coordinatewise to
the unit torus. -/
def cmp89PhysicalBrillouinToUnitAddTorus
    (x : Fin 4 → ℝ) : UnitAddTorus (Fin 4) :=
  fun mu => cmp89PhysicalBrillouinToUnitAddCircle (x mu)

/-- The negative torus momentum of the normalized physical coordinate is
the repository's literal translated Brillouin parameter. -/
theorem cmp89Eq248NegativeTwoPiTorusMomentum_physicalBrillouin
    (x : Fin 4 → ℝ) :
    cmp89Eq248NegativeTwoPiTorusMomentum
        (fun mu => (1 / 2 : ℝ) - (2 * Real.pi)⁻¹ * x mu) =
      fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ) := by
  funext mu
  unfold cmp89Eq248NegativeTwoPiTorusMomentum
    cmp89Eq251PhysicalBrillouinParameter
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  push_cast
  field_simp [htwoPi]
  ring

/-- A finite product of identically scaled measures carries exactly one
scalar per coordinate.  This is the bookkeeping lemma that prevents the
four-dimensional source normalization from being counted twice. -/
theorem cmp89Measure_pi_const_smul
    {iota α : Type*} [Fintype iota] [MeasurableSpace α]
    (c : NNReal) (mu : Measure α) [SigmaFinite mu] :
    Measure.pi (fun _ : iota => c • mu) =
      c ^ Fintype.card iota • Measure.pi (fun _ : iota => mu) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply _ (MeasurableSet.univ_pi hs),
    Measure.pi_pi]
  simp_rw [Measure.smul_apply _ (hs _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The product of the four normalized one-coordinate measures is literally
the source normalization times the repository's translated Brillouin
measure. -/
theorem cmp89NormalizedBrillouinProductMeasure_eq :
    (Measure.pi fun _ : Fin 4 =>
        cmp89OneDimensionalNormalizedBrillouinMeasure) =
      ENNReal.ofReal ((2 * Real.pi)⁻¹) ^ 4 •
        cmp89Eq249FourDimensionalBrillouinMeasure := by
  unfold cmp89OneDimensionalNormalizedBrillouinMeasure
    cmp89Eq249FourDimensionalBrillouinMeasure
  have htwoPi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hcoeff_nonneg : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  simpa [Set.uIoc_of_le htwoPi_nonneg,
    ENNReal.ofReal_eq_coe_nnreal hcoeff_nonneg] using
    (cmp89Measure_pi_const_smul (iota := Fin 4)
      (⟨(2 * Real.pi)⁻¹, hcoeff_nonneg⟩ : NNReal)
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))))

/-- The fourfold normalized physical Brillouin product measure is sent
exactly to Haar measure on the four-torus. -/
theorem measurePreserving_cmp89PhysicalBrillouinToUnitAddTorus :
    MeasurePreserving cmp89PhysicalBrillouinToUnitAddTorus
      (Measure.pi fun _ : Fin 4 =>
        cmp89OneDimensionalNormalizedBrillouinMeasure)
      (volume : Measure (UnitAddTorus (Fin 4))) := by
  have hpi := MeasureTheory.measurePreserving_pi
    (fun _ : Fin 4 => cmp89OneDimensionalNormalizedBrillouinMeasure)
    (fun _ : Fin 4 => (volume : Measure UnitAddCircle))
    (fun _ : Fin 4 =>
      measurePreserving_cmp89PhysicalBrillouinToUnitAddCircle)
  simpa [cmp89PhysicalBrillouinToUnitAddTorus,
    MeasureTheory.volume_pi] using hpi

/-- Haar integration of a continuous torus function is exactly its literal
source-normalized integral over the repository's translated Brillouin cube.
The four Jacobian factors are supplied by the source measure equality above.
-/
theorem integral_unitAddTorus_eq_cmp89NormalizedBrillouin
    (f : C(UnitAddTorus (Fin 4), ℂ)) :
    (∫ t, f t ∂(volume : Measure (UnitAddTorus (Fin 4)))) =
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => f (cmp89PhysicalBrillouinToUnitAddTorus x)) := by
  let h := measurePreserving_cmp89PhysicalBrillouinToUnitAddTorus
  calc
    (∫ t, f t ∂(volume : Measure (UnitAddTorus (Fin 4)))) =
        ∫ x, f (cmp89PhysicalBrillouinToUnitAddTorus x)
          ∂(Measure.pi fun _ : Fin 4 =>
            cmp89OneDimensionalNormalizedBrillouinMeasure) := by
      rw [← h.map_eq]
      exact MeasureTheory.integral_map h.aemeasurable
        f.continuous.aestronglyMeasurable
    _ = cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
          (fun x => f (cmp89PhysicalBrillouinToUnitAddTorus x)) := by
      rw [cmp89NormalizedBrillouinProductMeasure_eq,
        MeasureTheory.integral_smul_measure]
      unfold cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
      have hc : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
      rw [ENNReal.toReal_ofReal hc, inv_pow, Complex.real_smul]
      norm_cast

end

end YangMills.RG
