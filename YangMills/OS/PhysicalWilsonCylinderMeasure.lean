import YangMills.OS.PhysicalWilsonCylinder
import YangMills.OS.TwoTransporterHaarProjection
import YangMills.ClayCore.SchurZeroMean

/-!
# The physical two-plaquette Wilson cylinder measure

Six independent normalized Haar links, the literal Wilson density, and its
normalized Gibbs probability. Reflection preserves physical expectations.
The reflected form is rewritten by Fubini while retaining both crossing links.
No reflection positivity or positive centered norm is asserted here.

The short right/inversion Haar bridges adapt the already checked satellite
`SU2CharacterConvolution` / `SU2GlobalEdgeGaugeFixing` arguments at
`a1fbea97cbe673d383dbb4bc5e2a2fb70dbf190a` to the mother's `sunHaarProb`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace YangMills.OS.WilsonCylinder

section ProductReflection

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]

def reflectionEquiv : WilsonCylinder G ≃ᵐ WilsonCylinder G where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_involutive
  right_inv := reflect_involutive
  measurable_toFun :=
    (measurable_fst.snd.prodMk measurable_fst.fst).prodMk
      (measurable_snd.fst.inv.prodMk measurable_snd.snd.inv)
  measurable_invFun :=
    (measurable_fst.snd.prodMk measurable_fst.fst).prodMk
      (measurable_snd.fst.inv.prodMk measurable_snd.snd.inv)

def productMeasure (μ : Measure G) : Measure (WilsonCylinder G) :=
  ((μ.prod μ).prod (μ.prod μ)).prod (μ.prod μ)

theorem reflect_measurePreserving (μ : Measure G) [SFinite μ]
    [Measure.IsInvInvariant μ] :
    MeasurePreserving (reflect (G := G)) (productMeasure μ) (productMeasure μ) := by
  change MeasurePreserving (Prod.map Prod.swap (Prod.map Inv.inv Inv.inv)) _ _
  exact Measure.measurePreserving_swap.prod
    ((Measure.measurePreserving_inv μ).prod (Measure.measurePreserving_inv μ))

end ProductReflection

/-- Matrix coordinates supply the second countability needed by product Borel measures. -/
local instance secondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  exact TopologicalSpace.secondCountableTopology_induced SU2
    (Matrix (Fin 2) (Fin 2) ℂ) (fun U => U.1)

local instance haar : Measure.IsHaarMeasure (sunHaarProb 2) := by
  unfold sunHaarProb
  infer_instance

local instance rightInvariant : Measure.IsMulRightInvariant (sunHaarProb 2) where
  map_mul_right_eq_self g := by
    let ν : Measure SU2 := Measure.map (fun x : SU2 => x * g) (sunHaarProb 2)
    haveI : IsProbabilityMeasure ν := by
      constructor
      change (Measure.map (fun x : SU2 => x * g) (sunHaarProb 2)) Set.univ = 1
      calc
        (Measure.map (fun x : SU2 => x * g) (sunHaarProb 2)) Set.univ =
            (sunHaarProb 2) ((fun x : SU2 => x * g) ⁻¹' Set.univ) :=
          Measure.map_apply_of_aemeasurable
            ((continuous_id.mul continuous_const).measurable.aemeasurable)
            MeasurableSet.univ
        _ = 1 := by simp
    have hν := Measure.isMulInvariant_eq_smul_of_compactSpace ν (sunHaarProb 2)
    have hu := congrArg (fun μ : Measure SU2 => μ Set.univ) hν
    have hc : ν.haarScalarFactor (sunHaarProb 2) = 1 := by
      simpa [ENNReal.smul_def] using hu.symm
    rw [hc] at hν
    have hOne : (1 : ENNReal) • sunHaarProb 2 = sunHaarProb 2 := by
      ext s hs
      simp
    change ν = sunHaarProb 2
    exact hν.trans hOne

local instance invInvariant : Measure.IsInvInvariant (sunHaarProb 2) where
  inv_eq_self := by
    let ν : Measure SU2 := (sunHaarProb 2).inv
    haveI : IsProbabilityMeasure ν := by
      constructor
      change (Measure.map Inv.inv (sunHaarProb 2)) Set.univ = 1
      rw [Measure.map_apply measurable_inv MeasurableSet.univ]
      simp
    have hν := Measure.isMulInvariant_eq_smul_of_compactSpace ν (sunHaarProb 2)
    have hu := congrArg (fun μ : Measure SU2 => μ Set.univ) hν
    have hc : ν.haarScalarFactor (sunHaarProb 2) = 1 := by
      simpa [ENNReal.smul_def] using hu.symm
    rw [hc] at hν
    have hOne : (1 : ENNReal) • sunHaarProb 2 = sunHaarProb 2 := by
      ext s hs
      simp
    exact hν.trans hOne

def sliceHaar : Measure (SU2 × SU2) := (sunHaarProb 2).prod (sunHaarProb 2)

def haarMeasure : Measure (WilsonCylinder SU2) := productMeasure (sunHaarProb 2)

instance sliceHaar_probability : IsProbabilityMeasure sliceHaar := by
  unfold sliceHaar
  infer_instance

instance haarMeasure_probability : IsProbabilityMeasure haarMeasure := by
  unfold haarMeasure productMeasure
  infer_instance

theorem haar_reflect_measurePreserving :
    MeasurePreserving (reflect (G := SU2)) haarMeasure haarMeasure :=
  reflect_measurePreserving (sunHaarProb 2)

def logDensity (β : ℝ) (A : WilsonCylinder SU2) : ℝ :=
  (β / 2) * (Matrix.trace (face0 A).val).re +
    (β / 2) * (Matrix.trace (face1 A).val).re

/-- Wilson plaquette energy with its configuration-independent constant omitted. -/
def plaquetteEnergy (U : SU2) : ℝ := -(Matrix.trace U.val).re / 2

/-- Exact dictionary to the mother's Wilson action on the constructed geometry. -/
theorem logDensity_eq_neg_wilsonAction (β : ℝ) (A : WilsonCylinder SU2) :
    logDensity β A = -β *
      @wilsonAction 2 2 SU2 _ (geometry SU2) plaquetteEnergy (toGaugeConfig A) := by
  have hw : @wilsonAction 2 2 SU2 _ (geometry SU2) plaquetteEnergy (toGaugeConfig A) =
      plaquetteEnergy (face0 A) + plaquetteEnergy (face1 A) := by
    change (∑ p : Fin 2, plaquetteEnergy
      (@GaugeConfig.plaquetteHolonomy 2 2 SU2 _ (geometry SU2) (toGaugeConfig A) p)) = _
    rw [Fin.sum_univ_two, plaquetteHolonomy_zero, plaquetteHolonomy_one]
  rw [hw]
  unfold logDensity plaquetteEnergy
  ring

def density (β : ℝ) (A : WilsonCylinder SU2) : ℝ := Real.exp (logDensity β A)

theorem density_eq_wilson_product (β : ℝ) (A : WilsonCylinder SU2) :
    (density β A : ℂ) =
      TwoTransporterHaarProjection.su2WilsonWeight β (face0 A) *
      TwoTransporterHaarProjection.su2WilsonWeight β (face1 A) := by
  simp [density, logDensity, Real.exp_add,
    TwoTransporterHaarProjection.su2WilsonWeight]

theorem continuous_density (β : ℝ) : Continuous (density β) := by
  have h0 : Continuous (face0 (G := SU2)) := by unfold face0; fun_prop
  have h1 : Continuous (face1 (G := SU2)) := by unfold face1; fun_prop
  exact ((((Complex.continuous_re.comp (continuous_trace_sub 2)).comp h0).const_mul
    (β / 2)).add
    (((Complex.continuous_re.comp (continuous_trace_sub 2)).comp h1).const_mul
      (β / 2))).rexp

theorem density_pos (β : ℝ) (A : WilsonCylinder SU2) : 0 < density β A :=
  Real.exp_pos _

theorem density_integrable (β : ℝ) : Integrable (density β) haarMeasure :=
  (continuous_density β).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem density_reflect (β : ℝ) (A : WilsonCylinder SU2) :
    density β (reflect A) = density β A := by
  have h0 := TwoTransporterHaarProjection.su2WilsonWeight_conjugationInverseInvariant
    β (A.2.1)⁻¹ (face0 A)
  have h1 := TwoTransporterHaarProjection.su2WilsonWeight_conjugationInverseInvariant
    β (A.2.2)⁻¹ (face1 A)
  apply Complex.ofReal_injective
  rw [density_eq_wilson_product, density_eq_wilson_product,
    face0_reflect, face1_reflect]
  simpa only [inv_inv] using congrArg₂ (· * ·) h0 h1

def partition (β : ℝ) : ℝ := ∫ A, density β A ∂haarMeasure

theorem partition_pos (β : ℝ) : 0 < partition β :=
  integral_exp_pos (density_integrable β)

def gibbsMeasure (β : ℝ) : Measure (WilsonCylinder SU2) :=
  haarMeasure.tilted (logDensity β)

instance gibbsMeasure_probability (β : ℝ) : IsProbabilityMeasure (gibbsMeasure β) :=
  isProbabilityMeasure_tilted (density_integrable β)

/-- Continuous physical observables have genuine finite Gibbs expectations. -/
theorem continuous_integrable_gibbs (β : ℝ) (F : WilsonCylinder SU2 → ℂ)
    (hF : Continuous F) : Integrable F (gibbsMeasure β) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_gibbs_eq (β : ℝ) (F : WilsonCylinder SU2 → ℂ) :
    (∫ A, F A ∂gibbsMeasure β) =
      (partition β)⁻¹ • ∫ A, density β A • F A ∂haarMeasure := by
  rw [gibbsMeasure, integral_tilted]
  change (∫ A, (density β A / partition β) • F A ∂haarMeasure) = _
  simp only [Complex.real_smul, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  calc
    _ = ∫ A, ((partition β)⁻¹ : ℂ) * ((density β A : ℂ) * F A) ∂haarMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      ring
    _ = _ := integral_const_mul (μ := haarMeasure) ((partition β)⁻¹ : ℂ)
      (fun A => (density β A : ℂ) * F A)

/-- Reflection identity for the normalized measure. For arbitrary non-integrable
functions this is Mathlib's totalized integral; `continuous_integrable_gibbs`
establishes expectation semantics for continuous physical observables. -/
theorem integral_reflect (β : ℝ) (F : WilsonCylinder SU2 → ℂ) :
    (∫ A, F (reflect A) ∂gibbsMeasure β) = ∫ A, F A ∂gibbsMeasure β := by
  rw [integral_gibbs_eq, integral_gibbs_eq]
  congr 1
  have h := haar_reflect_measurePreserving.integral_comp
    (reflectionEquiv (G := SU2)).measurableEmbedding
    (fun A => density β A • F A)
  simpa only [density_reflect] using h

def reflectedForm (β : ℝ) (f g : SU2 × SU2 → ℂ) : ℂ :=
  ∫ A, star (f A.1.2) * g A.1.1 ∂gibbsMeasure β

/-- Fubini on the six physical links; the same crossing pair occurs in both faces. -/
theorem reflectedForm_eq_productHaar (β : ℝ) (f g : SU2 × SU2 → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    reflectedForm β f g = (partition β)⁻¹ •
      ∫ u, ∫ v, ∫ a, density β ((u, v), a) • (star (f v) * g u)
        ∂sliceHaar ∂sliceHaar ∂sliceHaar := by
  let F : WilsonCylinder SU2 → ℂ :=
    fun A => density β A • (star (f A.1.2) * g A.1.1)
  have hF : Continuous F := by
    change Continuous (fun A => density β A • (star (f A.1.2) * g A.1.1))
    simp only [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp (continuous_density β)).mul
      ((hf.comp continuous_fst.snd).star.mul (hg.comp continuous_fst.fst))
  have hI : Integrable F haarMeasure :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold reflectedForm
  rw [integral_gibbs_eq]
  change (partition β)⁻¹ • (∫ A, F A ∂haarMeasure) = _
  congr 1
  change (∫ A, F A ∂(sliceHaar.prod sliceHaar).prod sliceHaar) = _
  exact (integral_prod F hI).trans (integral_prod _ hI.integral_prod_left)

end YangMills.OS.WilsonCylinder
