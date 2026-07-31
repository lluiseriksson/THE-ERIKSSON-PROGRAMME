import YangMills.SU2ThetaPrism.Witness
import YangMills.ClayCore.SchurFundamentalOrthogonality
import Mathlib.MeasureTheory.Group.Prod

/-!
# Haar conditional identities, norm moments, and explicit Fubini frontier

The Schur and coordinate-change inputs below are technical integration steps.
The three orthogonality headlines and the `3/4` norm are derived from them by
local lemmas; neither headline is a structure field.
-/

noncomputable section

open Complex MeasureTheory TopologicalSpace

namespace YangMills.SU2ThetaPrism

/-- Concrete normalized Haar measure on SU(2).  This is definitionally the
repository's normalized `sunHaarProb 2`, so the existing Schur theorems apply
without a uniqueness-of-Haar gap. -/
abbrev haarSU2 : Measure SU2 := YangMills.sunHaarProb 2

/-- Multiplication is measurable in the concrete Borel structure on SU(2). -/
instance thetaMeasurableMulSU2 : MeasurableMul₂ SU2 := by
  refine ⟨Measurable.subtype_mk ?_⟩
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact ((YangMills.ClayCore.continuous_val_entry i k).measurable.comp
    measurable_fst).mul
    ((YangMills.ClayCore.continuous_val_entry k j).measurable.comp measurable_snd)

/-- Inversion is measurable because inverse in SU(2) is conjugate transpose. -/
instance thetaMeasurableInvSU2 : MeasurableInv SU2 := by
  refine ⟨Measurable.subtype_mk ?_⟩
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.star_apply]
  exact continuous_star.measurable.comp
    (YangMills.ClayCore.continuous_val_entry j i).measurable

theorem haar_measure_nonzero : haarSU2 (Set.univ : Set SU2) ≠ 0 := by
  simp

/-! ## The concrete eight-coordinate product measure -/

/-- Coordinate labels for the six branch variables and two transversals. -/
inductive CellSlot where
  | upper : Branch → CellSlot
  | lower : Branch → CellSlot
  | transversalS : CellSlot
  | transversalT : CellSlot
  deriving DecidableEq, Fintype

/-- Assemble a named cell configuration from its eight SU(2) coordinates. -/
def cellConfigurationEquiv : (CellSlot → SU2) ≃ CellConfiguration where
  toFun x :=
    { A := fun i => x (.upper i)
      B := fun i => x (.lower i)
      s := x .transversalS
      t := x .transversalT }
  invFun c
    | .upper i => c.A i
    | .lower i => c.B i
    | .transversalS => c.s
    | .transversalT => c.t
  left_inv x := by
    funext slot
    cases slot <;> rfl
  right_inv c := by
    cases c
    rfl

/-- The Borel product measurable space transported to the named structure. -/
noncomputable instance cellConfigurationMeasurableSpace :
    MeasurableSpace CellConfiguration :=
  MeasurableSpace.comap cellConfigurationEquiv.symm inferInstance

theorem measurable_cellConfigurationEquiv :
    Measurable cellConfigurationEquiv := by
  rw [measurable_iff_comap_le]
  simp only [cellConfigurationMeasurableSpace]
  rw [MeasurableSpace.comap_comp]
  simp [MeasurableSpace.comap_id]

theorem measurable_cellConfigurationEquiv_symm :
    Measurable cellConfigurationEquiv.symm := by
  rw [measurable_iff_comap_le]
  rfl

/-- Normalized product Haar on all eight registered cell coordinates. -/
def cellHaar : Measure CellConfiguration :=
  Measure.map cellConfigurationEquiv
    (Measure.pi fun _ : CellSlot => haarSU2)

instance cellHaar_isProbability : IsProbabilityMeasure cellHaar := by
  unfold cellHaar
  exact Measure.isProbabilityMeasure_map
    measurable_cellConfigurationEquiv.aemeasurable

theorem cellHaar_mass_one : cellHaar (Set.univ : Set CellConfiguration) = 1 := by
  simp

theorem cellHaar_finite : IsFiniteMeasure cellHaar := inferInstance

/-- Every named coordinate has the original normalized Haar marginal. -/
theorem cellHaar_coordinate_marginal (slot : CellSlot) :
    Measure.map (fun c => cellConfigurationEquiv.symm c slot) cellHaar = haarSU2 := by
  rw [cellHaar, Measure.map_map]
  · simpa [Function.comp_def] using
      (Measure.pi_map_eval (μ := fun _ : CellSlot => haarSU2) slot)
  · exact (measurable_pi_apply slot).comp
      measurable_cellConfigurationEquiv_symm
  · exact measurable_cellConfigurationEquiv

/-- The exact missing Schur and translated-coordinate integration steps. -/
structure HaarSchurSteps : Prop where
  character_integrable : Integrable chi haarSU2
  character_mean_zero : (∫ W, chi W ∂haarSU2) = 0
  two_character_integrable : ∀ A₁ A₂ : SU2,
    Integrable (fun W => chi (W * A₁) * chi (W * A₂)) haarSU2
  two_character : ∀ A₁ A₂ : SU2,
    (∫ W, chi (W * A₁) * chi (W * A₂) ∂haarSU2) =
      (1 / 2 : ℂ) * chi (A₂⁻¹ * A₁)
  left_inverse_translate_integrable : ∀ A : SU2,
    Integrable (fun W => chi (A * W⁻¹)) haarSU2
  left_inverse_translate : ∀ A : SU2,
    (∫ W, chi (A * W⁻¹) ∂haarSU2) = ∫ W, chi W ∂haarSU2
  right_translate_integrable : ∀ A : SU2,
    Integrable (fun W => chi (W * A)) haarSU2
  right_translate : ∀ A : SU2,
    (∫ W, chi (W * A) ∂haarSU2) = ∫ W, chi W ∂haarSU2

theorem chi_continuous : Continuous chi :=
  YangMills.continuous_trace_sub 2

theorem chi_integrable_concrete : Integrable chi haarSU2 :=
  YangMills.trace_integrable 2

private theorem chi_mul_expand (W B : SU2) :
    chi (W * B) = ∑ i : Fin 2, ∑ j : Fin 2, W.val i j * B.val j i := by
  simp [chi, Matrix.trace, Matrix.mul_apply]

private theorem star_chi_expand (W : SU2) :
    star (chi W) = ∑ k : Fin 2, star (W.val k k) := by
  simp [chi, Matrix.trace, map_sum]

private def traceConvolutionTerm (B : SU2) (i j k : Fin 2) (W : SU2) : ℂ :=
  (W.val i j * B.val j i) * star (W.val k k)

private theorem traceConvolutionTerm_integrable (B : SU2) (i j k : Fin 2) :
    Integrable (traceConvolutionTerm B i j k) haarSU2 := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (((YangMills.ClayCore.continuous_val_entry i j).mul continuous_const).mul
      ((YangMills.ClayCore.continuous_val_entry k k).star))
  · exact HasCompactSupport.of_compactSpace _

/-- Fundamental trace convolution, reduced entrywise to the Schur theorem
already proved in `SchurFundamentalOrthogonality`. -/
theorem trace_convolution (B : SU2) :
    (∫ W, chi (W * B) * chi W ∂haarSU2) = (1 / 2 : ℂ) * chi B := by
  classical
  have hfun : (fun W : SU2 => chi (W * B) * chi W) =
      fun W => ∑ k : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
        traceConvolutionTerm B i j k W := by
    funext W
    rw [show chi W = star (chi W) from (chi_star_eq W).symm,
      chi_mul_expand, star_chi_expand]
    simp only [Finset.sum_mul, Finset.mul_sum, traceConvolutionTerm]
  rw [hfun]
  have hk (k : Fin 2) : Integrable
      (fun W => ∑ i : Fin 2, ∑ j : Fin 2, traceConvolutionTerm B i j k W)
      haarSU2 :=
    integrable_finset_sum Finset.univ fun i _ =>
      integrable_finset_sum Finset.univ fun j _ =>
        traceConvolutionTerm_integrable B i j k
  calc
    (∫ W, ∑ k : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
        traceConvolutionTerm B i j k W ∂haarSU2) =
        ∑ k : Fin 2, ∫ W, ∑ i : Fin 2, ∑ j : Fin 2,
          traceConvolutionTerm B i j k W ∂haarSU2 :=
      integral_finset_sum Finset.univ fun k _ => hk k
    _ = ∑ k : Fin 2, ∑ i : Fin 2, ∫ W, ∑ j : Fin 2,
          traceConvolutionTerm B i j k W ∂haarSU2 := by
      apply Finset.sum_congr rfl
      intro k _
      exact integral_finset_sum Finset.univ fun i _ =>
        integrable_finset_sum Finset.univ fun j _ =>
          traceConvolutionTerm_integrable B i j k
    _ = ∑ k : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2, ∫ W,
          traceConvolutionTerm B i j k W ∂haarSU2 := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finset_sum Finset.univ fun j _ =>
        traceConvolutionTerm_integrable B i j k
    _ = (1 / 2 : ℂ) * chi B := by
      simp only [traceConvolutionTerm]
      have hterm (i j k : Fin 2) :
          (∫ W, (W.val i j * B.val j i) * star (W.val k k) ∂haarSU2) =
            B.val j i * (if i = k ∧ j = k then (1 : ℂ) / 2 else 0) := by
        rw [show (fun W : SU2 => (W.val i j * B.val j i) * star (W.val k k)) =
            fun W => B.val j i * (W.val i j * star (W.val k k)) by
          funext W
          ring]
        calc
          (∫ W, B.val j i * (W.val i j * star (W.val k k)) ∂haarSU2) =
              B.val j i * ∫ W, W.val i j * star (W.val k k) ∂haarSU2 :=
            integral_const_mul _ _
          _ = B.val j i * (if i = k ∧ j = k then (1 : ℂ) / 2 else 0) := by
            rw [YangMills.ClayCore.sunHaarProb_fundamental_entry_orthogonality]
            norm_num
      simp_rw [hterm]
      simp [chi, Matrix.trace]
      ring

/-- Concrete inhabitant of the Haar/Schur integration interface. -/
def haarSchurConcrete : HaarSchurSteps where
  character_integrable := chi_integrable_concrete
  character_mean_zero := YangMills.sunHaarProb_trace_complex_integral_zero 2 (by norm_num)
  two_character_integrable A₁ A₂ := by
    exact ((chi_continuous.comp (continuous_id.mul continuous_const)).mul
      (chi_continuous.comp (continuous_id.mul continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  two_character A₁ A₂ := by
    let B := A₂⁻¹ * A₁
    let f : SU2 → ℂ := fun X => chi (X * B) * chi X
    have hshift := integral_mul_right_eq_self (μ := haarSU2) f A₂
    have hpoint : (fun W : SU2 => f (W * A₂)) =
        fun W => chi (W * A₁) * chi (W * A₂) := by
      funext W
      simp [f, B, mul_assoc]
    rw [hpoint] at hshift
    simpa [B] using hshift.trans (trace_convolution B)
  left_inverse_translate_integrable A := by
    have hfun : (fun W : SU2 => chi (A * W⁻¹)) =
        fun W => chi (W * A⁻¹) := by
      funext W
      rw [← chi_inv_concrete (A * W⁻¹)]
      simp
    rw [hfun]
    exact chi_integrable_concrete.comp_mul_right A⁻¹
  left_inverse_translate A := by
    have hfun : (fun W : SU2 => chi (A * W⁻¹)) =
        fun W => chi (W * A⁻¹) := by
      funext W
      rw [← chi_inv_concrete (A * W⁻¹)]
      simp
    rw [hfun]
    exact integral_mul_right_eq_self chi A⁻¹
  right_translate_integrable A := chi_integrable_concrete.comp_mul_right A
  right_translate A := integral_mul_right_eq_self chi A

def conditionalU (U : SU2) : ℂ :=
  ∫ V, witness U V ∂haarSU2

def conditionalV (V : SU2) : ℂ :=
  ∫ U, witness U V ∂haarSU2

/-- Fibre with fixed relative coordinate `X = U V⁻¹`, parametrized by
`(U,V)=(XW,W)`. -/
def conditionalRelative (X : SU2) : ℂ :=
  ∫ W, witness (X * W) W ∂haarSU2

theorem conditionalU_zero (steps : HaarSchurSteps) (U : SU2) :
    conditionalU U = 0 := by
  have hchi : Integrable (fun V : SU2 => chi V) haarSU2 :=
    steps.character_integrable
  have hfirst : Integrable (fun V : SU2 => chi U * chi V) haarSU2 :=
    hchi.const_mul (chi U)
  rw [conditionalU]
  simp only [witness]
  rw [integral_sub hfirst
    ((steps.left_inverse_translate_integrable U).const_mul (1 / 2 : ℂ))]
  have hfirstInt : (∫ V, chi U * chi V ∂haarSU2) =
      chi U * ∫ V, chi V ∂haarSU2 := integral_const_mul _ _
  have hsecondInt : (∫ V, (1 / 2 : ℂ) * chi (U * V⁻¹) ∂haarSU2) =
      (1 / 2 : ℂ) * ∫ V, chi (U * V⁻¹) ∂haarSU2 := integral_const_mul _ _
  rw [hfirstInt, hsecondInt, steps.left_inverse_translate,
    steps.character_mean_zero]
  ring

theorem conditionalV_zero (steps : HaarSchurSteps) (V : SU2) :
    conditionalV V = 0 := by
  have hchi : Integrable (fun U : SU2 => chi U) haarSU2 :=
    steps.character_integrable
  have hfirst : Integrable (fun U : SU2 => chi U * chi V) haarSU2 :=
    hchi.mul_const (chi V)
  rw [conditionalV]
  simp only [witness]
  rw [integral_sub hfirst
    ((steps.right_translate_integrable V⁻¹).const_mul (1 / 2 : ℂ))]
  have hfirstInt : (∫ U, chi U * chi V ∂haarSU2) =
      (∫ U, chi U ∂haarSU2) * chi V := integral_mul_const _ _
  have hsecondInt : (∫ U, (1 / 2 : ℂ) * chi (U * V⁻¹) ∂haarSU2) =
      (1 / 2 : ℂ) * ∫ U, chi (U * V⁻¹) ∂haarSU2 := integral_const_mul _ _
  rw [hfirstInt, hsecondInt, steps.right_translate,
    steps.character_mean_zero]
  ring

theorem conditionalRelative_zero (steps : HaarSchurSteps) (X : SU2) :
    conditionalRelative X = 0 := by
  have hfun : (fun W : SU2 => witness (X * W) W) =
      fun W => chi (W * X) * chi (W * 1) - (1 / 2 : ℂ) * chi X := by
    funext W
    rw [witness, chi_mul_comm X W]
    simp
  rw [conditionalRelative, hfun,
    integral_sub (steps.two_character_integrable X 1)
      (integrable_const ((1 / 2 : ℂ) * chi X))]
  rw [steps.two_character]
  simp

/-- Product-Haar pairing with an arbitrary function of `U`. -/
def pairingU (phi : SU2 → ℂ) : ℂ :=
  ∫ p : SU2 × SU2,
    witness p.1 p.2 * star (phi p.1) ∂(haarSU2.prod haarSU2)

/-- Product-Haar pairing with an arbitrary function of `V`. -/
def pairingV (phi : SU2 → ℂ) : ℂ :=
  ∫ p : SU2 × SU2,
    witness p.1 p.2 * star (phi p.2) ∂(haarSU2.prod haarSU2)

/-- Product-Haar pairing with an arbitrary function of `U V⁻¹`. -/
def pairingRelative (phi : SU2 → ℂ) : ℂ :=
  ∫ p : SU2 × SU2,
    witness p.1 p.2 * star (phi (p.1 * p.2⁻¹)) ∂(haarSU2.prod haarSU2)

def UPairingIntegrable (phi : SU2 → ℂ) : Prop :=
  Integrable (fun p : SU2 × SU2 => witness p.1 p.2 * star (phi p.1))
    (haarSU2.prod haarSU2)

def VPairingIntegrable (phi : SU2 → ℂ) : Prop :=
  Integrable (fun p : SU2 × SU2 => witness p.1 p.2 * star (phi p.2))
    (haarSU2.prod haarSU2)

def RelativePairingIntegrable (phi : SU2 → ℂ) : Prop :=
  Integrable (fun p : SU2 × SU2 =>
    witness p.1 p.2 * star (phi (p.1 * p.2⁻¹))) (haarSU2.prod haarSU2)

/-- The missing Fubini and measure-preserving coordinate changes.  Each field
is an exchange identity, never an orthogonality conclusion. -/
structure FubiniCoordinateSteps : Prop where
  u_exchange : ∀ (phi : SU2 → ℂ), UPairingIntegrable phi →
    pairingU phi = ∫ U, conditionalU U * star (phi U) ∂haarSU2
  v_exchange : ∀ (phi : SU2 → ℂ), VPairingIntegrable phi →
    pairingV phi = ∫ V, conditionalV V * star (phi V) ∂haarSU2
  relative_coordinate_exchange : ∀ (phi : SU2 → ℂ), RelativePairingIntegrable phi →
    pairingRelative phi = ∫ X, conditionalRelative X * star (phi X) ∂haarSU2

/-- The Haar coordinate change `(X,W) ↦ (XW,W)`.  Its inverse is
`(U,V) ↦ (UV⁻¹,V)`.  This is deliberately separate from ordinary Fubini. -/
def relativeCoordinateEquiv : (SU2 × SU2) ≃ᵐ (SU2 × SU2) where
  toFun p := (p.1 * p.2, p.2)
  invFun p := (p.1 / p.2, p.2)
  left_inv p := by simp [div_eq_mul_inv]
  right_inv p := by simp [div_eq_mul_inv]
  measurable_toFun :=
    (measurable_fst.mul measurable_snd).prodMk measurable_snd
  measurable_invFun :=
    (measurable_fst.div measurable_snd).prodMk measurable_snd

@[simp] theorem relativeCoordinateEquiv_apply (p : SU2 × SU2) :
    relativeCoordinateEquiv p = (p.1 * p.2, p.2) := rfl

/-- Product Haar is invariant under the explicit relative-coordinate change. -/
theorem relativeCoordinateEquiv_measurePreserving :
    MeasurePreserving relativeCoordinateEquiv
      (haarSU2.prod haarSU2) (haarSU2.prod haarSU2) := by
  simpa [relativeCoordinateEquiv] using
    (measurePreserving_mul_prod (μ := haarSU2) (ν := haarSU2))

/-- Concrete Fubini exchanges.  The first two fields are ordinary Fubini
consequences of the supplied integrability.  The third additionally invokes
the separately proved Haar-invariant coordinate change above. -/
def fubiniCoordinatesConcrete : FubiniCoordinateSteps where
  u_exchange phi hphi := by
    rw [pairingU, integral_prod _ hphi]
    change (∫ U, ∫ V, witness U V * star (phi U) ∂haarSU2 ∂haarSU2) = _
    apply integral_congr_ae
    exact ae_of_all _ fun U => by
      change (∫ V, witness U V * star (phi U) ∂haarSU2) =
        (∫ V, witness U V ∂haarSU2) * star (phi U)
      exact integral_mul_const _ _
  v_exchange phi hphi := by
    rw [pairingV, integral_prod_symm _ hphi]
    change (∫ V, ∫ U, witness U V * star (phi V) ∂haarSU2 ∂haarSU2) = _
    apply integral_congr_ae
    exact ae_of_all _ fun V => by
      change (∫ U, witness U V * star (phi V) ∂haarSU2) =
        (∫ U, witness U V ∂haarSU2) * star (phi V)
      exact integral_mul_const _ _
  relative_coordinate_exchange phi hphi := by
    let f : SU2 × SU2 → ℂ := fun p =>
      witness p.1 p.2 * star (phi (p.1 * p.2⁻¹))
    let e := relativeCoordinateEquiv
    have hmp : MeasurePreserving e (haarSU2.prod haarSU2)
        (haarSU2.prod haarSU2) := relativeCoordinateEquiv_measurePreserving
    have hf : Integrable f (haarSU2.prod haarSU2) := hphi
    have hfMap : Integrable f (Measure.map e (haarSU2.prod haarSU2)) := by
      rwa [hmp.map_eq]
    have hcomp : Integrable (f ∘ e) (haarSU2.prod haarSU2) :=
      hfMap.comp_measurable e.measurable
    calc
      pairingRelative phi = ∫ p, f p ∂(haarSU2.prod haarSU2) := rfl
      _ = ∫ p, f (e p) ∂(haarSU2.prod haarSU2) :=
        (hmp.integral_comp' f).symm
      _ = ∫ X, ∫ W, f (e (X, W)) ∂haarSU2 ∂haarSU2 :=
        integral_prod _ hcomp
      _ = ∫ X, conditionalRelative X * star (phi X) ∂haarSU2 := by
        apply integral_congr_ae
        exact ae_of_all _ fun X => by
          simp only [e, relativeCoordinateEquiv_apply, f, Prod.fst, Prod.snd]
          simp only [mul_inv_cancel_right]
          change (∫ W, witness (X * W) W * star (phi X) ∂haarSU2) =
            (∫ W, witness (X * W) W ∂haarSU2) * star (phi X)
          exact integral_mul_const _ _

def CompleteUOrthogonality : Prop :=
  ∀ phi, UPairingIntegrable phi → pairingU phi = 0

def CompleteVOrthogonality : Prop :=
  ∀ phi, VPairingIntegrable phi → pairingV phi = 0

def CompleteRelativeOrthogonality : Prop :=
  ∀ phi, RelativePairingIntegrable phi → pairingRelative phi = 0

theorem complete_U_orthogonality (haar : HaarSchurSteps)
    (fubini : FubiniCoordinateSteps) : CompleteUOrthogonality := by
  intro phi hphi
  rw [fubini.u_exchange phi hphi]
  simp [conditionalU_zero haar]

theorem complete_V_orthogonality (haar : HaarSchurSteps)
    (fubini : FubiniCoordinateSteps) : CompleteVOrthogonality := by
  intro phi hphi
  rw [fubini.v_exchange phi hphi]
  simp [conditionalV_zero haar]

theorem complete_relative_orthogonality (haar : HaarSchurSteps)
    (fubini : FubiniCoordinateSteps) : CompleteRelativeOrthogonality := by
  intro phi hphi
  rw [fubini.relative_coordinate_exchange phi hphi]
  simp [conditionalRelative_zero haar]

private def productCharacter (p : SU2 × SU2) : ℂ :=
  chi p.1 * chi p.2

private def relativeCharacter (p : SU2 × SU2) : ℂ :=
  chi (p.1 * p.2⁻¹)

/-- Concrete product-Haar squared norm of the witness. -/
def witnessNormSq : ℂ :=
  ∫ p : SU2 × SU2, witness p.1 p.2 * star (witness p.1 p.2)
    ∂(haarSU2.prod haarSU2)

/-- Technical Schur moments and their integrability.  No field mentions the
witness norm or its target value. -/
structure NormMomentSteps : Prop where
  product_integrable : Integrable (fun p : SU2 × SU2 =>
    productCharacter p * star (productCharacter p)) (haarSU2.prod haarSU2)
  cross_forward_integrable : Integrable (fun p : SU2 × SU2 =>
    productCharacter p * star (relativeCharacter p)) (haarSU2.prod haarSU2)
  cross_reverse_integrable : Integrable (fun p : SU2 × SU2 =>
    relativeCharacter p * star (productCharacter p)) (haarSU2.prod haarSU2)
  relative_integrable : Integrable (fun p : SU2 × SU2 =>
    relativeCharacter p * star (relativeCharacter p)) (haarSU2.prod haarSU2)
  product_moment : (∫ p : SU2 × SU2,
    productCharacter p * star (productCharacter p) ∂(haarSU2.prod haarSU2)) = 1
  cross_forward_moment : (∫ p : SU2 × SU2,
    productCharacter p * star (relativeCharacter p) ∂(haarSU2.prod haarSU2)) = 1 / 2
  cross_reverse_moment : (∫ p : SU2 × SU2,
    relativeCharacter p * star (productCharacter p) ∂(haarSU2.prod haarSU2)) = 1 / 2
  relative_moment : (∫ p : SU2 × SU2,
    relativeCharacter p * star (relativeCharacter p) ∂(haarSU2.prod haarSU2)) = 1

private theorem witness_norm_integrand_expand (p : SU2 × SU2) :
    witness p.1 p.2 * star (witness p.1 p.2) =
      productCharacter p * star (productCharacter p) -
      (1 / 2 : ℂ) * (productCharacter p * star (relativeCharacter p)) -
      (1 / 2 : ℂ) * (relativeCharacter p * star (productCharacter p)) +
      (1 / 4 : ℂ) * (relativeCharacter p * star (relativeCharacter p)) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    change (starRingEnd ℂ) ((1 : ℂ) / 2) = 1 / 2
    simp only [map_div₀, map_one, map_ofNat]
  have hstar :
      star (productCharacter p - (1 / 2 : ℂ) * relativeCharacter p) =
        (starRingEnd ℂ) (productCharacter p) -
          (1 / 2 : ℂ) * (starRingEnd ℂ) (relativeCharacter p) := by
    change (starRingEnd ℂ)
      (productCharacter p - (1 / 2 : ℂ) * relativeCharacter p) = _
    rw [map_sub, map_mul, hhalf]
  change
    (productCharacter p - (1 / 2 : ℂ) * relativeCharacter p) *
        star (productCharacter p - (1 / 2 : ℂ) * relativeCharacter p) = _
  rw [hstar]
  change
    (productCharacter p - (1 / 2 : ℂ) * relativeCharacter p) *
        ((starRingEnd ℂ) (productCharacter p) -
          (1 / 2 : ℂ) * (starRingEnd ℂ) (relativeCharacter p)) =
      productCharacter p * (starRingEnd ℂ) (productCharacter p) -
      (1 / 2 : ℂ) *
        (productCharacter p * (starRingEnd ℂ) (relativeCharacter p)) -
      (1 / 2 : ℂ) *
        (relativeCharacter p * (starRingEnd ℂ) (productCharacter p)) +
      (1 / 4 : ℂ) *
        (relativeCharacter p * (starRingEnd ℂ) (relativeCharacter p))
  ring

/-- Exact `3/4`, derived by expanding the concrete witness and consuming four
Schur moments. -/
theorem witnessNormSq_eq_three_quarters (moments : NormMomentSteps) :
    witnessNormSq = 3 / 4 := by
  rw [witnessNormSq]
  apply Eq.trans (integral_congr_ae (ae_of_all _ witness_norm_integrand_expand))
  let f0 : SU2 × SU2 → ℂ := fun p =>
    productCharacter p * star (productCharacter p)
  let f1 : SU2 × SU2 → ℂ := fun p =>
    (1 / 2 : ℂ) * (productCharacter p * star (relativeCharacter p))
  let f2 : SU2 × SU2 → ℂ := fun p =>
    (1 / 2 : ℂ) * (relativeCharacter p * star (productCharacter p))
  let f3 : SU2 × SU2 → ℂ := fun p =>
    (1 / 4 : ℂ) * (relativeCharacter p * star (relativeCharacter p))
  change (∫ p, (f0 - f1 - f2 + f3) p ∂(haarSU2.prod haarSU2)) = 3 / 4
  have hi0 : Integrable f0 (haarSU2.prod haarSU2) := moments.product_integrable
  have hi1 : Integrable f1 (haarSU2.prod haarSU2) :=
    moments.cross_forward_integrable.const_mul (1 / 2 : ℂ)
  have hi2 : Integrable f2 (haarSU2.prod haarSU2) :=
    moments.cross_reverse_integrable.const_mul (1 / 2 : ℂ)
  have hi3 : Integrable f3 (haarSU2.prod haarSU2) :=
    moments.relative_integrable.const_mul (1 / 4 : ℂ)
  have hi01 := hi0.sub hi1
  have hi012 := hi01.sub hi2
  change (∫ p, (f0 - f1 - f2) p + f3 p ∂(haarSU2.prod haarSU2)) = 3 / 4
  rw [integral_add hi012 hi3]
  change (∫ p, (f0 - f1) p - f2 p ∂(haarSU2.prod haarSU2)) +
    (∫ p, f3 p ∂(haarSU2.prod haarSU2)) = 3 / 4
  rw [integral_sub hi01 hi2]
  change ((∫ p, f0 p - f1 p ∂(haarSU2.prod haarSU2)) -
    (∫ p, f2 p ∂(haarSU2.prod haarSU2))) +
    (∫ p, f3 p ∂(haarSU2.prod haarSU2)) = 3 / 4
  rw [integral_sub hi0 hi1]
  simp only [f0, f1, f2, f3]
  have hf1Int : (∫ p : SU2 × SU2,
      (1 / 2 : ℂ) * (productCharacter p * star (relativeCharacter p))
        ∂(haarSU2.prod haarSU2)) =
      (1 / 2 : ℂ) * ∫ p,
        productCharacter p * star (relativeCharacter p)
          ∂(haarSU2.prod haarSU2) := integral_const_mul _ _
  have hf2Int : (∫ p : SU2 × SU2,
      (1 / 2 : ℂ) * (relativeCharacter p * star (productCharacter p))
        ∂(haarSU2.prod haarSU2)) =
      (1 / 2 : ℂ) * ∫ p,
        relativeCharacter p * star (productCharacter p)
          ∂(haarSU2.prod haarSU2) := integral_const_mul _ _
  have hf3Int : (∫ p : SU2 × SU2,
      (1 / 4 : ℂ) * (relativeCharacter p * star (relativeCharacter p))
        ∂(haarSU2.prod haarSU2)) =
      (1 / 4 : ℂ) * ∫ p,
        relativeCharacter p * star (relativeCharacter p)
          ∂(haarSU2.prod haarSU2) := integral_const_mul _ _
  rw [hf1Int, hf2Int, hf3Int, moments.product_moment,
    moments.cross_forward_moment,
    moments.cross_reverse_moment, moments.relative_moment]
  norm_num

variable [MeasurableSpace CellConfiguration]

/-- Measurability is the only loaded step needed to turn the concrete pointwise
weight bound into integrability against any finite measure. -/
structure WeightMeasurabilityStep (mu : Measure CellConfiguration)
    (beta : ℝ) : Prop where
  measurable : AEStronglyMeasurable (cellWeight beta) mu

theorem cellWeight_integrable {mu : Measure CellConfiguration} [IsFiniteMeasure mu]
    (bound : CharacterBoundCertificate) (beta : ℝ)
    (meas : WeightMeasurabilityStep mu beta) : Integrable (cellWeight beta) mu := by
  refine (integrable_const (Real.exp (3 * |beta|))).mono' meas.measurable ?_
  exact ae_of_all _ fun c => by
    rw [Real.norm_eq_abs, abs_of_nonneg (cellWeight_nonnegative beta c)]
    exact cellWeight_le_exp_three_abs bound beta c

end YangMills.SU2ThetaPrism
