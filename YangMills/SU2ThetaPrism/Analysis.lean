import YangMills.SU2ThetaPrism.Witness
import YangMills.P8_PhysicalGap.SUN_Compact

/-!
# Haar conditional identities, norm moments, and explicit Fubini frontier

The Schur and coordinate-change inputs below are technical integration steps.
The three orthogonality headlines and the `3/4` norm are derived from them by
local lemmas; neither headline is a structure field.
-/

noncomputable section

open Complex MeasureTheory TopologicalSpace

namespace YangMills.SU2ThetaPrism

instance thetaMeasurableSpaceMatrix :
    MeasurableSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
  change MeasurableSpace (Fin 2 → Fin 2 → ℂ)
  infer_instance

instance thetaBorelSpaceMatrix :
    BorelSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
  change BorelSpace (Fin 2 → Fin 2 → ℂ)
  infer_instance

instance thetaMeasurableSpaceSU2 : MeasurableSpace SU2 := inferInstance
instance thetaBorelSpaceSU2 : BorelSpace SU2 := inferInstance
instance thetaCompactSpaceSU2 : CompactSpace SU2 :=
  YangMills.instCompactSpaceSUN_concrete 2

noncomputable instance thetaIsTopologicalGroupSU2 : IsTopologicalGroup SU2 where
  continuous_mul :=
    Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))
      (fun p => mul_mem p.1.2 p.2.2)
  continuous_inv :=
    Continuous.subtype_mk (continuous_star.comp continuous_subtype_val)
      (fun M => (M⁻¹).2)

/-- The whole compact group as a positive compact set. -/
def su2PositiveCompacts : PositiveCompacts SU2 where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp [interior_univ]

/-- Concrete normalized Haar measure on SU(2), defined without a lattice
state-space import. -/
def haarSU2 : Measure SU2 :=
  Measure.haarMeasure su2PositiveCompacts

instance haarSU2_isProbability : IsProbabilityMeasure haarSU2 := by
  constructor
  have h := @Measure.haarMeasure_self SU2 _ _ _ _ _ su2PositiveCompacts
  simpa [haarSU2, su2PositiveCompacts] using h

theorem haar_measure_nonzero : haarSU2 (Set.univ : Set SU2) ≠ 0 := by
  simp

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
