/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CorrectedSourcePi4RectangularRadial
import YangMills.RG.BalabanCMP102Eq80JointEvaluationSourceJetBound
import YangMills.RG.BalabanCMP102Eq80JointPotentialSourceJetBound
import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionDerivativeBound
import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionLinearGrowth
import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionSecondDerivative
import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivativeEvaluationJetBound

/-!
# Source-generated second jet of the corrected rectangular potential

The selected CMP102 correction has type `Fine → Coarse`, while the physical
background minimizer has type `Coarse →L Fine`.  This module keeps those
rectangular types literal.  It packages the actual order-zero, order-one,
and order-two correction estimates and consumes them in the generic joint
equation-(80) source-jet theorem.

The conclusion concerns the global rectangular potential (and hence its
radial Hessian).  It does not assert a termwise identity with the separate
connected-domain Faà di Bruno activities.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

section GenericRectangularSlice

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Generic joint smoothness for the rectangular equation-(80) functional.
The older physical specialization has equal fine and coarse spaces; this
version retains the literal `E → F` correction type. -/
theorem contDiff_cmp102Eq80JointPotential_rectangular
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Δπ : E →L[ℝ] E) (J : E)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ ⊤
      (fun p : (F →L[ℝ] E) × E =>
        cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2) := by
  unfold cmp102Eq80GlobalPotential
  have hHD : ContDiff ℝ ⊤
      (fun p : (F →L[ℝ] E) × E => p.1 (D p.2)) :=
    contDiff_fst.clm_apply (hD.comp contDiff_snd)
  have hHD₃ : ContDiff ℝ ⊤
      (fun p : (F →L[ℝ] E) × E => p.1 (D₃ p.2)) :=
    contDiff_fst.clm_apply (hD₃.comp contDiff_snd)
  have hΔHD : ContDiff ℝ ⊤
      (fun p : (F →L[ℝ] E) × E => Δπ (p.1 (D p.2))) :=
    Δπ.contDiff.comp hHD
  exact
    (((hHD₃.inner ℝ contDiff_const).neg.add
      ((contDiff_snd.inner ℝ hΔHD).neg)).add
      (contDiff_const.mul (hHD.inner ℝ hΔHD))).add
      (hV₀.comp (contDiff_snd.sub hHD))

/-- Restricting a smooth joint map to a fixed first-coordinate slice cannot
increase any iterated-derivative norm. -/
theorem norm_iteratedFDeriv_fixedFirstSlice_le
    (Φ : F × E → G) (hΦ : ContDiff ℝ ⊤ Φ)
    (n : ℕ) (H : F) (A : E) :
    ‖iteratedFDeriv ℝ n (fun X => Φ (H, X)) A‖ ≤
      ‖iteratedFDeriv ℝ n Φ (H, A)‖ := by
  let e : E →L[ℝ] F × E := ContinuousLinearMap.inr ℝ F E
  let Φshift : F × E → G := fun p => Φ (p + (H, 0))
  have hshift : ContDiff ℝ ⊤ Φshift :=
    hΦ.comp (contDiff_id.add contDiff_const)
  have hfun : (fun X : E => Φ (H, X)) = Φshift ∘ e := by
    funext X
    simp [Φshift, e]
  rw [hfun, e.iteratedFDeriv_comp_right hshift A le_top]
  rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Φ)
    n (H, 0) (e A)]
  calc
    ‖(iteratedFDeriv ℝ n Φ (e A + (H, 0))).compContinuousLinearMap
        (fun _ => e)‖ ≤
        ‖iteratedFDeriv ℝ n Φ (e A + (H, 0))‖ *
          ∏ _ : Fin n, ‖e‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n Φ (e A + (H, 0))‖ * 1 := by
      gcongr
      exact Finset.prod_le_one
        (fun _ _ => norm_nonneg e)
        (fun _ _ => by
          simpa [e] using
            (ContinuousLinearMap.norm_inr_le_one ℝ F E))
    _ = ‖iteratedFDeriv ℝ n Φ (H, A)‖ := by
      simp [e]

/-- A radius large enough to contain the literal order-zero, order-one, and
order-two jets of a rectangular evaluation `H (D A)`. -/
def cmp102Eq80RectangularOrderTwoJetRadius
    (Hnorm B₀ B₁ B₂ : ℝ) : ℝ :=
  1 + B₀ + 2 * B₁ + B₂ + Hnorm * (B₁ + B₂)

/-- The explicit order-two radius discharges the only positive jet orders
required by the equation-(80) Hessian.  It contains no bound for the
complete potential. -/
theorem cmp102Eq80JointRemainderRadius_orderTwo_of_correctionJets
    (D : E → F) (H : F →L[ℝ] E) (A : E)
    (B₀ B₁ B₂ : ℝ)
    (h₀ : ‖D A‖ ≤ B₀)
    (h₁ : ‖iteratedFDeriv ℝ 1 D A‖ ≤ B₁)
    (h₂ : ‖iteratedFDeriv ℝ 2 D A‖ ≤ B₂)
    (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i ≤ 2) :
    cmp102Eq80JointFieldProjectionJetMajorant i +
        cmp102Eq80JointEvaluationSourceJetMajorant D i (H, A) ≤
      cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂ ^ i := by
  have hB₀ : 0 ≤ B₀ := (norm_nonneg (D A)).trans h₀
  have hB₁ : 0 ≤ B₁ :=
    (norm_nonneg (iteratedFDeriv ℝ 1 D A)).trans h₁
  have hB₂ : 0 ≤ B₂ :=
    (norm_nonneg (iteratedFDeriv ℝ 2 D A)).trans h₂
  have h₁' : ‖fderiv ℝ D A‖ ≤ B₁ := by
    simpa only [norm_iteratedFDeriv_one] using h₁
  have hRone :
      1 ≤ cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂ := by
    unfold cmp102Eq80RectangularOrderTwoJetRadius
    nlinarith [mul_nonneg (norm_nonneg H) (add_nonneg hB₁ hB₂)]
  interval_cases i
  · have heval :
        cmp102Eq80JointEvaluationSourceJetMajorant D 1 (H, A) =
          ‖H‖ * ‖iteratedFDeriv ℝ 1 D A‖ + ‖D A‖ := by
      simp [cmp102Eq80JointEvaluationSourceJetMajorant,
        cmp102Eq80JointOperatorProjectionJetMajorant,
        Finset.sum_range_succ, norm_iteratedFDeriv_zero]
    rw [heval, pow_one]
    simp [cmp102Eq80JointFieldProjectionJetMajorant]
    have hH₁ :
        ‖H‖ * ‖fderiv ℝ D A‖ ≤ ‖H‖ * B₁ :=
      mul_le_mul_of_nonneg_left h₁' (norm_nonneg H)
    unfold cmp102Eq80RectangularOrderTwoJetRadius
    nlinarith [hH₁, h₀,
      mul_nonneg (norm_nonneg H) hB₂]
  · have hR0 :
        0 ≤ cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂ :=
      hRone.trans' zero_le_one
    have hlinear :
        cmp102Eq80JointFieldProjectionJetMajorant 2 +
            cmp102Eq80JointEvaluationSourceJetMajorant D 2 (H, A) ≤
          cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂ := by
      have heval :
          cmp102Eq80JointEvaluationSourceJetMajorant D 2 (H, A) =
            ‖H‖ * ‖iteratedFDeriv ℝ 2 D A‖ +
              2 * ‖iteratedFDeriv ℝ 1 D A‖ := by
        simp [cmp102Eq80JointEvaluationSourceJetMajorant,
          cmp102Eq80JointOperatorProjectionJetMajorant,
          Finset.sum_range_succ]
      rw [heval]
      simp [cmp102Eq80JointFieldProjectionJetMajorant]
      have hH₂ :
          ‖H‖ * ‖iteratedFDeriv ℝ 2 D A‖ ≤ ‖H‖ * B₂ :=
        mul_le_mul_of_nonneg_left h₂ (norm_nonneg H)
      unfold cmp102Eq80RectangularOrderTwoJetRadius
      nlinarith [hH₂, h₁',
        mul_nonneg (norm_nonneg H) hB₁]
    exact hlinear.trans (by nlinarith [hRone])

/-- The order-two field jet of the literal rectangular equation-(80)
potential is generated from the three actual correction jets and the
componentwise `V₀` budget.  No bound for the complete Hessian is assumed. -/
theorem norm_iteratedFDeriv_two_cmp102Eq80GlobalPotential_fixedRectangular_le_sourceJets
    (D D₃ : E → F) (V₀ : E → ℝ)
    (H : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (B₀ B₁ B₂ C : ℝ)
    (h₀ : ‖D A‖ ≤ B₀)
    (h₁ : ‖iteratedFDeriv ℝ 1 D A‖ ≤ B₁)
    (h₂ : ‖iteratedFDeriv ℝ 2 D A‖ ≤ B₂)
    (hC : ∀ i, i ≤ 2 →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner D (H, A))‖ ≤ C) :
    ‖iteratedFDeriv ℝ 2
        (fun X => cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J X) A‖ ≤
      cmp102Eq80JointPotentialSourceJetMajorant
        D D₃ Δπ J 2 (H, A) C
          (cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂) := by
  let Φ : (F →L[ℝ] E) × E → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hΦ : ContDiff ℝ ⊤ Φ :=
    contDiff_cmp102Eq80JointPotential_rectangular
      D D₃ V₀ Δπ J hD hD₃ hV₀
  have hslice :
      ‖iteratedFDeriv ℝ 2
          (fun X => cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J X) A‖ ≤
        ‖iteratedFDeriv ℝ 2 Φ (H, A)‖ := by
    simpa [Φ] using
      norm_iteratedFDeriv_fixedFirstSlice_le Φ hΦ 2 H A
  have hR : ∀ i, 1 ≤ i → i ≤ 2 →
      ‖iteratedFDeriv ℝ i
          (fun q : (F →L[ℝ] E) × E => q.2) (H, A)‖ +
          cmp102Eq80JointEvaluationJetMajorant D i (H, A) ≤
        cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂ ^ i := by
    intro i hi₁ hi₂
    calc
      ‖iteratedFDeriv ℝ i
          (fun q : (F →L[ℝ] E) × E => q.2) (H, A)‖ +
          cmp102Eq80JointEvaluationJetMajorant D i (H, A) ≤
        cmp102Eq80JointFieldProjectionJetMajorant i +
          cmp102Eq80JointEvaluationSourceJetMajorant D i (H, A) :=
        add_le_add
          (norm_iteratedFDeriv_jointFieldProjection_le i hi₁ (H, A))
          (cmp102Eq80JointEvaluationJetMajorant_le_sourceJetMajorant
            D hD i (H, A))
      _ ≤ cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂ ^ i :=
        cmp102Eq80JointRemainderRadius_orderTwo_of_correctionJets
          D H A B₀ B₁ B₂ h₀ h₁ h₂ i hi₁ hi₂
  have hjoint :
      ‖iteratedFDeriv ℝ 2 Φ (H, A)‖ ≤
        cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 2 (H, A) C
            (cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂) := by
    simpa [Φ] using
      norm_iteratedFDeriv_cmp102Eq80JointPotential_le_sourceJetMajorant
        D D₃ V₀ Δπ J hD hD₃ hV₀ 2 (H, A) C
        (cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂)
        hC hR
  exact hslice.trans hjoint

end GenericRectangularSlice

section PhysicalCorrection

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

local instance cmp102RectangularSourceJetCoordCLMNorm :
    Norm (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102RectangularSourceJetCoordCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102RectangularSourceJetCoordCLMNormedSpace :
    NormedSpace ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FineField :=
  FinePhysicalOneCochain d L N' Nc

private abbrev CoarseField :=
  PhysicalGaugeOneCochain d N' Nc

/-- **Physical rectangular Hessian producer.**  The literal CMP102
fixed-point correction supplies its own value, first jet, and second jet to
the global rectangular equation-(80) potential.  The remaining `hC`
assumption mentions only derivatives of the independent remainder
potential `V₀`; it is not a renamed Hessian bound. -/
theorem
    norm_iteratedFDeriv_two_cmp102Eq80GlobalPotential_physicalCorrection_le_sourceJets
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FineField (d := d) (L := L) (N' := N') (Nc := Nc) → ℝ)
    (r z s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (hr : 0 ≤ r) (hz13 : 1 / 3 ≤ z) (hz1 : z < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hshift : ∀ A,
      ‖cmp102PhysicalCochainToAmbientCLM
        (cmp102PhysicalBackgroundShiftCLM
          U ha hP hε hsmall hbudget
          (A, physicalGaugeOneCochainSupEquiv
            (cmp102Eq80PhysicalBackgroundCorrection
              U ha hP hε hsmall hbudget ρ radius
                (fun _ => r) (fun _ => s) S hcontract A)))‖ ≤ r)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hdeviation : ∀ A, ∀ b : PhysicalBond d N',
      ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget
            (A, physicalGaugeOneCochainSupEquiv
              (cmp102Eq80PhysicalBackgroundCorrection
                U ha hP hε hsmall hbudget ρ radius
                  (fun _ => r) (fun _ => s) S hcontract A))))‖ ≤ z)
    (hdev :
      cmp102SourceAmbientRelativeDeviationValueBudget d L r z ≤ s)
    (H : CoarseField (d := d) (N' := N') (Nc := Nc) →L[ℝ]
      FineField (d := d) (L := L) (N' := N') (Nc := Nc))
    (D₃ : FineField (d := d) (L := L) (N' := N') (Nc := Nc) →
      CoarseField (d := d) (N' := N') (Nc := Nc))
    (V₀ : FineField (d := d) (L := L) (N' := N') (Nc := Nc) → ℝ)
    (Δπ : FineField (d := d) (L := L) (N' := N') (Nc := Nc) →L[ℝ]
      FineField (d := d) (L := L) (N' := N') (Nc := Nc))
    (J A : FineField (d := d) (L := L) (N' := N') (Nc := Nc))
    (hD₃ : ContDiff ℝ ⊤ D₃) (hV₀ : ContDiff ℝ ⊤ V₀)
    (C : ℝ)
    (hC : ∀ i, i ≤ 2 →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r) (fun _ => s) S hcontract)
          (H, A))‖ ≤ C) :
    let D :=
      cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract
    let B₀ :=
      cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S A * ‖A‖
    let B₁ :=
      ‖(physicalGaugeOneCochainSupEquiv
          (d := d) (N := N') (Nc := Nc)).symm.toContinuousLinearMap‖ *
        ((cmp102PhysicalCorrectionContractionRate Nc d L r s /
            (1 - ((S 0).toBallData).contractionRate)) *
          ‖(physicalGaugeOneCochainSupEquiv :
            FineField (d := d) (L := L) (N' := N') (Nc := Nc) ≃L[ℝ]
              PhysicalGaugeOneCochainSup d (L * N') Nc
            ).toContinuousLinearMap‖)
    let Lcorr :=
      (cmp102PhysicalCorrectionContractionRate Nc d L r s /
          (1 - ((S 0).toBallData).contractionRate)) *
        ‖(physicalGaugeOneCochainSupEquiv :
          FineField (d := d) (L := L) (N' := N') (Nc := Nc) ≃L[ℝ]
            PhysicalGaugeOneCochainSup d (L * N') Nc
          ).toContinuousLinearMap‖
    let q := ((S 0).toBallData).contractionRate
    let B₂ :=
      ‖(physicalGaugeOneCochainSupEquiv
          (d := d) (N := N') (Nc := Nc)).symm.toContinuousLinearMap‖ *
        cmp102Eq80PhysicalBackgroundCorrectionSecondDerivativeBudget
          U ha hP hε hsmall hbudget r z s Lcorr q
    ‖iteratedFDeriv ℝ 2
        (fun X => cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J X) A‖ ≤
      cmp102Eq80JointPotentialSourceJetMajorant
        D D₃ Δπ J 2 (H, A) C
          (cmp102Eq80RectangularOrderTwoJetRadius ‖H‖ B₀ B₁ B₂) := by
  dsimp only
  let D :=
    cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract
  let B₀ :=
    cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S A * ‖A‖
  let B₁ :=
    ‖(physicalGaugeOneCochainSupEquiv
        (d := d) (N := N') (Nc := Nc)).symm.toContinuousLinearMap‖ *
      ((cmp102PhysicalCorrectionContractionRate Nc d L r s /
          (1 - ((S 0).toBallData).contractionRate)) *
        ‖(physicalGaugeOneCochainSupEquiv :
          FineField (d := d) (L := L) (N' := N') (Nc := Nc) ≃L[ℝ]
            PhysicalGaugeOneCochainSup d (L * N') Nc
          ).toContinuousLinearMap‖)
  let Lcorr :=
    (cmp102PhysicalCorrectionContractionRate Nc d L r s /
        (1 - ((S 0).toBallData).contractionRate)) *
      ‖(physicalGaugeOneCochainSupEquiv :
        FineField (d := d) (L := L) (N' := N') (Nc := Nc) ≃L[ℝ]
          PhysicalGaugeOneCochainSup d (L * N') Nc
        ).toContinuousLinearMap‖
  let q := ((S 0).toBallData).contractionRate
  let B₂ :=
    ‖(physicalGaugeOneCochainSupEquiv
        (d := d) (N := N') (Nc := Nc)).symm.toContinuousLinearMap‖ *
      cmp102Eq80PhysicalBackgroundCorrectionSecondDerivativeBudget
        U ha hP hε hsmall hbudget r z s Lcorr q
  have hD : ContDiff ℝ ⊤ D := by
    simpa [D] using
      contDiff_top_cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract
  have h₀ : ‖D A‖ ≤ B₀ := by
    simpa [D, B₀] using
      norm_cmp102Eq80PhysicalBackgroundCorrection_le
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract A
  have h₁ : ‖iteratedFDeriv ℝ 1 D A‖ ≤ B₁ := by
    simpa [D, B₁] using
      norm_iteratedFDeriv_one_cmp102Eq80PhysicalBackgroundCorrection_le_sourceBudget
        U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract A
  have h₂ : ‖iteratedFDeriv ℝ 2 D A‖ ≤ B₂ := by
    simpa [D, B₂, Lcorr, q] using
      norm_iteratedFDeriv_two_cmp102Eq80PhysicalBackgroundCorrection_le_sourceBudget
        U ha hP hε hsmall hbudget ρ radius r z s S hρ hcontract
        hr hz13 hz1 hs0 hs1 hshift hbase hdeviation hdev A
  exact
    norm_iteratedFDeriv_two_cmp102Eq80GlobalPotential_fixedRectangular_le_sourceJets
      D D₃ V₀ H Δπ J A hD hD₃ hV₀ B₀ B₁ B₂ C h₀ h₁ h₂ hC

end PhysicalCorrection

end

end YangMills.RG
