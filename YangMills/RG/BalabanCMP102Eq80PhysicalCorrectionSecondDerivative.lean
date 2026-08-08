/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicFixedPointSourceDerivative
import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionRegularity
import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionLipschitz
import YangMills.RG.QuantitativeFixedPointDerivativeStability

/-!
# Source-generated second derivative of the physical CMP102 correction

The selected CMP102 correction is a smooth fixed point of the literal
certificate-free intrinsic map.  The source estimates already control the
variation of the full derivative of that map.  Combining those two facts
with the physical vertical contraction produces an explicit second-
derivative bound for the selected correction.

No bound for a second derivative of the fixed point is assumed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

local instance cmp102SecondDerivativeCoordCLMNorm :
    Norm (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102SecondDerivativeCoordCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102SecondDerivativeCoordCLMNormedSpace :
    NormedSpace ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toNormedSpace

/-- The explicit second-derivative budget obtained by differentiating the
physical fixed-point equation. -/
noncomputable def cmp102Eq80PhysicalBackgroundCorrectionSecondDerivativeBudget
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (r z s Lcorr q : ℝ) : ℝ :=
  cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
      U ha hP hε hsmall hbudget r z s *
    (max 1 Lcorr) ^ 2 / (1 - q)

/-- **Source second-jet producer.**  Uniform source-domain conditions along
the selected physical fixed-point graph imply a quantitative bound for its
actual second Fréchet derivative.  The only analytic constant is generated
by the literal contour, logarithm, exponential, and physical shift budgets.
-/
theorem
    norm_iteratedFDeriv_two_cmp102Eq80PhysicalBackgroundCorrection_sup_le_sourceBudget
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
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
    (A : FinePhysicalOneCochain d L N' Nc) :
    let Lcorr :=
      (cmp102PhysicalCorrectionContractionRate Nc d L r s /
          (1 - ((S 0).toBallData).contractionRate)) *
        ‖(physicalGaugeOneCochainSupEquiv :
          FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
            PhysicalGaugeOneCochainSup d (L * N') Nc
          ).toContinuousLinearMap‖
    let q := ((S 0).toBallData).contractionRate
    ‖iteratedFDeriv ℝ 2
        (fun X =>
          physicalGaugeOneCochainSupEquiv
            (cmp102Eq80PhysicalBackgroundCorrection
              U ha hP hε hsmall hbudget ρ radius
                (fun _ => r) (fun _ => s) S hcontract X))
        A‖ ≤
      cmp102Eq80PhysicalBackgroundCorrectionSecondDerivativeBudget
        U ha hP hε hsmall hbudget r z s Lcorr q := by
  dsimp only
  let g := fun X : FinePhysicalOneCochain d L N' Nc =>
    physicalGaugeOneCochainSupEquiv
      (cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract X)
  let T :=
    cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
      U ha hP hε hsmall hbudget
  let Lcorr :=
    (cmp102PhysicalCorrectionContractionRate Nc d L r s /
        (1 - ((S 0).toBallData).contractionRate)) *
      ‖(physicalGaugeOneCochainSupEquiv :
        FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
          PhysicalGaugeOneCochainSup d (L * N') Nc
        ).toContinuousLinearMap‖
  let q := ((S 0).toBallData).contractionRate
  let B :=
    cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
      U ha hP hε hsmall hbudget r z s
  have hL0 : 0 ≤ Lcorr := by
    unfold Lcorr
    exact mul_nonneg
      (div_nonneg
        (cmp102PhysicalCorrectionContractionRate_nonneg
          r s (S 0).r_nonneg (S 0).s_nonneg)
        (sub_nonneg.mpr (hcontract 0).le))
      (norm_nonneg _)
  have hB0 : 0 ≤ B := by
    unfold B
      cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
    exact mul_nonneg
      (by
        unfold cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
        exact mul_nonneg
          (mul_nonneg (norm_nonneg _)
            (cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget_nonneg
              hr ((by norm_num : (0 : ℝ) ≤ 1 / 3).trans hz13) hs0))
          (sq_nonneg _))
      (sq_nonneg _)
  have hq1 : q < 1 := by
    exact hcontract 0
  have hfix : g = fun y => T (y, g y) := by
    funext y
    simpa [g, T,
      cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry] using
      (cmp102Eq80PhysicalBackgroundCorrection_intrinsicEquation
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract y).symm
  have hg : ContDiff ℝ 2 g := by
    simpa [g] using
      (contDiff_cmp102Eq80PhysicalBackgroundCorrection_sup
        U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract)
  have hglip : LipschitzOnWith ⟨Lcorr, hL0⟩ g Set.univ := by
    have hall :
        LipschitzWith ⟨Lcorr, hL0⟩ g := by
      simpa [g, Lcorr, q] using
        (lipschitzWith_cmp102Eq80PhysicalBackgroundCorrection_sup
          U ha hP hε hsmall hbudget ρ radius r s S hcontract)
    exact hall.lipschitzOnWith
  have hlocal : ∀ y, ∀ b : PhysicalBond d N',
      ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget (y, g y)))‖ < 1 := by
    intro y b x hx
    exact (hdeviation y b x hx).trans_lt hz1
  have hrelative : ∀ y, ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM
              (cmp102PhysicalBackgroundShiftCLM
                U ha hP hε hsmall hbudget (y, g y))) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1 := by
    intro y b
    exact ((norm_cmp102AmbientRelativeDeviation_le_sourceBudget
      U b
      (cmp102PhysicalCochainToAmbientCLM
        (cmp102PhysicalBackgroundShiftCLM
          U ha hP hε hsmall hbudget (y, g y)))
      hr hz13 hz1 (by simpa [g] using hshift y)
      (hbase b) (by simpa [g] using hdeviation y b)
    ).trans hdev).trans_lt hs1
  have hT : ∀ y ∈ (Set.univ :
      Set (FinePhysicalOneCochain d L N' Nc)),
      DifferentiableAt ℝ T (y, g y) := by
    intro y _
    exact
      (contDiffAt_cmp102IntrinsicPhysicalBackgroundCorrectionMap_uncurry
        U ha hP hε hsmall hbudget y (g y)
          (hlocal y) (hrelative y)).differentiableAt (by decide)
  have hjoint : ∀ y ∈ (Set.univ :
      Set (FinePhysicalOneCochain d L N' Nc)), ∀ z' ∈ Set.univ,
      ‖fderiv ℝ T (y, g y) - fderiv ℝ T (z', g z')‖ ≤
        B * dist (y, g y) (z', g z') := by
    intro y _ z' _
    rw [dist_eq_norm]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB0 (norm_nonneg _))
    intro R
    simpa [T, g, norm_smul] using
      (norm_fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_sub_apply_le_sourceBudget
        U ha hP hε hsmall hbudget
        (y, g y) (z', g z') R
        hr hz13 hz1 hs0 hs1
        (by simpa [g] using hshift y)
        (by simpa [g] using hshift z')
        hbase
        (by simpa [g] using hdeviation y)
        (by simpa [g] using hdeviation z')
        hdev)
  have hvertical : ∀ y ∈ (Set.univ :
      Set (FinePhysicalOneCochain d L N' Nc)),
      ‖(fderiv ℝ T (y, g y)).comp
          (ContinuousLinearMap.inr ℝ
            (FinePhysicalOneCochain d L N' Nc)
            (PhysicalGaugeOneCochainSup d N' Nc))‖ ≤ q := by
    intro y _
    have hmem : ‖g y‖ ≤ ρ y := by
      simpa [g, norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm] using
        (cmp102Eq80PhysicalBackgroundCorrection_mem_ball
          U ha hP hε hsmall hbudget ρ radius
            (fun _ => r) (fun _ => s) S hcontract y)
    have hv :=
      norm_cmp102IntrinsicPhysicalBackgroundCorrectionMap_verticalFDeriv_le
        U ha hP hε hsmall hbudget y (ρ y) r s
        (S y).toBallData (hρ y) (g y) hmem
        (hlocal y) (hrelative y)
    simpa [T, q] using hv
  have hmain :=
    norm_iteratedFDeriv_two_fixedPoint_le
      T g Set.univ isOpen_univ A (Set.mem_univ A)
      hL0 hB0 hq1 hfix hg hT hglip hjoint hvertical
  simpa [g, B, Lcorr, q,
    cmp102Eq80PhysicalBackgroundCorrectionSecondDerivativeBudget] using hmain

/-- **Ambient second-jet producer.**  Transporting the source-generated
sup-norm estimate back through the inverse physical coordinate equivalence
gives the actual second derivative of the stored coarse cochain.  The only
cost is the explicit finite-dimensional norm of that inverse equivalence;
no second-derivative premise is introduced. -/
theorem
    norm_iteratedFDeriv_two_cmp102Eq80PhysicalBackgroundCorrection_le_sourceBudget
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
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
    (A : FinePhysicalOneCochain d L N' Nc) :
    let Lcorr :=
      (cmp102PhysicalCorrectionContractionRate Nc d L r s /
          (1 - ((S 0).toBallData).contractionRate)) *
        ‖(physicalGaugeOneCochainSupEquiv :
          FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
            PhysicalGaugeOneCochainSup d (L * N') Nc
          ).toContinuousLinearMap‖
    let q := ((S 0).toBallData).contractionRate
    ‖iteratedFDeriv ℝ 2
        (cmp102Eq80PhysicalBackgroundCorrection
          U ha hP hε hsmall hbudget ρ radius
            (fun _ => r) (fun _ => s) S hcontract)
        A‖ ≤
      ‖(physicalGaugeOneCochainSupEquiv
          (d := d) (N := N') (Nc := Nc)).symm.toContinuousLinearMap‖ *
        cmp102Eq80PhysicalBackgroundCorrectionSecondDerivativeBudget
          U ha hP hε hsmall hbudget r z s Lcorr q := by
  dsimp only
  let g := fun X : FinePhysicalOneCochain d L N' Nc =>
    physicalGaugeOneCochainSupEquiv
      (cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract X)
  let inv :=
    (physicalGaugeOneCochainSupEquiv
      (d := d) (N := N') (Nc := Nc)).symm.toContinuousLinearMap
  have hg : ContDiffAt ℝ 2 g A := by
    exact
      (contDiff_cmp102Eq80PhysicalBackgroundCorrection_sup
        U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract).contDiffAt
  have hcomp :
      ‖iteratedFDeriv ℝ 2 (inv ∘ g) A‖ ≤
        ‖inv‖ * ‖iteratedFDeriv ℝ 2 g A‖ :=
    inv.norm_iteratedFDeriv_comp_left hg le_rfl
  have hsup :=
    norm_iteratedFDeriv_two_cmp102Eq80PhysicalBackgroundCorrection_sup_le_sourceBudget
      U ha hP hε hsmall hbudget ρ radius r z s S hρ hcontract
      hr hz13 hz1 hs0 hs1 hshift hbase hdeviation hdev A
  have hfun :
      cmp102Eq80PhysicalBackgroundCorrection
          U ha hP hε hsmall hbudget ρ radius
            (fun _ => r) (fun _ => s) S hcontract =
        inv ∘ g := by
    funext X
    simp [inv, g]
  rw [hfun]
  exact hcomp.trans
    (mul_le_mul_of_nonneg_left hsup (norm_nonneg inv))

end

end YangMills.RG
