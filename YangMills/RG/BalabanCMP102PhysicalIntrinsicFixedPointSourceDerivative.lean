/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicCorrectionSupDerivative
import YangMills.RG.BalabanCMP102PhysicalIntrinsicFixedPointSmooth

/-!
# Source derivative budget for the intrinsic CMP102 fixed-point map

The certificate-free fixed-point map depends on `(A,D)` only through the
literal physical shift `(A,D) ↦ A - H D`.  This file composes the
volume-uniform derivative budget of the intrinsic correction with that
shift.  The resulting constant uses the actual operator norm of the
canonical shift twice; no caller-supplied comparison constant is exposed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

local instance cmp102FixedPointSourceCoordCLMNorm :
    Norm (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102FixedPointSourceCoordCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102FixedPointSourceCoordCLMNormedSpace :
    NormedSpace ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toNormedSpace

/-- Uncurried certificate-free physical fixed-point map. -/
noncomputable def cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (p : FinePhysicalOneCochain d L N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc) :
    PhysicalGaugeOneCochainSup d N' Nc :=
  cmp102IntrinsicPhysicalBackgroundCorrectionMap
    U ha hP hε hsmall hbudget p.1 p.2

@[simp] theorem cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_eq
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (p : FinePhysicalOneCochain d L N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc) :
    cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
        U ha hP hε hsmall hbudget p =
      cmp102IntrinsicPhysicalNonlinearCorrectionSup U
        (cmp102PhysicalBackgroundShiftCLM
          U ha hP hε hsmall hbudget p) := by
  rfl

/-- Exact chain rule through the literal physical shift. -/
theorem fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_apply
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (p R : FinePhysicalOneCochain d L N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc)
    (hlocal : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget p))‖ < 1)
    (hrelative : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM
              (cmp102PhysicalBackgroundShiftCLM
                U ha hP hε hsmall hbudget p)) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1) :
    fderiv ℝ
        (cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
          U ha hP hε hsmall hbudget) p R =
      fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U)
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget p)
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget R) := by
  let shift :=
    cmp102PhysicalBackgroundShiftCLM
      U ha hP hε hsmall hbudget
  have hC :
      DifferentiableAt ℝ
        (cmp102IntrinsicPhysicalNonlinearCorrectionSup U)
        (shift p) := by
    unfold cmp102IntrinsicPhysicalNonlinearCorrectionSup
    have hin :
        DifferentiableAt ℝ
          (cmp102IntrinsicPhysicalNonlinearCorrection U) (shift p) :=
      (contDiffAt_cmp102IntrinsicPhysicalNonlinearCorrection
        U (shift p) hlocal hrelative).differentiableAt (by simp)
    exact
      physicalGaugeOneCochainSupEquiv.toContinuousLinearMap.differentiableAt.comp
        (shift p) hin
  have hcomp := hC.hasFDerivAt.comp p shift.hasFDerivAt
  have happ := congrArg (fun T => T R) hcomp.fderiv
  simpa [cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry,
    cmp102IntrinsicPhysicalBackgroundCorrectionMap,
    cmp102IntrinsicPhysicalNonlinearCorrectionSup, shift,
    ContinuousLinearMap.comp_apply] using happ

/-- The generated joint derivative-Lipschitz budget.  The square is the
two exact uses of the physical shift: once for the base-point difference
and once for the derivative direction. -/
noncomputable def
    cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (r q s : ℝ) : ℝ :=
  cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
      d L N' Nc r q s *
    ‖cmp102PhysicalBackgroundShiftCLM
      U ha hP hε hsmall hbudget‖ ^ 2

/-- **Fixed-point source producer.**  Uniform source conditions at two
physical shifted fields imply a joint derivative-Lipschitz estimate for
the literal certificate-free fixed-point map. -/
theorem
    norm_fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_sub_apply_le_sourceBudget
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (p q R : FinePhysicalOneCochain d L N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc)
    {r z s : ℝ}
    (hr : 0 ≤ r) (hz13 : 1 / 3 ≤ z) (hz1 : z < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hp : ‖cmp102PhysicalCochainToAmbientCLM
      (cmp102PhysicalBackgroundShiftCLM
        U ha hP hε hsmall hbudget p)‖ ≤ r)
    (hq : ‖cmp102PhysicalCochainToAmbientCLM
      (cmp102PhysicalBackgroundShiftCLM
        U ha hP hε hsmall hbudget q)‖ ≤ r)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hDp : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget p))‖ ≤ z)
    (hDq : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget q))‖ ≤ z)
    (hdev :
      cmp102SourceAmbientRelativeDeviationValueBudget d L r z ≤ s) :
    ‖(fderiv ℝ
          (cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
            U ha hP hε hsmall hbudget) p -
        fderiv ℝ
          (cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
            U ha hP hε hsmall hbudget) q) R‖ ≤
      cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
          U ha hP hε hsmall hbudget r z s *
        ‖p - q‖ * ‖R‖ := by
  let shift :=
    cmp102PhysicalBackgroundShiftCLM
      U ha hP hε hsmall hbudget
  let C :=
    cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
      d L N' Nc r z s
  have hz0 : 0 ≤ z := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hz13
  have hrelativeP : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM (shift p)) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1 := by
    intro b
    exact ((norm_cmp102AmbientRelativeDeviation_le_sourceBudget
      U b (cmp102PhysicalCochainToAmbientCLM (shift p))
      hr hz13 hz1 hp (hbase b) (hDp b)).trans hdev).trans_lt hs1
  have hrelativeQ : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM (shift q)) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1 := by
    intro b
    exact ((norm_cmp102AmbientRelativeDeviation_le_sourceBudget
      U b (cmp102PhysicalCochainToAmbientCLM (shift q))
      hr hz13 hz1 hq (hbase b) (hDq b)).trans hdev).trans_lt hs1
  rw [ContinuousLinearMap.sub_apply,
    fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_apply
      U ha hP hε hsmall hbudget p R
      (fun b x hx => (hDp b x hx).trans_lt hz1) hrelativeP,
    fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_apply
      U ha hP hε hsmall hbudget q R
      (fun b x hx => (hDq b x hx).trans_lt hz1) hrelativeQ]
  have hsource :
      ‖fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U)
            (shift p) (shift R) -
          fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U)
            (shift q) (shift R)‖ ≤
        C * ‖shift p - shift q‖ * ‖shift R‖ :=
    norm_fderiv_cmp102IntrinsicPhysicalNonlinearCorrectionSup_sub_apply_le_sourceBudget
      U (shift p) (shift q) (shift R)
      hr hz13 hz1 hs0 hs1 hp hq hbase hDp hDq hdev
  have hC : 0 ≤ C := by
    unfold C
    unfold cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _)
        (cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget_nonneg
          hr hz0 hs0))
      (sq_nonneg _)
  have hpq : ‖shift p - shift q‖ ≤ ‖shift‖ * ‖p - q‖ := by
    rw [← map_sub]
    exact ContinuousLinearMap.le_opNorm shift (p - q)
  have hR : ‖shift R‖ ≤ ‖shift‖ * ‖R‖ :=
    ContinuousLinearMap.le_opNorm shift R
  calc
    ‖fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U)
          (shift p) (shift R) -
        fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U)
          (shift q) (shift R)‖
        ≤ C * ‖shift p - shift q‖ * ‖shift R‖ := hsource
    _ ≤ C * (‖shift‖ * ‖p - q‖) * (‖shift‖ * ‖R‖) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hpq hC) hR
        (norm_nonneg _)
        (mul_nonneg hC (mul_nonneg (norm_nonneg shift) (norm_nonneg (p - q))))
    _ = cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
          U ha hP hε hsmall hbudget r z s * ‖p - q‖ * ‖R‖ := by
      unfold
        cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
      dsimp only [C, shift]
      ring

end

end YangMills.RG
