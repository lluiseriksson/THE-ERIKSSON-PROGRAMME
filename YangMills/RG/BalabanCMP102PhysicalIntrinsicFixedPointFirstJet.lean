/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicFixedPointJetZero

/-!
# First joint jet of the intrinsic CMP102 fixed-point source

The source-generated derivative-Lipschitz estimate is anchored at the
proved zero first jet.  This yields an operator-norm bound for the literal
joint source map at a physical point; no first-jet budget is supplied by
the caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
  [NeZero (M * N')]

local instance cmp102FirstJetCoordCLMNorm :
    Norm (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102FirstJetCoordCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102FirstJetCoordCLMNormedSpace :
    NormedSpace ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toNormedSpace

/-- The generated joint derivative-Lipschitz budget is nonnegative under
the same scalar source conditions used by its producer. -/
theorem
    cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget_nonneg
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d M N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    {r z s : ℝ} (hr : 0 ≤ r) (hz : 0 ≤ z) (hs : 0 ≤ s) :
    0 ≤
      cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
        U ha hP hε hsmall hbudget r z s := by
  unfold
    cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
  exact mul_nonneg
    (by
      unfold cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
      exact mul_nonneg
        (mul_nonneg (norm_nonneg (cmp98AmbientToLieCoordCLM Nc))
          (cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget_nonneg
            hr hz hs))
        (sq_nonneg _))
    (sq_nonneg _)

set_option maxHeartbeats 1000000 in
/-- Pointwise form of the physical first-joint-jet estimate. -/
theorem
    norm_fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_apply_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d M N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (p : FinePhysicalOneCochain d M N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc)
    (R : FinePhysicalOneCochain d M N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc)
    {r z s : ℝ}
    (hr : 0 ≤ r) (hz13 : 1 / 3 ≤ z) (hz1 : z < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hp : ‖cmp102PhysicalCochainToAmbientCLM
      (cmp102PhysicalBackgroundShiftCLM
        U ha hP hε hsmall hbudget p)‖ ≤ r)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hDp : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget p))‖ ≤ z)
    (hdev :
      cmp102SourceAmbientRelativeDeviationValueBudget d M r z ≤ s) :
    ‖fderiv ℝ
      (cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
        U ha hP hε hsmall hbudget) p R‖ ≤
      cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
          U ha hP hε hsmall hbudget r z s * ‖p‖ * ‖R‖ := by
  have hq :
      ‖cmp102PhysicalCochainToAmbientCLM
        (cmp102PhysicalBackgroundShiftCLM
          U ha hP hε hsmall hbudget
            (0 : FinePhysicalOneCochain d M N' Nc ×
              PhysicalGaugeOneCochainSup d N' Nc))‖ ≤ r := by
    simpa only [map_zero, norm_zero] using hr
  have hDq : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget
              (0 : FinePhysicalOneCochain d M N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc)))‖ ≤ z := by
    intro b x hx
    simpa only [map_zero] using (hbase b x hx).trans hz13
  have hmain :=
    norm_fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_sub_apply_le_sourceBudget
      (d := d) (L := M) (N' := N') (Nc := Nc)
      U ha hP hε hsmall hbudget p 0 R
      hr hz13 hz1 hs0 hs1 hp hq hbase hDp hDq hdev
  have hzero :=
    fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_zero
      U ha hP hε hsmall hbudget hbase
  rw [hzero, sub_zero] at hmain
  simpa using hmain

set_option maxHeartbeats 1000000 in
/-- **Physical first-joint-jet producer.**  The first derivative of the
literal uncurried CMP102 source map is controlled by its generated
derivative-Lipschitz constant times the distance from the zero source. -/
theorem
    norm_iteratedFDeriv_one_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d M N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (p : FinePhysicalOneCochain d M N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc)
    {r z s : ℝ}
    (hr : 0 ≤ r) (hz13 : 1 / 3 ≤ z) (hz1 : z < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hp : ‖cmp102PhysicalCochainToAmbientCLM
      (cmp102PhysicalBackgroundShiftCLM
        U ha hP hε hsmall hbudget p)‖ ≤ r)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hDp : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget p))‖ ≤ z)
    (hdev :
      cmp102SourceAmbientRelativeDeviationValueBudget d M r z ≤ s) :
    ‖iteratedFDeriv ℝ 1
      (cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
        U ha hP hε hsmall hbudget) p‖ ≤
      cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
          U ha hP hε hsmall hbudget r z s * ‖p‖ := by
  have hz0 : 0 ≤ z := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hz13
  have hB0 :
      0 ≤
        cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
          U ha hP hε hsmall hbudget r z s :=
    cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget_nonneg
      U ha hP hε hsmall hbudget hr hz0 hs0
  rw [norm_iteratedFDeriv_one]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB0 (norm_nonneg p))
  intro R
  exact
    norm_fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_apply_le
      U ha hP hε hsmall hbudget p R hr hz13 hz1 hs0 hs1
      hp hbase hDp hdev

end

end YangMills.RG
