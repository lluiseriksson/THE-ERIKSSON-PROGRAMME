/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

H5e3a: combine the exact generated point-source Holder identity with H5e2's
residue-family owner bound.  Absolute summability is reconstructed from the
two physical derivative coefficient families and the exact termwise Holder
identity before `norm_tsum_le_tsum_norm` is used.  No source extension,
regional B0, window-15 attainment or terminal field is claimed here.
-/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolder
import YangMills.RG.BalabanCMP99SourceSeparatedPhysicalHolderResidueFamilyOwnerBound

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The literal generated point-source Holder difference inherits the exact
two-point owner decay.  The zero-residue family has already been summed before
the owner estimate, so neither a fine cardinality nor a second endpoint bound
appears. -/
theorem
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderDifference_le_owner_draft
    (hL : 2 ≤ L) (depth : ℕ)
    (y : FinBox 4 (2 * (K * Q))) (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho alpha : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (halphaStrict : alpha < 1) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho)
    (derivMu bondNu : Fin 4) :
    let Kfine := L ^ (depth + 1)
    let N := 2 * (K * Q)
    let a := cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
    let fineX := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth x
    let fineY := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth
      (blockBasepoint Kfine N y)
    let b : PhysicalBond 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
      (fineX, bondNu)
    let xi := cmp89Eq249FineLatticeSpacing Kfine 1
    let A := cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
      a rho alpha
    ‖(((xi ^ alpha : ℝ) : ℂ)⁻¹) •
        (cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
            (L := L) (K := K) (Q := Q) (Nc := Nc)
            hL depth y v x derivMu -
          cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
            (L := L) (K := K) (Q := Q) (Nc := Nc)
            hL depth y v (x.shift bondNu) derivMu)‖ ≤
      (A *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp ((rho * xi) *
              (2 * (L ^ (depth + 1) - 1) : ℕ)) *
            Real.exp (-rho *
              (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
                depth b fineY : ℝ)))) * ‖v‖) := by
  dsimp only
  let Kfine : ℕ := L ^ (depth + 1)
  let N : ℕ := 2 * (K * Q)
  let a : ℝ := cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
    (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
  let u : Fin 4 → ℤ := fun nu =>
    -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement Kfine x y nu
  let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
  let holderU := cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu)
  let xi := cmp89Eq249FineLatticeSpacing Kfine 1
  let c : ℂ := (((xi ^ alpha : ℝ) : ℂ)⁻¹)
  let sourceCoeff := fun n : CMP99FlatIntegerResidueClass 4 N 0 =>
    cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
      Kfine 1 0 a derivMu u n.1
  let forwardCoeff := fun n : CMP99FlatIntegerResidueClass 4 N 0 =>
    cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
      Kfine 1 0 a derivMu forwardU n.1
  let holderTerm := fun n : CMP99FlatIntegerResidueClass 4 N 0 =>
    cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
      Kfine 1 0 a alpha derivMu holderU
      (cmp89SignedLatticeResidueAffineMap Kfine forwardU n.1)
  have hsource : Summable sourceCoeff :=
    summable_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_zeroResidue_draft
      (K := Kfine) (N := N) (mass := 0) (a := a) (rho := rho)
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
      hrho hamplitude hradius hwindow (by norm_num) derivMu u
  have hforward : Summable forwardCoeff :=
    summable_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_zeroResidue_draft
      (K := Kfine) (N := N) (mass := 0) (a := a) (rho := rho)
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
      hrho hamplitude hradius hwindow (by norm_num) derivMu forwardU
  have hpoint : ∀ n, holderTerm n =
      c * (sourceCoeff n - forwardCoeff n) := by
    intro n
    have hholder :=
      cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_eq_xiRpowInv_mul_raw_draft
        (L := Kfine) (j := 1) (mass := 0) (a := a) (alpha := alpha)
        derivMu (cmp116CMP89PhysicalBondHolderDisplacement_unit (x, bondNu))
        (cmp89SignedLatticeResidueAffineMap Kfine forwardU n.1)
    have hraw :=
      cmp89Eq249NormalizedFineLatticeStabilizedIntegral_physicalBond_eq_sourceCoefficient_sub_forwardCoefficient_draft
        (K := Kfine) (N := N) (mass := 0) (a := a) (rho := rho)
        (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
        hrho.le hamplitude hradius hwindow (by norm_num)
        x derivMu bondNu u n
    simpa [holderTerm, holderU, sourceCoeff, forwardCoeff, forwardU, c, xi]
      using hholder.trans (congrArg (fun z : ℂ => c * z) hraw)
  have hholder : Summable holderTerm := by
    refine Summable.congr ((hsource.sub hforward).mul_left c) ?_
    intro n
    exact (hpoint n).symm
  have hsumBound :=
    tsum_norm_cmp99SourceSeparatedPhysicalHolderIntegral_le_owner_draft
      (L := L) (K := K) (Q := Q) depth
      (a := a) (rho := rho) (alpha := alpha)
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
      halpha0 halpha1 halphaStrict hrho hradius hwindow hamplitude
      x y derivMu bondNu
  have hnormTsum := (norm_tsum_le_tsum_norm hholder.norm).trans hsumBound
  have hidentity :=
    cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderDifference_eq_tsumIntegral_smul_draft
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v x hrho hamplitude hradius hwindow derivMu bondNu
  change ‖c •
      (cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          hL depth y v x derivMu -
        cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative_draft
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          hL depth y v (x.shift bondNu) derivMu)‖ ≤ _
  rw [hidentity, norm_smul]
  exact mul_le_mul_of_nonneg_right hnormTsum (norm_nonneg v)

end

end YangMills.RG
