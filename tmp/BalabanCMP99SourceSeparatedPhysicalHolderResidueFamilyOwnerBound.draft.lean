/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

H5e2: consume the complete zero-residue Holder family before transporting
the one remaining centered-periodic endpoint to the two-point owner metric.
The decay rate is not split termwise, and no representative multiplicity or
fine-site cardinality is introduced.  Regional B0, window 15 and terminal
fields remain open.
-/

import YangMills.RG.BalabanCMP89Eq249CompleteHolderMassUniformNormalizedIntegralBound
import YangMills.RG.BalabanCMP89CenteredGreenFourierSummability
import YangMills.RG.BalabanCMP99CenteredPeriodicEndpointDictionary
import YangMills.RG.BalabanCMP99SourceSeparatedPhysicalHolderResidueOwnerProjection
import YangMills.RG.BalabanCMP99SourceSeparatedPhysicalHolderCarrierDictionary
import YangMills.RG.BalabanCMP116CMP89PhysicalNearestEndpointOwnerTransport

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- The H5 residue family costs its exact product-l1 mass once.  The residual
centered endpoint is then transported once to the minimum of the two physical
owners.  In particular, the proof does not apply the owner estimate termwise
and does not divide the contour rate. -/
theorem
    tsum_norm_cmp99SourceSeparatedPhysicalHolderIntegral_le_owner_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {a rho alpha : ℝ}
    (ha : 0 ≤ a) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (halphaStrict : alpha < 1) (hrho : 0 < rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (y : FinBox 4 (2 * (K * Q))) (derivMu bondNu : Fin 4) :
    let Kfine := L ^ (depth + 1)
    let N := 2 * (K * Q)
    let u : Fin 4 → ℤ := fun nu =>
      -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement Kfine x y nu
    let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
    let holderU := cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu)
    let fineX := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth x
    let fineY := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth
      (blockBasepoint Kfine N y)
    let b : PhysicalBond 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
      (fineX, bondNu)
    let xi := cmp89Eq249FineLatticeSpacing Kfine 1
    let A := cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
      a rho alpha
    (∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        ‖cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
          (fun q => cmp89Eq251ComplexStabilizedIntegrand 4 Kfine 1
            0 a alpha
            (fun nu => (cmp89Eq251PhysicalBrillouinParameter q nu : ℂ))
            derivMu
            (cmp89Eq249PhysicalFineLatticeDisplacement xi holderU)
            (cmp89Eq249PhysicalFineLatticeDisplacement xi
              (cmp89SignedLatticeResidueAffineMap Kfine forwardU n.1)))‖) ≤
      A *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp ((rho * xi) *
              (2 * (L ^ (depth + 1) - 1) : ℕ)) *
            Real.exp (-rho *
              (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
                depth b fineY : ℝ)))) := by
  dsimp only
  let Kfine : ℕ := L ^ (depth + 1)
  let N : ℕ := 2 * (K * Q)
  let u : Fin 4 → ℤ := fun nu =>
    -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement Kfine x y nu
  let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
  let holderU := cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu)
  let fineX := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth x
  let fineY := cmp99SourceSeparatedFineSiteOfD4_draft L K Q depth
    (blockBasepoint Kfine N y)
  let b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
    (fineX, bondNu)
  let xi := cmp89Eq249FineLatticeSpacing Kfine 1
  let A := cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
    a rho alpha
  let coefficient := fun transportU : Fin 4 → ℤ =>
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
      (fun q => cmp89Eq251ComplexStabilizedIntegrand 4 Kfine 1
        0 a alpha
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter q nu : ℂ))
        derivMu
        (cmp89Eq249PhysicalFineLatticeDisplacement xi holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement xi transportU))
  have hA : 0 ≤ A := by
    dsimp [A, cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft]
    positivity
  have hcoefficient : ∀ transportU,
      ‖coefficient transportU‖ ≤
        A * cmp89SignedLatticeL1ExponentialWeight
          (rho / (Kfine : ℝ)) transportU := by
    intro transportU
    have h :=
      norm_cmp89Eq249NormalizedCompleteHolderIntegral_physicalFine_le_massUniform_draft
        (L := Kfine) (j := 1) (mass := 0) (a := a) (rho := rho)
        (alpha := alpha) ha halpha0 halpha1 halphaStrict hrho.le hradius
        (by norm_num) hwindow hamplitude derivMu
        (cmp116CMP89PhysicalBondHolderDisplacement_unit (x, bondNu))
        transportU
    rw [cmp89Eq248PhysicalFineGreenDecay_eq_signedLatticeWeight_draft] at h
    simpa [coefficient, xi, A, Kfine, mul_comm] using h
  have hresidue :=
    tsum_norm_cmp99FlatIntegerZeroResidueClass_le_centeredPeriodic
      (d := 4) (K := Kfine) (N := N) hrho hA coefficient hcoefficient
      forwardU
  let centered :=
    cmp99CenteredPeriodicEndpointVectorRepresentative (Kfine * N) forwardU
  have hcastD4 : ∀ nu,
      (centered nu : ZMod (Kfine * N)) =
        (((x.shift bondNu nu).val : ZMod (Kfine * N)) -
          ((blockBasepoint Kfine N y nu).val : ZMod (Kfine * N))) := by
    intro nu
    exact
      cmp99SourceSeparatedPhysicalHolderCenteredForwardBase_cast_eq_target_sub_blockBasepoint_draft
        x y bondNu nu
  have hcastSeparated : ∀ nu,
      (centered nu : ZMod
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) =
        ((cmp116BondTarget b nu).val : ZMod
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) -
        (fineY nu).val := by
    intro nu
    simpa [centered, Kfine, N, b, fineX, fineY,
      cmp99SourceSeparatedFineSiteOfD4_draft,
      cmp99Eq389SourceLocalizationSiteEquiv] using hcastD4 nu
  let selected := cmp89Eq249NearestEndpointTransport_draft
    (cmp116CMP89PhysicalBondHolderDisplacement b) centered
  have hselectedLength :
      cmp89Eq251LatticeL1Length selected ≤
        cmp89Eq251LatticeL1Length centered := by
    rw [cmp89Eq251LatticeL1Length_nearestEndpointTransport_eq_min_draft]
    exact min_le_left _ _
  have htargetSelected :
      cmp89SignedLatticeL1ExponentialWeight
          (rho / (Kfine : ℝ)) centered ≤
        Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement xi selected))) := by
    rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
    apply Real.exp_le_exp.mpr
    have hKfine : 0 < (Kfine : ℝ) := by
      exact_mod_cast pow_pos (NeZero.pos L) (depth + 1)
    have hxi : xi = (Kfine : ℝ)⁻¹ := by
      simp [xi, cmp89Eq249FineLatticeSpacing]
    rw [cmp89Eq251DisplacementL1_physicalFineLatticeDisplacement
      (by positivity : 0 ≤ xi), hxi]
    dsimp [cmp89Eq251LatticeL1Length] at hselectedLength ⊢
    have hrate : 0 ≤ rho / (Kfine : ℝ) := (div_pos hrho hKfine).le
    nlinarith
  have howner :=
    cmp116CMP89PhysicalNearestEndpointWeight_le_ownerWeight_of_cast_draft
      depth hrho.le b fineY centered hcastSeparated
  have htargetOwner :
      cmp89SignedLatticeL1ExponentialWeight
          (rho / (Kfine : ℝ)) centered ≤
        Real.exp ((rho * xi) *
            (2 * (L ^ (depth + 1) - 1) : ℕ)) *
          Real.exp (-rho *
            (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
              depth b fineY : ℝ)) := by
    exact htargetSelected.trans (by
      simpa [selected, xi, Kfine] using howner)
  have hmass : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left htargetOwner hmass
  exact hresidue.trans (by
    simpa [coefficient, centered, A, cmp89SignedLatticeResidueAffineMap,
      mul_assoc] using
      mul_le_mul_of_nonneg_left hscaled hA)

end

end YangMills.RG
