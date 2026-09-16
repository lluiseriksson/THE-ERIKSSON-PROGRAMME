/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Generated point-source left derivative and its literal source-owner bound.
The periodic target seam is discharged by the explicit zero-residue
equivalence, and the normalized divided difference is the mass-uniform CMP89
derivative series.  No regional Green, regional `B0`, window-15 attainment or
terminal field is asserted here.
-/

-- Promotion imports:
-- import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceZeroResidue
-- import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativeResidueShift
-- import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativePeriodization
-- import YangMills.RG.BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary
-- import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The wrapped generated target value reindexes to the ordinary forward
endpoint series before any subtraction or norm is taken. -/
theorem
    tsum_cmp99SourceSeparatedGeneratedFlatPhysicalGreen_shift_eq_forward_draft
    (depth : ℕ)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (y : FinBox 4 (2 * (K * Q))) (mu : Fin 4)
    (a : ℝ) :
    (∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          (L ^ (depth + 1)) 1 0 a
          (fun nu ⇒
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              (L ^ (depth + 1)) (x.shift mu) y nu) n.1) =
      ∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          (L ^ (depth + 1)) 1 0 a
          (cmp89Eq248FineLatticeForwardCoordinateShift mu
            (fun nu ⇒
              -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                (L ^ (depth + 1)) x y nu)) n.1 := by
  simpa [cmp89Eq248CenteredGreenPhysicalFourierCoefficient,
    cmp89SignedLatticeResidueAffineMap] using
    (tsum_cmp99SourceSeparatedFineTargetShift_affineResidue_eq_forward_draft
      (M := L ^ (depth + 1)) (N := 2 * (K * Q)) x y mu
      (cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
        (L ^ (depth + 1)) 1 0 a))

/-- Exact point-source forward difference of the internally generated
`G Q'^*`.  The right side is the literal zero-residue CMP89 derivative
coefficient family; no derivative operator or equality is supplied by the
caller. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_forwardDifference_eq_derivativeSeries_smul_draft
    (hL : 2 ≤ L) (depth : ℕ)
    (y : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho)
    (mu : Fin 4) :
    let T :=
      (cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc))
    let u : Fin 4 → ℤ := fun nu ⇒
      -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
        (L ^ (depth + 1)) x y nu
    (cmp89Eq249FineLatticeSpacing (L ^ (depth + 1)) 1 : ℂ)⁻¹ •
        (T (cmp99FlatComplexFibrePointSource y v) (x.shift mu) -
          T (cmp99FlatComplexFibrePointSource y v) x) =
      (∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          (L ^ (depth + 1)) 1 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
          mu u n.1) • v := by
  dsimp only
  let a : ℝ :=
    cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
  let u : Fin 4 → ℤ := fun nu ⇒
    -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
      (L ^ (depth + 1)) x y nu
  have hshift :=
    tsum_cmp99SourceSeparatedGeneratedFlatPhysicalGreen_shift_eq_forward_draft
      (L := L) (K := K) (Q := Q) depth x y mu a
  have hperiod :=
    tsum_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_forwardDifference_eq_derivative_draft
      (K := L ^ (depth + 1)) (N := 2 * (K * Q))
      (mass := 0) (a := a) (rho := rho)
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
      hrho hamplitude hradius hwindow (by norm_num) mu u
  have hscalar :
      ((∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
            cmp89Eq248CenteredGreenPhysicalFourierCoefficient
              (L ^ (depth + 1)) 1 0 a
              (fun nu ⇒
                -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                  (L ^ (depth + 1)) (x.shift mu) y nu) n.1) -
          ∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
            cmp89Eq248CenteredGreenPhysicalFourierCoefficient
              (L ^ (depth + 1)) 1 0 a u n.1) /
          (cmp89Eq249FineLatticeSpacing (L ^ (depth + 1)) 1 : ℂ) =
        ∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
          cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
            (L ^ (depth + 1)) 1 0 a mu u n.1 := by
    rw [hshift]
    exact hperiod
  rw [
    cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_eq_zeroResidue_smul
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v (x.shift mu) hrho hamplitude hradius hwindow,
    cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_apply_eq_zeroResidue_smul
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v x hrho hamplitude hradius hwindow]
  simpa [a, u, sub_smul, smul_sub, smul_smul, div_eq_mul_inv,
    mul_comm] using congrArg (fun z : ℂ ⇒ z • v) hscalar

/-- One zero-mass derivative coefficient has the exact signed-lattice
majorant used by the centered owner dictionary. -/
theorem norm_cmp89Eq249PhysicalZeroMassDerivative_le_signedLatticeWeight_draft
    {K : ℕ} [NeZero K] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    ‖cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
        K 1 0 a mu endpointU‖ ≤
      cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho *
        cmp89SignedLatticeL1ExponentialWeight
          (rho / (K : ℝ)) endpointU := by
  have h :=
    norm_cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel_massZero_le_draft
      (L := K) (j := 1) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow mu endpointU
  rw [cmp89Eq248PhysicalFineGreenDecay_eq_signedLatticeWeight_draft] at h
  simpa [mul_comm] using h

/-- Absolute mass of the derivative coefficients selected by residue zero,
retaining the centered endpoint decay and no `N^4` volume factor. -/
theorem tsum_norm_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_zeroResidue_le_draft
    {K N : ℕ} [NeZero K] [NeZero N] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (mu : Fin 4) (u : Fin 4 → ℤ) :
    (∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        ‖cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          K 1 0 a mu u n.1‖) ≤
      cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N) u)) := by
  let A := cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho
  let coefficient := fun endpointU : Fin 4 → ℤ ⇒
    cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
      K 1 0 a mu endpointU
  have hA : 0 ≤ A := by
    have hpoint :=
      norm_cmp89Eq249PhysicalZeroMassDerivative_le_signedLatticeWeight_draft
        (K := K) ha hrho.le hamplitude hradius hwindow mu 0
    simpa [A] using (le_trans (norm_nonneg _) hpoint)
  have hcoefficient : ∀ endpointU,
      ‖coefficient endpointU‖ ≤ A *
        cmp89SignedLatticeL1ExponentialWeight
          (rho / (K : ℝ)) endpointU := by
    intro endpointU
    exact norm_cmp89Eq249PhysicalZeroMassDerivative_le_signedLatticeWeight_draft
      ha hrho.le hamplitude hradius hwindow mu endpointU
  have h :=
    tsum_norm_cmp99FlatIntegerZeroResidueClass_le_centeredPeriodic
      (d := 4) (K := K) (N := N) hrho hA coefficient hcoefficient u
  simpa [A, coefficient,
    cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient,
    cmp89SignedLatticeResidueAffineMap] using h

/-- The scalar derivative series at the literal fine-to-coarse endpoint has
the same source-owner decay as the value branch, with the derivative
amplitude kept explicit. -/
theorem
    norm_tsum_cmp99SourceSeparatedGeneratedFlatPhysicalDerivative_zeroResidue_le_owner_draft
    (depth : ℕ) {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho)
    (mu : Fin 4)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    (y : FinBox 4 (2 * (K * Q))) :
    ‖∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          (L ^ (depth + 1)) 1 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
          mu
          (fun nu ⇒
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              (L ^ (depth + 1)) x y nu) n.1‖ ≤
      cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist (blockSite (L ^ (depth + 1))
              (2 * (K * Q)) x) y : ℝ)) := by
  let Kfine : ℕ := L ^ (depth + 1)
  let N : ℕ := 2 * (K * Q)
  let a : ℝ :=
    cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
  let u : Fin 4 → ℤ := fun nu ⇒
    -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement Kfine x y nu
  letI : NeZero Kfine := by
    dsimp [Kfine]
    infer_instance
  letI : NeZero N := by
    dsimp [N]
    infer_instance
  have hzero :=
    tsum_norm_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_zeroResidue_le_draft
      (K := Kfine) (N := N) (a := a) (rho := rho)
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
      hrho hamplitude hradius hwindow mu u
  have howner :=
    cmp89SignedLatticeL1ExponentialWeight_centered_neg_fineToCoarse_le_owner
      (M := Kfine) (N := N) hrho.le x y
  have hA :
      0 ≤ cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound
        a rho := by
    have hpoint :=
      norm_cmp89Eq249PhysicalZeroMassDerivative_le_signedLatticeWeight_draft
        (K := Kfine)
        (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
        hrho.le hamplitude hradius hwindow mu 0
    simpa using (le_trans (norm_nonneg _) hpoint)
  have hgeom : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 := by positivity
  change ‖∑' n : CMP99FlatIntegerResidueClass 4 N 0,
      cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
        Kfine 1 0 a mu u n.1‖ ≤ _
  calc
    ‖∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          Kfine 1 0 a mu u n.1‖ ≤
      ∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        ‖cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          Kfine 1 0 a mu u n.1‖ := by
      exact norm_tsum_le_tsum_norm
        (summable_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_zeroResidue_draft
          (K := Kfine) (N := N) (mass := 0) (a := a) (rho := rho)
          (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
          hrho hamplitude hradius hwindow (by norm_num) mu u).norm
    _ ≤ cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          cmp89SignedLatticeL1ExponentialWeight (rho / (Kfine : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative
              (Kfine * N) u)) := hzero
    _ ≤ cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp (2 * rho) *
            Real.exp (-rho *
              (finBoxDist (blockSite Kfine N x) y : ℝ)))) := by
      gcongr
    _ = _ := by ring

/-- D4d point-source action bound for the actual generated forward
difference.  The fine spacing is divided before the norm, and no source
cardinality factor is introduced. -/
theorem
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_forwardDifference_le_owner_draft
    (hL : 2 ≤ L) (depth : ℕ)
    (y : FinBox 4 (2 * (K * Q)))
    (v : SUNLieComplexCoord Nc)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho)
    (mu : Fin 4) :
    let T :=
      (cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc))
    ‖(cmp89Eq249FineLatticeSpacing (L ^ (depth + 1)) 1 : ℂ)⁻¹ •
        (T (cmp99FlatComplexFibrePointSource y v) (x.shift mu) -
          T (cmp99FlatComplexFibrePointSource y v) x)‖ ≤
      cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist (blockSite (L ^ (depth + 1))
              (2 * (K * Q)) x) y : ℝ)) * ‖v‖ := by
  dsimp only
  rw [
    cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_forwardDifference_eq_derivativeSeries_smul_draft
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth y v x hrho hamplitude hradius hwindow mu,
    norm_smul]
  exact mul_le_mul_of_nonneg_right
    (norm_tsum_cmp99SourceSeparatedGeneratedFlatPhysicalDerivative_zeroResidue_le_owner_draft
      (L := L) (K := K) (Q := Q) depth hrho hamplitude hradius hwindow
      mu x y)
    (norm_nonneg v)

/-- The point-source derivative bound upgrades to an arbitrary coarse field
supported in one identity-owner fibre, with the existing finite supremum norm
and no owner-fibre cardinality. -/
theorem
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_localizedField_forwardDifference_le_owner_draft
    (hL : 2 ≤ L) (depth : ℕ)
    (owner : FinBox 4 (2 * (K * Q)))
    (f : FinitePiLpField (FinBox 4 (2 * (K * Q)))
      (SUNLieComplexCoord Nc))
    (hf : FinitePiLpSupportedInOwner (fun y ⇒ y) owner f)
    (x : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))))
    {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho)
    (mu : Fin 4) :
    let T :=
      (cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1))
          (N' := 2 * (K * Q)) (Nc := Nc))
    ‖(cmp89Eq249FineLatticeSpacing (L ^ (depth + 1)) 1 : ℂ)⁻¹ •
        (T (WithLp.ofLp f) (x.shift mu) - T (WithLp.ofLp f) x)‖ ≤
      cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist (blockSite (L ^ (depth + 1))
              (2 * (K * Q)) x) owner : ℝ)) * finitePiLpSupNorm f := by
  dsimp only
  have hfpoint :=
    finitePiLp_of_supportedInIdentityOwner_eq_flatComplexFibrePointSource
      owner f hf
  rw [hfpoint]
  have hpoint :=
    norm_cmp99SourceSeparatedGeneratedFlatPhysicalGreenQprimeStar_pointSource_forwardDifference_le_owner_draft
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth owner (f owner) x hrho hamplitude hradius hwindow mu
  have hcoefficient :
      0 ≤ cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist (blockSite (L ^ (depth + 1))
              (2 * (K * Q)) x) owner : ℝ)) := by
    have hamp :
        0 ≤ cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho := by
      have hzero :=
        norm_cmp89Eq249PhysicalZeroMassDerivative_le_signedLatticeWeight_draft
          (K := L ^ (depth + 1))
          (cmp99SourceGeneratedFullComplexA_pos_physical L depth).le
          hrho.le hamplitude hradius hwindow mu 0
      simpa using (le_trans (norm_nonneg _) hzero)
    positivity
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (norm_apply_le_finitePiLpSupNorm f owner) hcoefficient)

end

end YangMills.RG
