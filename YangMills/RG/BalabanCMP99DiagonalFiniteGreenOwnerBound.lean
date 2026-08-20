/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This file closes the periodic-owner estimate only on the diagonal Gate-7
carrier `FinBox 4 (K*N)`: Green scale and owner-block side are both `K`.
It retains the exact boundary factor and does not identify this owner with
CMP99's final source-localization owner at independent scales `(L,Klarge)`.
Thus it is item 4 of the post-Gate-7 route, not item 5, not regional `B0`, and
not window-15 attainment.
-/

import YangMills.RG.BalabanCMP99PhysicalGreenZeroResidueBound
import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- Shortest signed periodic displacement on the diagonal fine carrier. -/
def cmp99DiagonalPeriodicDisplacement
    {d K N : ℕ} [NeZero K] [NeZero N]
    (x y : FinBox d (K * N)) : Fin d → ℤ :=
  fun mu => cmp116CMP89PeriodicCoordinateDisplacement (x mu) (y mu)

/-- Its exact `l1` length is the sum of coordinatewise torus distances. -/
theorem cmp89Eq251LatticeL1Length_cmp99DiagonalPeriodicDisplacement_eq
    {d K N : ℕ} [NeZero K] [NeZero N]
    (x y : FinBox d (K * N)) :
    cmp89Eq251LatticeL1Length (cmp99DiagonalPeriodicDisplacement x y) =
      ∑ mu, (finTorusDist (x mu) (y mu) : ℝ) := by
  unfold cmp89Eq251LatticeL1Length cmp99DiagonalPeriodicDisplacement
  apply Finset.sum_congr rfl
  intro mu _
  congr 1
  exact natAbs_cmp116CMP89PeriodicCoordinateDisplacement_eq_finTorusDist _ _

/-- Re-centering the already shortest periodic displacement can change the
antipodal sign but not its exact `l1` length. -/
theorem cmp89Eq251LatticeL1Length_centeredDiagonalPeriodicDisplacement_eq
    {d K N : ℕ} [NeZero K] [NeZero N]
    (x y : FinBox d (K * N)) :
    cmp89Eq251LatticeL1Length
        (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
          (cmp99DiagonalPeriodicDisplacement x y)) =
      cmp89Eq251LatticeL1Length
        (cmp99DiagonalPeriodicDisplacement x y) := by
  let z : Fin d → ZMod (K * N) := fun mu =>
    ((x mu).val : ZMod (K * N)) - ((y mu).val : ZMod (K * N))
  have h := cmp89Eq251LatticeL1Length_centeredPeriodic_valMinAbs_eq z
  simpa [z, cmp99DiagonalPeriodicDisplacement,
    cmp116CMP89PeriodicCoordinateDisplacement] using h

/-- Real-valued form consumed by the exponential transport. -/
theorem cmp99DiagonalOwner_mul_dist_real_le_periodicL1_add_boundary
    {K N : ℕ} [NeZero K] [NeZero N]
    (x y : FinBox 4 (K * N)) :
    (K : ℝ) *
        (finBoxDist (blockSite K N x) (blockSite K N y) : ℝ) ≤
      cmp89Eq251LatticeL1Length
          (cmp99DiagonalPeriodicDisplacement x y) +
        (2 * (K - 1) : ℕ) := by
  have hblock :=
    mul_finBoxDist_blockSite_le_finBoxDist_add_two_mul_sub_one x y
  have hblockReal :
      (K : ℝ) *
          (finBoxDist (blockSite K N x) (blockSite K N y) : ℝ) ≤
        (finBoxDist x y : ℝ) + (2 * (K - 1) : ℕ) := by
    exact_mod_cast hblock
  have hfine :
      (finBoxDist x y : ℝ) ≤
        cmp89Eq251LatticeL1Length
          (cmp99DiagonalPeriodicDisplacement x y) := by
    rw [cmp89Eq251LatticeL1Length_cmp99DiagonalPeriodicDisplacement_eq]
    exact_mod_cast finBoxDist_le_sum_finTorusDist x y
  exact hblockReal.trans (add_le_add hfine (le_refl _))

/-- The centered periodic Fourier weight transports to the diagonal owner
metric with the exact scale-free boundary factor `exp (2*rho)`. -/
theorem cmp89SignedLatticeL1ExponentialWeight_centeredDiagonal_le_owner
    {K N : ℕ} [NeZero K] [NeZero N]
    {rho : ℝ} (hrho : 0 ≤ rho)
    (x y : FinBox 4 (K * N)) :
    cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
        (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
          (cmp99DiagonalPeriodicDisplacement x y)) ≤
      Real.exp (2 * rho) *
        Real.exp (-rho *
          (finBoxDist (blockSite K N x) (blockSite K N y) : ℝ)) := by
  have hKReal : 0 < (K : ℝ) := by exact_mod_cast NeZero.pos K
  have howner :=
    cmp99DiagonalOwner_mul_dist_real_le_periodicL1_add_boundary x y
  have hlength :=
    cmp89Eq251LatticeL1Length_centeredDiagonalPeriodicDisplacement_eq x y
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  unfold cmp89Eq251LatticeL1Length at hlength
  rw [hlength]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hboundary :
      (rho / (K : ℝ)) * (2 * (K - 1) : ℕ) ≤ 2 * rho := by
    have hnat : (2 * (K - 1) : ℕ) ≤ 2 * K := by omega
    have hreal : ((2 * (K - 1) : ℕ) : ℝ) ≤ 2 * (K : ℝ) := by
      exact_mod_cast hnat
    calc
      (rho / (K : ℝ)) * (2 * (K - 1) : ℕ) ≤
          (rho / (K : ℝ)) * (2 * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hreal (div_nonneg hrho hKReal.le)
      _ = 2 * rho := by field_simp [ne_of_gt hKReal] <;> ring
  have hscaled :
      rho *
          (finBoxDist (blockSite K N x) (blockSite K N y) : ℝ) ≤
        (rho / (K : ℝ)) *
          cmp89Eq251LatticeL1Length
            (cmp99DiagonalPeriodicDisplacement x y) + 2 * rho := by
    calc
      rho *
          (finBoxDist (blockSite K N x) (blockSite K N y) : ℝ) =
        (rho / (K : ℝ)) *
          ((K : ℝ) *
            (finBoxDist (blockSite K N x) (blockSite K N y) : ℝ)) := by
              field_simp [ne_of_gt hKReal]
      _ ≤ (rho / (K : ℝ)) *
          (cmp89Eq251LatticeL1Length
              (cmp99DiagonalPeriodicDisplacement x y) +
            (2 * (K - 1) : ℕ)) :=
        mul_le_mul_of_nonneg_left howner (div_nonneg hrho hKReal.le)
      _ = (rho / (K : ℝ)) *
            cmp89Eq251LatticeL1Length
              (cmp99DiagonalPeriodicDisplacement x y) +
          (rho / (K : ℝ)) * (2 * (K - 1) : ℕ) := by ring
      _ ≤ (rho / (K : ℝ)) *
            cmp89Eq251LatticeL1Length
              (cmp99DiagonalPeriodicDisplacement x y) + 2 * rho :=
        add_le_add_right hboundary _
  linarith

/-- Diagonal Gate-7 owner bound for the actual residue-zero physical Green
coefficient sum.  This is not yet the separated-scale regional `B0`. -/
theorem norm_tsum_cmp89Eq248PhysicalGreen_zeroResidue_le_diagonalOwner_draft
    {K N : ℕ} [NeZero K] [NeZero N] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (x y : FinBox 4 (K * N)) :
    ‖∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient K 1 0 a
          (cmp99DiagonalPeriodicDisplacement x y) n.1‖ ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist (blockSite K N x) (blockSite K N y) : ℝ)) := by
  have hzero :=
    norm_tsum_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_zeroResidue_le_draft
      (K := K) (N := N) ha hrho hamplitude hradius hwindow
      (cmp99DiagonalPeriodicDisplacement x y)
  have howner :=
    cmp89SignedLatticeL1ExponentialWeight_centeredDiagonal_le_owner
      hrho.le x y
  have hA :
      0 ≤ cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho := by
    have hpoint :=
      norm_cmp89Eq248PhysicalZeroMassGreen_le_signedLatticeWeight_draft
        (K := K) ha hrho.le hamplitude hradius hwindow 0
    simpa [cmp89SignedLatticeL1ExponentialWeight,
      cmp89SignedLatticeOneDimensionalExpWeight] using
        (le_trans (norm_nonneg _) hpoint)
  have hgeom : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 := by positivity
  calc
    ‖∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient K 1 0 a
          (cmp99DiagonalPeriodicDisplacement x y) n.1‖ ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          cmp89SignedLatticeL1ExponentialWeight (rho / (K : ℝ))
            (cmp99CenteredPeriodicEndpointVectorRepresentative (K * N)
              (cmp99DiagonalPeriodicDisplacement x y))) := hzero
    _ ≤ cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp (2 * rho) *
            Real.exp (-rho *
              (finBoxDist (blockSite K N x) (blockSite K N y) : ℝ)))) := by
      gcongr
    _ = cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho) *
          Real.exp (-rho *
            (finBoxDist (blockSite K N x) (blockSite K N y) : ℝ)) := by ring

end

end YangMills.RG
