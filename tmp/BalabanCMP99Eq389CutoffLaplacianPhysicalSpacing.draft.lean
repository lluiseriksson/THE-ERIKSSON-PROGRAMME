import YangMills.RG.BalabanCMP99Eq389SignedCutoffLaplacianPhysicalBound

/-!
SCRATCH ONLY: this file is neither imported nor compiler-verified and is not
evidence.

# CMP99 (3.89) second species at physical spacing

The sealed second-species producer fixes spacing one.  The literal physical
cutoff-Laplacian correction contains two inverse-spacing factors.  This leaf
keeps both factors explicit before any regional-cell or owner sum; they are
not absorbed into `B0` or the cutoff profile.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The literal cutoff-Laplacian correction at physical spacing is the
unit-spacing correction with two explicit inverse-spacing factors. -/
theorem norm_cmp99CutoffLaplacianCorrection_spacing_eq
    {d N : ℕ} [NeZero N]
    {spacing : ℝ} (hspacing : 0 < spacing)
    (h : FinBox d N → ℝ)
    (phi : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d N) :
    ‖cmp99CutoffLaplacianCorrection spacing h phi x‖ =
      spacing⁻¹ * spacing⁻¹ *
        ‖cmp99CutoffLaplacianCorrection 1 h phi x‖ := by
  unfold cmp99CutoffLaplacianCorrection
  simp only [inv_one, one_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hspacing)]
  ring

/-- Direct physical-spacing estimate for the signed source-separated second
species.  The exact `spacing⁻²` factor is present before every later sum. -/
theorem norm_cmp99CutoffLaplacianCorrection_sourceSeparated_spacing_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖cmp99CutoffLaplacianCorrection (Nc := Nc) spacing
        (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell) phi x‖ ≤
      spacing⁻¹ * spacing⁻¹ *
        (((48 * P.secondDerivBound) /
          cmp99SourceSeparatedLargeBlockCutoffScale L K depth ^ 2) *
            ‖phi x‖) := by
  have hinv : 0 ≤ spacing⁻¹ := (inv_pos.mpr hspacing).le
  rw [norm_cmp99CutoffLaplacianCorrection_spacing_eq hspacing]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hinv hinv)
  rw [cmp99CutoffLaplacianCorrection_one_eq_sourceSeparatedSignedCoefficient,
    norm_smul]
  exact mul_le_mul_of_nonneg_right
    (norm_cmp99SourceSeparatedSignedCutoffLaplacianCoefficient_le
      (L := L) (K := K) P depth cell x)
    (norm_nonneg _)

end

end YangMills.RG
