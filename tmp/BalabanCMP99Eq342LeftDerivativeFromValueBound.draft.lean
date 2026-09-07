import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixLeftDerivativeOwnerDecay

/-!
SCRATCH ONLY: this file is neither imported nor compiler-verified and is not
evidence.

# Localized left derivative from a localized Green value bound

This is the reusable algebraic step behind the second post-D2 action.  It
does not choose a background or a Green.  The physical specialization must
still instantiate both with the named C6d source-carrier objects.

The result spends the value estimate at the two endpoints of one fine bond.
The shifted endpoint costs exactly `exp rate`; the terminal spacing is
`ell * spacing`.  Thus an input amplitude `A * ell^2` becomes

`A * ((1 + exp rate) / spacing) * ell`.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq342LeftDerivativeAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- A localized value estimate yields the literal covariant left-derivative
estimate at terminal spacing.  No identification of the background or Green
is hidden in this lemma. -/
theorem cmp99Eq342_leftDerivative_blockLocalizedSupBound_of_value
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (background : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (G : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {spacing ell A rate : ℝ}
    (hspacing : 0 < spacing) (hell : 0 < ell)
    (hG : FinitePiLpTypedBlockLocalizedSupBound G
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (A * ell ^ 2) rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM Omega
          (matrixSUNAdjointModel Nc) background (ell * spacing)).comp G)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist (A * ((1 + Real.exp rate) / spacing) * ell) rate := by
  have hterminal : 0 < ell * spacing := mul_pos hell hspacing
  have hAell : 0 ≤ A * ell ^ 2 := hG.1
  have hrate : 0 < rate := hG.2.1
  have hA : 0 ≤ A := by
    have hellsq : 0 < ell ^ 2 := sq_pos_of_pos hell
    exact nonneg_of_mul_nonneg_left hAell hellsq
  have hout : 0 ≤ A * ((1 + Real.exp rate) / spacing) * ell := by
    exact mul_nonneg
      (mul_nonneg hA
        (div_nonneg (add_nonneg zero_le_one (Real.exp_pos _).le)
          hspacing.le))
      hell.le
  refine ⟨hout, hrate, ?_⟩
  intro owner f hf bond
  let phi := G f
  let extPhi := extendZeroZeroCLM Omega phi
  have hvalue (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
      ‖extPhi x‖ ≤
        (A * ell ^ 2) *
          Real.exp (-(rate *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth x)
              owner : ℝ))) * finitePiLpSupNorm f := by
    by_cases hx : x ∈ Omega.sites
    · let target : ActiveGaugeRegion.Site Omega := ⟨x, hx⟩
      have hbase := hG.2.2 owner f hf target
      simpa [phi, extPhi,
        extendZeroZeroCLM_apply_of_mem Omega phi x hx,
        cmp99Eq342SourceLocalizedActiveOwner, target,
        finBoxDist_comm] using hbase
    · rw [show extPhi x = 0 by
          exact extendZeroZeroCLM_apply_of_not_mem Omega phi x hx, norm_zero]
      exact mul_nonneg
        (mul_nonneg hAell (Real.exp_pos _).le)
        (finitePiLpSupNorm_nonneg f)
  have hfirst := hvalue bond.1
  have hshift := hvalue (bond.1.shift bond.2)
  have hshiftExp := exp_neg_sourceLocalizationOwner_shift_le_exp_mul
    L K Q depth bond.1 owner bond.2 hrate.le
  have hshiftValue :
      ‖extPhi (bond.1.shift bond.2)‖ ≤
        (A * ell ^ 2) *
          (Real.exp rate * Real.exp (-(rate *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth bond.1)
              owner : ℝ)))) * finitePiLpSupNorm f := by
    calc
      ‖extPhi (bond.1.shift bond.2)‖ ≤
          (A * ell ^ 2) *
            Real.exp (-(rate *
              (finBoxDist
                (cmp99Eq389SourceLocalizationOwner L K Q depth
                  (bond.1.shift bond.2)) owner : ℝ))) *
            finitePiLpSupNorm f := hshift
      _ ≤ (A * ell ^ 2) *
          (Real.exp rate * Real.exp (-(rate *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth bond.1)
              owner : ℝ)))) * finitePiLpSupNorm f := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hshiftExp hAell)
          (finitePiLpSupNorm_nonneg f)
  change ‖(ell * spacing)⁻¹ •
    (extPhi bond.1 -
      (matrixSUNAdjointModel Nc).adCLM
        (background (ConcreteEdge.mk bond.1 bond.2 true))
        (extPhi (bond.1.shift bond.2)))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hterminal)]
  calc
    (ell * spacing)⁻¹ *
        ‖extPhi bond.1 -
          (matrixSUNAdjointModel Nc).adCLM
            (background (ConcreteEdge.mk bond.1 bond.2 true))
            (extPhi (bond.1.shift bond.2))‖ ≤
      (ell * spacing)⁻¹ *
        (‖extPhi bond.1‖ + ‖extPhi (bond.1.shift bond.2)‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hterminal.le)
      calc
        ‖extPhi bond.1 -
          (matrixSUNAdjointModel Nc).adCLM
            (background (ConcreteEdge.mk bond.1 bond.2 true))
            (extPhi (bond.1.shift bond.2))‖ ≤
            ‖extPhi bond.1‖ +
              ‖(matrixSUNAdjointModel Nc).adCLM
                (background (ConcreteEdge.mk bond.1 bond.2 true))
                (extPhi (bond.1.shift bond.2))‖ := norm_sub_le _ _
        _ = ‖extPhi bond.1‖ + ‖extPhi (bond.1.shift bond.2)‖ := by
          rw [(matrixSUNAdjointModel Nc).norm_ad]
    _ ≤ (ell * spacing)⁻¹ *
        ((A * ell ^ 2) *
            Real.exp (-(rate *
              (finBoxDist
                (cmp99Eq389SourceLocalizationOwner L K Q depth bond.1)
                owner : ℝ))) * finitePiLpSupNorm f +
          (A * ell ^ 2) *
            (Real.exp rate * Real.exp (-(rate *
              (finBoxDist
                (cmp99Eq389SourceLocalizationOwner L K Q depth bond.1)
                owner : ℝ)))) * finitePiLpSupNorm f) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hfirst hshiftValue)
        (inv_nonneg.mpr hterminal.le)
    _ = (A * ((1 + Real.exp rate) / spacing) * ell) *
        Real.exp (-(rate *
          (finBoxDist
            (cmp99Eq342SourceLocalizedBondOwner L K Q depth bond)
            owner : ℝ))) * finitePiLpSupNorm f := by
      unfold cmp99Eq342SourceLocalizedBondOwner
      field_simp [ne_of_gt hspacing, ne_of_gt hell]

end

end YangMills.RG
