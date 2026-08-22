import YangMills.RG.BalabanCMP99SourceGeneratedFullComplexAPositive
import YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse
import YangMills.RG.BalabanCMP99SourceFlatRetainedPhysicalTower

/-!
# PRE-VALIDATION: depth decay of the Poincare-generated full-complex coefficient

Source is present, its `.olean` has not been materialized, and the result has
not yet been verified by the compiler.

This diagnostic separates two coefficients that must not be identified
silently.  The source averaging coefficient has a positive depth-uniform
floor, whereas the coefficient obtained by normalizing the recursive
Poincare ledger loses at least a factor two at every additional canonical
flat depth.

Honest scope: the terminal theorem concerns the generated coefficient
`cmp99SourceGeneratedFullComplexA`.  It does not refute the source coefficient
`a_j`; it proves that a dictionary identifying the two coefficients cannot be
definitionally inherited from the present Poincare-generated tower.
-/

namespace YangMills.RG

noncomputable section

/-- The physical full-complex coefficient at positive canonical depth. -/
noncomputable def cmp99SourceGeneratedCanonicalFullComplexA
    (d M depth : ℕ) : ℝ :=
  cmp99SourceGeneratedFullComplexA d M (depth + 1)
    (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0

/-- Multiplying the canonical spacing at the next depth by one block side
recovers the canonical spacing at the preceding depth. -/
theorem cmp99SourceGeneratedFullComplexSpacing_succ_scale
    (M depth : ℕ) [NeZero M] :
    (M : ℝ) * cmp99SourceGeneratedFullComplexSpacing M (depth + 1) =
      cmp99SourceGeneratedFullComplexSpacing M depth := by
  unfold cmp99SourceGeneratedFullComplexSpacing
    cmp99SourceGeneratedFullComplexBlockSide
  rw [pow_succ, Nat.cast_mul, Nat.cast_pow]
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne M)]

/-- Exact canonical-spacing recurrence for the generated Poincare energy
coefficient at zero source radius. -/
theorem cmp99SourcePoincareEnergyCoeff_canonical_succ
    (d M depth : ℕ) [NeZero d] [NeZero M] :
    cmp99SourcePoincareEnergyCoeff d M (depth + 2)
        (cmp99SourceGeneratedFullComplexSpacing M (depth + 2)) 0 =
      cmp99OneScaleBlockPoincareConstant d M *
        ((cmp99SourceGeneratedFullComplexSpacing M (depth + 2)) ^ 2 +
          2 * cmp99SourceBlockAverageWeight M d *
            cmp99SourcePoincareEnergyCoeff d M (depth + 1)
              (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0) := by
  simp only [cmp99SourcePoincareEnergyCoeff,
    cmp99SourceUbarNextFineRadius_zero]
  rw [cmp99SourceGeneratedFullComplexSpacing_succ_scale]

/-- Each extra canonical flat depth loses at least one factor two in the
Poincare-generated full-complex coefficient. -/
theorem cmp99SourceGeneratedCanonicalFullComplexA_succ_le_half
    (d M depth : ℕ) [NeZero d] [NeZero M] :
    cmp99SourceGeneratedCanonicalFullComplexA d M (depth + 1) ≤
      cmp99SourceGeneratedCanonicalFullComplexA d M depth / 2 := by
  let C := cmp99OneScaleBlockPoincareConstant d M
  let w := cmp99SourceBlockAverageWeight M d
  let sNext := cmp99SourceGeneratedFullComplexSpacing M (depth + 2)
  let sPrev := cmp99SourceGeneratedFullComplexSpacing M (depth + 1)
  let EPrev := cmp99SourcePoincareEnergyCoeff d M (depth + 1) sPrev 0
  let ENext := cmp99SourcePoincareEnergyCoeff d M (depth + 2) sNext 0
  have hC : 0 < C := by
    exact cmp99OneScaleBlockPoincareConstant_pos
  have hw : 0 < w := by
    exact cmp99SourceBlockAverageWeight_pos M d
  have hsPrev : 0 < sPrev := by
    exact cmp99SourceGeneratedFullComplexSpacing_pos M (depth + 1)
  have hsNext : 0 < sNext := by
    exact cmp99SourceGeneratedFullComplexSpacing_pos M (depth + 2)
  have hEPrev : 0 < EPrev := by
    exact cmp99SourcePoincareEnergyCoeff_pos_succ d M depth hsPrev
  have hENext : 0 < ENext := by
    exact cmp99SourcePoincareEnergyCoeff_pos_succ d M (depth + 1) hsNext
  have hrec :
      ENext = C * (sNext ^ 2 + 2 * w * EPrev) := by
    dsimp [C, w, sNext, sPrev, EPrev, ENext]
    exact cmp99SourcePoincareEnergyCoeff_canonical_succ d M depth
  have hlower : 2 * C * w * EPrev ≤ ENext := by
    rw [hrec]
    nlinarith [sq_nonneg sNext]
  have hden : 0 < 2 * C * w * EPrev := by positivity
  have hnum :
      0 ≤ C ^ (depth + 2) *
        cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d := by positivity
  have hdiv :
      (C ^ (depth + 2) *
          cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d) / ENext ≤
        (C ^ (depth + 2) *
          cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d) /
            (2 * C * w * EPrev) := by
    apply (le_div_iff₀ hden).2
    calc
      (C ^ (depth + 2) *
            cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d) /
              ENext * (2 * C * w * EPrev) ≤
          (C ^ (depth + 2) *
            cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d) /
              ENext * ENext := by
        exact mul_le_mul_of_nonneg_left hlower (div_nonneg hnum hENext.le)
      _ = C ^ (depth + 2) *
            cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d := by
        exact div_mul_cancel₀ _ (ne_of_gt hENext)
  change
    (C ^ (depth + 2) / ENext) *
        cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d ≤
      ((C ^ (depth + 1) / EPrev) *
        cmp99SourceBlockAverageWeight (M ^ (depth + 1)) d) / 2
  rw [show
    (C ^ (depth + 2) / ENext) *
        cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d =
      (C ^ (depth + 2) *
        cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d) / ENext by ring]
  refine hdiv.trans_eq ?_
  rw [← cmp99SourceBlockAverageWeight_pow_eq_oneBlock M d (depth + 2),
    ← cmp99SourceBlockAverageWeight_pow_eq_oneBlock M d (depth + 1)]
  field_simp [ne_of_gt hC, ne_of_gt hw, ne_of_gt hEPrev]
  ring

end

end YangMills.RG
