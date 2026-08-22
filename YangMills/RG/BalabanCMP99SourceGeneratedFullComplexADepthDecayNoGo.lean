import YangMills.RG.BalabanCMP99SourceGeneratedFullComplexAPositive
import YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse
import YangMills.RG.BalabanCMP99SourceFlatRetainedPhysicalTower
import YangMills.RG.BalabanCMP85SourceAveragingCoefficientFloor

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
        cmp99SourceBlockAverageWeight (M ^ (depth + 2)) d := by
    exact mul_nonneg (pow_nonneg hC.le _)
      (cmp99SourceBlockAverageWeight_nonneg (M ^ (depth + 2)) d)
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

/-- Iterating the adjacent-depth estimate exposes the complete geometric
loss, with no depth-dependent constant hidden in the statement. -/
theorem cmp99SourceGeneratedCanonicalFullComplexA_add_le_div_pow
    (d M base steps : ℕ) [NeZero d] [NeZero M] :
    cmp99SourceGeneratedCanonicalFullComplexA d M (base + steps) ≤
      cmp99SourceGeneratedCanonicalFullComplexA d M base /
        (2 : ℝ) ^ steps := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      calc
        cmp99SourceGeneratedCanonicalFullComplexA d M
            (base + (steps + 1)) =
          cmp99SourceGeneratedCanonicalFullComplexA d M
            ((base + steps) + 1) := by simp [Nat.add_assoc]
        _ ≤ cmp99SourceGeneratedCanonicalFullComplexA d M
              (base + steps) / 2 :=
          cmp99SourceGeneratedCanonicalFullComplexA_succ_le_half
            d M (base + steps)
        _ ≤ (cmp99SourceGeneratedCanonicalFullComplexA d M base /
              (2 : ℝ) ^ steps) / 2 := by linarith
        _ = cmp99SourceGeneratedCanonicalFullComplexA d M base /
              (2 : ℝ) ^ (steps + 1) := by
          rw [pow_succ]
          ring

/-- The generated full-complex coefficient has no positive lower floor
uniform in depth.  This is the terminal no-go for identifying it with the
positive source coefficient `a_j` without an additional dictionary. -/
theorem cmp99SourceGeneratedCanonicalFullComplexA_eventually_lt
    (d M : ℕ) [NeZero d] [NeZero M]
    {floor : ℝ} (hfloor : 0 < floor) :
    ∃ depth,
      cmp99SourceGeneratedCanonicalFullComplexA d M depth < floor := by
  let A0 := cmp99SourceGeneratedCanonicalFullComplexA d M 0
  have hA0 : 0 < A0 := by
    dsimp [A0, cmp99SourceGeneratedCanonicalFullComplexA]
    exact cmp99SourceGeneratedFullComplexA_pos_succ d M 0
      (cmp99SourceGeneratedFullComplexSpacing_pos M 1)
  obtain ⟨steps, hsteps⟩ := exists_pow_lt_of_lt_one
    (div_pos hfloor hA0) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨steps, (cmp99SourceGeneratedCanonicalFullComplexA_add_le_div_pow
    d M 0 steps).trans_lt ?_⟩
  have hmul := mul_lt_mul_of_pos_left hsteps hA0
  have hcancel : A0 * (floor / A0) = floor := by
    field_simp [ne_of_gt hA0]
  rw [hcancel] at hmul
  simpa [A0, div_eq_mul_inv] using hmul

/-- The source coefficient and the current Poincare-generated full-complex
coefficient cannot agree at every depth: eventually the generated coefficient
lies strictly below the positive CMP85 source floor, while the source flow
stays above it. -/
theorem exists_cmp99SourceGeneratedCanonicalFullComplexA_lt_massParameter
    (d M : ℕ) [NeZero d] [NeZero M]
    {a : ℝ} (ha : 0 < a) (hM : 1 < M) :
    ∃ depth,
      cmp99SourceGeneratedCanonicalFullComplexA d M depth <
        cmp99SourceMassParameter a (M : ℝ) depth := by
  have hMreal : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hfloor :
      0 < cmp85Eq215SourceAveragingCoefficientFloor a (M : ℝ) :=
    cmp85Eq215SourceAveragingCoefficientFloor_pos ha hMreal
  obtain ⟨depth, hgenerated⟩ :=
    cmp99SourceGeneratedCanonicalFullComplexA_eventually_lt
      d M hfloor
  exact ⟨depth, hgenerated.trans_le
    (cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter
      ha hMreal depth)⟩

end

end YangMills.RG
