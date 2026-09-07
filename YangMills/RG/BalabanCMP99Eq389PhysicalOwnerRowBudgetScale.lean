/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389SourceLocalizedDefectOwnerWeightedSup

/-!
# Exact large-block scale of the physical CMP99 owner row

Cold GitHub Actions run `31216957809` compiled this module from source
checkpoint `c4a33843f9081d537c61d157a47f94be699a77aa` without restoring or
saving `.lake/build`; its audit found exactly
`[propext, Classical.choice, Quot.sound]` in all five declarations.

This module exposes the exact `K` dependence of the already source-localized
CMP99 (3.89) owner-row budget.  For fixed Green constants `B0`, `delta0` and
reserved rate, the two first-order species contribute one common `K^-1`
coefficient and the cutoff-Laplacian species contributes one `K^-2`
coefficient.  The owner-shell sum is paid exactly once.

The final existence lemma is scalar compatibility only.  It does not produce
one family of physical Green certificates with `B0` and `delta0` uniform as
`K` varies, and it does not discharge the separate CMP99 Theorem-3.15
smallness condition coupling the printed large parameter to `alpha_0`.
Consequently it does not attain window 15, discharge rows 23--24, or inhabit
a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

variable {L K : ℕ} [NeZero L] [NeZero K]

/-- The complete numerator of the two physical `K^-1` species before the
owner-shell conversion.  The first and generated-mass mechanisms remain
separate inside the displayed sum. -/
noncomputable def cmp99Eq389PhysicalOwnerRowLeadingNumerator
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (epsilon B0 delta0 rate : ℝ) : ℝ :=
  16 *
    (4 * (8 * B0 * P.derivBound) * (1 + Real.exp delta0) +
      |cmp99SourceGeneratedPhysicalMass 4 L (depth + 1) 1 epsilon| *
        ((cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) *
          (8 * P.derivBound * (B0 * (L ^ (depth + 1) : ℝ) ^ 2)))) *
    cmp99OmegaSiteExpSumBound (delta0 - rate)

/-- The complete numerator of the physical `K^-2` cutoff-Laplacian species,
including the one-time owner-shell conversion. -/
noncomputable def cmp99Eq389PhysicalOwnerRowQuadraticNumerator
    (P : CMP95SourceSmoothPartitionProfile)
    (B0 delta0 rate : ℝ) : ℝ :=
  16 * (12 * B0 * P.secondDerivBound) *
    cmp99OmegaSiteExpSumBound (delta0 - rate)

/-- Exact scale decomposition of the literal physical owner-row budget.

The dominant term is `K^-1`; `K^-2` belongs only to the second species.  The
shell factor occurs in the two numerators once, not once per Neumann power. -/
theorem cmp99Eq389SourceLocalizedRegionalDefectOwnerRowBudget_eq_scale
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (epsilon B0 delta0 rate : ℝ) :
    cmp99Eq389SourceLocalizedRegionalDefectOwnerRowBudget
        (L := L) (K := K) P depth epsilon B0 delta0 rate =
      cmp99Eq389PhysicalOwnerRowLeadingNumerator
          (L := L) P depth epsilon B0 delta0 rate / (K : ℝ) +
        cmp99Eq389PhysicalOwnerRowQuadraticNumerator
          P B0 delta0 rate / (K : ℝ) ^ 2 := by
  unfold cmp99Eq389SourceLocalizedRegionalDefectOwnerRowBudget
    cmp99Eq389SourceLocalizedThreeSpeciesBudget
    cmp99Eq389SignedCovariantLinkSourceBudget
    cmp99Eq389SignedCutoffLaplacianSourceBudget
    cmp99Eq389GeneratedMassSourceBudget
    cmp99Eq389PhysicalOwnerRowLeadingNumerator
    cmp99Eq389PhysicalOwnerRowQuadraticNumerator
  ring

/-- Both physical scale numerators are nonnegative once the Green amplitude
`B0` is nonnegative. -/
theorem cmp99Eq389PhysicalOwnerRowNumerators_nonneg
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (epsilon delta0 rate : ℝ) {B0 : ℝ} (hB0 : 0 ≤ B0) :
    0 ≤ cmp99Eq389PhysicalOwnerRowLeadingNumerator
        (L := L) P depth epsilon B0 delta0 rate ∧
      0 ≤ cmp99Eq389PhysicalOwnerRowQuadraticNumerator
        P B0 delta0 rate := by
  have hS : 0 ≤ cmp99OmegaSiteExpSumBound (delta0 - rate) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hweight :
      0 ≤ (cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) :=
    pow_nonneg (cmp99SourceBlockAverageWeight_nonneg L 4) _
  have hfirst :
      0 ≤ 4 * (8 * B0 * P.derivBound) * (1 + Real.exp delta0) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg (by norm_num) hB0)
          P.derivBound_nonneg))
      (add_nonneg zero_le_one (Real.exp_pos _).le)
  have hthird :
      0 ≤ |cmp99SourceGeneratedPhysicalMass 4 L (depth + 1) 1 epsilon| *
        ((cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) *
          (8 * P.derivBound * (B0 * (L ^ (depth + 1) : ℝ) ^ 2))) := by
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg hweight
        (mul_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
          (mul_nonneg hB0 (sq_nonneg _))))
  constructor
  · unfold cmp99Eq389PhysicalOwnerRowLeadingNumerator
    exact mul_nonneg
      (mul_nonneg (by norm_num) (add_nonneg hfirst hthird)) hS
  · unfold cmp99Eq389PhysicalOwnerRowQuadraticNumerator
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg (by norm_num) hB0)
          P.secondDerivBound_nonneg)) hS

/-- For a fixed leading coefficient and a nonnegative quadratic coefficient,
the literal mixed `K^-1 + K^-2` shape is below one for a sufficiently large
integer `K`.

This theorem contains no physical data and deliberately does not assert that
the Green constants used to form the coefficients stay uniform for the
chosen `K`. -/
theorem exists_nat_two_le_and_div_add_div_sq_lt_one
    (a₁ a₂ : ℝ) (ha₂ : 0 ≤ a₂) :
    ∃ K : ℕ, 2 ≤ K ∧
      a₁ / (K : ℝ) + a₂ / (K : ℝ) ^ 2 < 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (a₁ + a₂)
  let K := n + 2
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast (by omega : 0 < K)
  have hKone : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ K)
  have hsumK : a₁ + a₂ < (K : ℝ) := by
    dsimp [K]
    push_cast
    linarith
  have ha₂div : a₂ / (K : ℝ) ≤ a₂ := by
    apply (div_le_iff₀ hKpos).2
    nlinarith
  refine ⟨K, by omega, ?_⟩
  rw [show a₁ / (K : ℝ) + a₂ / (K : ℝ) ^ 2 =
      (a₁ + a₂ / (K : ℝ)) / (K : ℝ) by ring]
  apply (div_lt_one hKpos).2
  linarith

end

end YangMills.RG
