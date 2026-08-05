/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedRegionalDefectContraction
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalLargeBlockCutoff

/-!
# PRE-VALIDATION: auxiliary separated-scale Schur budget

The source below is present, but its `.olean` has not yet been materialized
and its results have not yet been verified by the Lean compiler.

This module records the algebra obtained by propagating the independent
large-block factor through the old CT + Schur scalar budget.  The Green rate,
coercivity and shell sums depend on the fixed RG ratio `L`; the cutoff budget
contributes the only `K^-1` factor.  Consequently this auxiliary majorant is
exactly `numerator / K` and is below one for a sufficiently large integer
`K`.

This is **not** the accepted physical repair of step 7.  The physical producer
must formalize the direct `O(K^-1)` estimate printed in CMP99 (3.89), with the
gain present before the layer sums and with the overlap `16` independent of
`K`.  No operator is constructed here, and these auxiliary scalar theorems
must not be used to claim attainment of window 15.
-/

namespace YangMills.RG

noncomputable section

/-- One separated-scale regional correction amplitude before paying the
source overlap. -/
noncomputable def
    cmp99SourceSeparatedGeneratedPhysicalRegionalCorrectionAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let rate := cmp99SourceGeneratedPhysicalRegionalGreenRate
    L depth spacing epsilon
  let c := cmp99SourceGeneratedCoercivity
    4 L (depth + 1) spacing epsilon
  cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget
      P L K depth spacing epsilon rate *
    (2 / c) * cmp99OmegaSiteExpSumBound (rate / 2)

/-- Exponential amplitude after paying the source overlap exactly once. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalRegionalDefectAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  16 * cmp99SourceSeparatedGeneratedPhysicalRegionalCorrectionAmplitude
    P L K depth spacing epsilon

/-- The defect rate is inherited from the fixed RG tower and does not depend
on the independent large-block parameter. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalRegionalDefectRate
    (L depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalRegionalGreenRate L depth spacing epsilon / 2

/-- Complete scalar Schur budget after the second exponential shell sum. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceSeparatedGeneratedPhysicalRegionalDefectAmplitude
      P L K depth spacing epsilon *
    cmp99OmegaSiteExpSumBound
      (cmp99SourceSeparatedGeneratedPhysicalRegionalDefectRate
        L depth spacing epsilon)

/-- Numerator of the complete separated-scale Schur budget.  It is independent
of `K`. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalRegionalDefectNumerator
    (P : CMP95SourceSmoothPartitionProfile)
    (L depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let rate := cmp99SourceGeneratedPhysicalRegionalGreenRate
    L depth spacing epsilon
  let c := cmp99SourceGeneratedCoercivity
    4 L (depth + 1) spacing epsilon
  16 *
    (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffNumerator
        P L depth spacing epsilon rate *
      (2 / c) * cmp99OmegaSiteExpSumBound (rate / 2)) *
    cmp99OmegaSiteExpSumBound (rate / 2)

/-- The complete separated scalar budget carries exactly one `K^-1`. -/
theorem cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget_eq
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) (spacing epsilon : ℝ) :
    cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget
        P L K depth spacing epsilon =
      cmp99SourceSeparatedGeneratedPhysicalRegionalDefectNumerator
        P L depth spacing epsilon / (K : ℝ) := by
  unfold cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget
    cmp99SourceSeparatedGeneratedPhysicalRegionalDefectAmplitude
    cmp99SourceSeparatedGeneratedPhysicalRegionalCorrectionAmplitude
    cmp99SourceSeparatedGeneratedPhysicalRegionalDefectRate
    cmp99SourceSeparatedGeneratedPhysicalRegionalDefectNumerator
  simp only [cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget_eq]
  ring

/-- The separated scalar Schur majorant is genuinely attainable for every
fixed RG tower and background parameter set.  The theorem chooses `K`
internally; it is not yet a norm estimate for the regional defect operator. -/
theorem exists_cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget_lt_one
    (P : CMP95SourceSmoothPartitionProfile)
    (L depth : ℕ) [NeZero L] {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :
    ∃ K : ℕ, 2 ≤ K ∧
      cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget
        P L K depth spacing epsilon < 1 := by
  have _hcoercivity :
      0 < cmp99SourceGeneratedCoercivity
        4 L (depth + 1) spacing epsilon :=
    cmp99SourceGeneratedCoercivity_pos 4 L depth hspacing hsmall
  obtain ⟨n, hn⟩ := exists_nat_gt
    (cmp99SourceSeparatedGeneratedPhysicalRegionalDefectNumerator
      P L depth spacing epsilon)
  let K := n + 2
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast (by omega : 0 < K)
  have hnumK :
      cmp99SourceSeparatedGeneratedPhysicalRegionalDefectNumerator
          P L depth spacing epsilon < (K : ℝ) := by
    dsimp [K]
    push_cast
    linarith
  refine ⟨K, by omega, ?_⟩
  rw [cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget_eq]
  exact (div_lt_one hKpos).2 hnumK

/-- The diagonal `K = L` reduces to the previously sealed scalar budget. -/
theorem cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget_self
    (P : CMP95SourceSmoothPartitionProfile)
    (L depth : ℕ) (spacing epsilon : ℝ) :
    cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget
        P L L depth spacing epsilon =
      cmp99SourceGeneratedPhysicalRegionalDefectBudget
        P L depth spacing epsilon := by
  unfold cmp99SourceSeparatedGeneratedPhysicalRegionalDefectBudget
    cmp99SourceSeparatedGeneratedPhysicalRegionalDefectAmplitude
    cmp99SourceSeparatedGeneratedPhysicalRegionalCorrectionAmplitude
    cmp99SourceSeparatedGeneratedPhysicalRegionalDefectRate
    cmp99SourceGeneratedPhysicalRegionalDefectBudget
    cmp99SourceGeneratedPhysicalRegionalDefectAmplitude
    cmp99SourceGeneratedPhysicalRegionalCorrectionAmplitude
    cmp99SourceGeneratedPhysicalRegionalDefectRate
  simp only [cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget_self]

end

end YangMills.RG
