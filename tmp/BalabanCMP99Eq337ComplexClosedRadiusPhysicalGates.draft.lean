import tmp.BalabanCMP99Eq337ComplexClosedRadiusPhysicalBridge.draft

/-!
PRE-VALIDATION: scratch scalar-gate producer. This file has no materialized
`.olean` and no compiler or axiom-oracle verdict.

It derives every flowing no-winding, logarithmic and positive-link gate from
one `CMP99ComplexClosedRadiusBudget`. No per-scale gate is caller data.
-/

namespace YangMills.RG

noncomputable section

namespace CMP99ComplexClosedRadiusBudget

variable {L M depth : ℕ} [NeZero L] [NeZero M]
variable {r0 R threshold : ℝ}

/-- Every nonterminal generated deviation lies in the quarter-radius regime
used by the compiled logarithm/exponential estimate. -/
theorem deviation_lt_quarter
    (B : CMP99ComplexClosedRadiusBudget L M depth r0 R threshold)
    {k : ℕ} (hk : k < depth) :
    cmp99ComplexClosedRadiusDeviation L
        (cmp99ComplexClosedRadiusAt L M r0 k) < (1 / 4 : ℝ) := by
  let C := cmp99ComplexClosedRadiusDeviationCoefficient L R
  let K := cmp99ComplexClosedRadiusGrowthFactor L M R
  have hC : 0 < C :=
    cmp99ComplexClosedRadiusDeviationCoefficient_pos L B.R_nonneg
  have hK : 1 ≤ K := one_le_cmp99ComplexClosedRadiusGrowthFactor L M R
  have hr := (B.radiusAt_nonneg_and_le (Nat.le_of_lt hk)).2
  have hr_nonneg := (B.radiusAt_nonneg_and_le (Nat.le_of_lt hk)).1
  have hpow : K ^ k ≤ K ^ depth :=
    pow_le_pow_right₀ hK (Nat.le_of_lt hk)
  have hr_terminal :
      cmp99ComplexClosedRadiusAt L M r0 k ≤ K ^ depth * r0 :=
    hr.trans (mul_le_mul_of_nonneg_right hpow B.r0_nonneg)
  have hterminalR : K ^ depth * r0 < R :=
    lt_of_lt_of_le B.terminal_small (min_le_left _ _)
  have hrR : cmp99ComplexClosedRadiusAt L M r0 k ≤ R :=
    hr_terminal.trans hterminalR.le
  have hratio : K ^ depth * r0 < min threshold (1 / 4 : ℝ) / C :=
    lt_of_lt_of_le B.terminal_small
      ((min_le_right _ _).trans (min_le_left _ _))
  have hmul : C * (K ^ depth * r0) < min threshold (1 / 4 : ℝ) := by
    have h := (lt_div_iff₀ hC).mp hratio
    nlinarith
  calc
    cmp99ComplexClosedRadiusDeviation L
        (cmp99ComplexClosedRadiusAt L M r0 k) ≤
        C * cmp99ComplexClosedRadiusAt L M r0 k := by
          exact cmp99ComplexClosedRadiusDeviation_le_coefficient_mul
            L hr_nonneg hrR
    _ ≤ C * (K ^ depth * r0) :=
      mul_le_mul_of_nonneg_left hr_terminal hC.le
    _ < min threshold (1 / 4 : ℝ) := hmul
    _ ≤ (1 / 4 : ℝ) := min_le_right _ _

/-- Every nonterminal positive-edge radius is strictly below one half. -/
theorem nextLink_lt_half
    (B : CMP99ComplexClosedRadiusBudget L M depth r0 R threshold)
    {k : ℕ} (hk : k < depth) :
    cmp99ComplexClosedRadiusNextLink L M
        (cmp99ComplexClosedRadiusAt L M r0 k) < (1 / 2 : ℝ) := by
  let Q := cmp99ComplexClosedRadiusLinkCoefficient L M R
  let K := cmp99ComplexClosedRadiusGrowthFactor L M R
  have hQ : 0 < Q :=
    cmp99ComplexClosedRadiusLinkCoefficient_pos L M B.R_nonneg
  have hK : 1 ≤ K := one_le_cmp99ComplexClosedRadiusGrowthFactor L M R
  obtain ⟨hr_nonneg, hr⟩ := B.radiusAt_nonneg_and_le (Nat.le_of_lt hk)
  have hpow : K ^ k ≤ K ^ depth :=
    pow_le_pow_right₀ hK (Nat.le_of_lt hk)
  have hr_terminal :
      cmp99ComplexClosedRadiusAt L M r0 k ≤ K ^ depth * r0 :=
    hr.trans (mul_le_mul_of_nonneg_right hpow B.r0_nonneg)
  have hterminalR : K ^ depth * r0 < R :=
    lt_of_lt_of_le B.terminal_small (min_le_left _ _)
  have hrR : cmp99ComplexClosedRadiusAt L M r0 k ≤ R :=
    hr_terminal.trans hterminalR.le
  have hterminalHalfRatio : K ^ depth * r0 < (1 / 2 : ℝ) / Q :=
    lt_of_lt_of_le B.terminal_small
      ((min_le_right _ _).trans (min_le_right _ _))
  have hterminalHalf : Q * (K ^ depth * r0) < (1 / 2 : ℝ) := by
    have h := (lt_div_iff₀ hQ).mp hterminalHalfRatio
    nlinarith
  calc
    cmp99ComplexClosedRadiusNextLink L M
        (cmp99ComplexClosedRadiusAt L M r0 k) ≤
        Q * cmp99ComplexClosedRadiusAt L M r0 k := by
          exact cmp99ComplexClosedRadiusNextLink_le_coefficient_mul
            L M hr_nonneg hrR (B.deviation_lt_quarter hk)
    _ ≤ Q * (K ^ depth * r0) :=
      mul_le_mul_of_nonneg_left hr_terminal hQ.le
    _ < (1 / 2 : ℝ) := hterminalHalf

/-- The proof-free logarithmic radius is strictly below one at every
nonterminal scale. -/
theorem closedLog_lt_one
    (B : CMP99ComplexClosedRadiusBudget L M depth r0 R threshold)
    {k : ℕ} (hk : k < depth) :
    cmp99ComplexClosedRadiusLog
      (cmp99ComplexClosedRadiusDeviation L
        (cmp99ComplexClosedRadiusAt L M r0 k)) < 1 := by
  let delta := cmp99ComplexClosedRadiusDeviation L
    (cmp99ComplexClosedRadiusAt L M r0 k)
  have hr_nonneg := (B.radiusAt_nonneg_and_le (Nat.le_of_lt hk)).1
  have hdelta0 : 0 ≤ delta :=
    cmp99ComplexClosedRadiusDeviation_nonneg L hr_nonneg
  have hdeltaQuarter : delta < (1 / 4 : ℝ) := B.deviation_lt_quarter hk
  have hden : 0 < 1 - delta := by linarith
  unfold cmp99ComplexClosedRadiusLog
  exact (div_lt_iff₀ hden).2 (by nlinarith)

/-- The literal physical no-winding record produced from the closed budget
has logarithmic radius below one. -/
theorem physicalLog_lt_one
    {d Nc : ℕ} [NeZero Nc] [NeZero (d * (M - 1))]
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth r0 R (cmp99UbarNoWindingThreshold Nc))
    {k : ℕ} (hk : k < depth) :
    cmp99UbarLogRadius
      (cmp99ComplexClosedRadiusPhysicalNoWindingBudget
        d M Nc depth r0 R B k hk) < 1 := by
  simpa [cmp99ComplexClosedRadiusPhysicalNoWindingBudget,
    cmp99UbarLogRadius, cmp99ComplexClosedRadiusLog,
    cmp99SourceComplexUbarNoWindingBudget_delta,
    cmp99ComplexClosedRadiusDeviation_eq_eq337Uniform] using
      B.closedLog_lt_one hk

/-- The literal physical positive-edge radius produced from the closed
budget is strictly below one. -/
theorem physicalNextLink_lt_one
    {d Nc : ℕ} [NeZero Nc] [NeZero (d * (M - 1))]
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth r0 R (cmp99UbarNoWindingThreshold Nc))
    {k : ℕ} (hk : k < depth) :
    cmp99SourceComplexUbarNextLinkRadius (Nc := Nc) M
      (cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k)
      (cmp99ComplexClosedRadiusPhysicalNoWindingBudget
        d M Nc depth r0 R B k hk) < 1 := by
  have hhalf := B.nextLink_lt_half hk
  have hone :
      cmp99ComplexClosedRadiusNextLink (d * (M - 1)) M
        (cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k) < 1 :=
    hhalf.trans (by norm_num)
  unfold cmp99ComplexClosedRadiusPhysicalNoWindingBudget
  rw [← cmp99ComplexClosedRadiusNextLink_eq_sourceNextLinkRadius
    (Nc := Nc) d M
      (cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k)]
  exact hone

end CMP99ComplexClosedRadiusBudget

end

end YangMills.RG
