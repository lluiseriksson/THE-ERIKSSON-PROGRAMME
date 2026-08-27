import YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusPhysicalBridge
import YangMills.RG.BalabanCMP99SourceUbarRadiusBudget

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# A closed complex radius budget dominates the physical real-slice budget

The complex Eq. (3.37) recursion pays the four-path envelope and the
non-unitary inverse loss.  On a nonnegative comparison radius these constants
dominate the real physical `Ubar` constants.  Consequently the one closed
complex budget also constructs the physical radius chain needed to identify
the real slice of the perturbed tower.  No second per-scale family or freely
chosen radius chain is accepted.
-/

namespace YangMills.RG

noncomputable section

private theorem d_mul_m_sub_one_ne_zero
    {d M : ℕ} (hd : 2 ≤ d) (hM : 2 ≤ M) :
    d * (M - 1) ≠ 0 :=
  Nat.mul_ne_zero (by omega) (by omega)

/-- The literal real `Ubar` deviation coefficient is bounded by the complex
four-path coefficient. -/
theorem cmp99SourceUbarDeviationCoefficient_le_complexClosed
    (d M : ℕ) (hd : 2 ≤ d) (hM : 2 ≤ M) {R : ℝ} (hR : 0 ≤ R) :
    cmp99SourceUbarDeviationCoefficient d M ≤
      cmp99ComplexClosedRadiusDeviationCoefficient (d * (M - 1)) R := by
  let L := d * (M - 1)
  let F := (1 + R) ^ L
  have hM_le : M ≤ d * (M - 1) := by
    calc
      M ≤ 2 * (M - 1) := by omega
      _ ≤ d * (M - 1) := Nat.mul_le_mul_right (M - 1) hd
  have hLnat : 3 * d * (M - 1) + M ≤ 4 * L := by
    dsimp only [L]
    calc
      3 * d * (M - 1) + M ≤
          3 * d * (M - 1) + d * (M - 1) :=
        Nat.add_le_add_left hM_le _
      _ = 4 * (d * (M - 1)) := by ring
  have hsource :
      cmp99SourceUbarDeviationCoefficient d M ≤ 4 * (L : ℝ) := by
    unfold cmp99SourceUbarDeviationCoefficient
    exact_mod_cast hLnat
  have hF : 1 ≤ F := by
    dsimp only [F]
    exact one_le_pow₀ (by linarith)
  have hsum : 4 ≤ F ^ 4 + F ^ 3 + F ^ 2 + F := by
    have hF2 : 1 ≤ F ^ 2 := one_le_pow₀ hF
    have hF3 : 1 ≤ F ^ 3 := one_le_pow₀ hF
    have hF4 : 1 ≤ F ^ 4 := one_le_pow₀ hF
    linarith
  calc
    cmp99SourceUbarDeviationCoefficient d M ≤ 4 * (L : ℝ) := hsource
    _ ≤ (L : ℝ) * (F ^ 4 + F ^ 3 + F ^ 2 + F) := by
      have hL0 : 0 ≤ (L : ℝ) := by positivity
      nlinarith
    _ = cmp99ComplexClosedRadiusDeviationCoefficient L R := by
      rfl

/-- The conservative real growth factor is bounded by the complex growth
factor, including the all-orientation inverse loss. -/
theorem cmp99SourceUbarRadiusGrowthFactor_le_complexClosed
    (d M : ℕ) (hd : 2 ≤ d) (hM : 2 ≤ M) {R : ℝ} (hR : 0 ≤ R) :
    cmp99SourceUbarRadiusGrowthFactor d M ≤
      cmp99ComplexClosedRadiusGrowthFactor (d * (M - 1)) M R := by
  let Cs := cmp99SourceUbarDeviationCoefficient d M
  let Cc := cmp99ComplexClosedRadiusDeviationCoefficient (d * (M - 1)) R
  let A := 4 * Cc + (M : ℝ)
  let F := (1 + R) ^ M
  have hC : Cs ≤ Cc :=
    cmp99SourceUbarDeviationCoefficient_le_complexClosed d M hd hM hR
  have hCc0 : 0 ≤ Cc := by
    dsimp only [Cc, cmp99ComplexClosedRadiusDeviationCoefficient,
      cmp99ComplexClosedRadiusFactorEnvelope]
    positivity
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hF : 1 ≤ F := by
    dsimp only [F]
    exact one_le_pow₀ (by linarith)
  have hAF : A ≤ A * F := by
    nlinarith [mul_le_mul_of_nonneg_left hF hA0]
  calc
    cmp99SourceUbarRadiusGrowthFactor d M = 4 * Cs + (M : ℝ) := rfl
    _ ≤ A := by dsimp only [A]; linarith
    _ ≤ 2 * (A * F) := by nlinarith
    _ = 2 * cmp99ComplexClosedRadiusLinkCoefficient
        (d * (M - 1)) M R := by rfl
    _ ≤ cmp99ComplexClosedRadiusGrowthFactor (d * (M - 1)) M R := by
      exact le_max_right _ _

/-- The single closed complex budget constructs the closed physical
real-slice budget at the same initial radius. -/
noncomputable def CMP99ComplexClosedRadiusBudget.toSourceUbarClosedBudget
    {d M Nc depth : ℕ} [NeZero M] [NeZero Nc]
    (hd : 2 ≤ d) (hM : 2 ≤ M) {r0 R : ℝ}
    (B : @CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth
      ⟨d_mul_m_sub_one_ne_zero hd hM⟩ inferInstance
      r0 R (cmp99UbarNoWindingThreshold Nc)) :
    CMP99SourceUbarClosedBudget d M Nc depth r0 := by
  letI : NeZero d := ⟨by omega⟩
  letI : NeZero (d * (M - 1)) :=
    ⟨d_mul_m_sub_one_ne_zero hd hM⟩
  let Cs := cmp99SourceUbarDeviationCoefficient d M
  let Ks := cmp99SourceUbarRadiusGrowthFactor d M
  let Cc := cmp99ComplexClosedRadiusDeviationCoefficient (d * (M - 1)) R
  let Kc := cmp99ComplexClosedRadiusGrowthFactor (d * (M - 1)) M R
  have hCc : 0 < Cc :=
    cmp99ComplexClosedRadiusDeviationCoefficient_pos
      (d * (M - 1)) B.R_nonneg
  have hCs : 0 ≤ Cs := cmp99SourceUbarDeviationCoefficient_nonneg d M
  have hKs : 0 ≤ Ks :=
    (one_le_cmp99SourceUbarRadiusGrowthFactor d M).trans' zero_le_one
  have hC : Cs ≤ Cc :=
    cmp99SourceUbarDeviationCoefficient_le_complexClosed
      d M hd hM B.R_nonneg
  have hK : Ks ≤ Kc :=
    cmp99SourceUbarRadiusGrowthFactor_le_complexClosed
      d M hd hM B.R_nonneg
  have hpow : Ks ^ depth ≤ Kc ^ depth :=
    pow_le_pow_left₀ hKs hK depth
  have hmajorant : Cs * Ks ^ depth * r0 ≤ Cc * Kc ^ depth * r0 := by
    have hcoeffPower : Cs * Ks ^ depth ≤ Cc * Kc ^ depth :=
      mul_le_mul hC hpow (pow_nonneg hKs depth) hCc.le
    exact mul_le_mul_of_nonneg_right hcoeffPower B.r0_nonneg
  have hterminalDiv : Kc ^ depth * r0 <
      min (cmp99UbarNoWindingThreshold Nc) (1 / 4 : ℝ) / Cc := by
    exact B.terminal_small.trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hterminalComplex : Cc * Kc ^ depth * r0 <
      min (cmp99UbarNoWindingThreshold Nc) (1 / 4 : ℝ) := by
    rw [lt_div_iff₀ hCc] at hterminalDiv
    nlinarith
  exact {
    epsilon_nonneg := B.r0_nonneg
    terminal_small := hmajorant.trans_lt hterminalComplex }

/-- The same complex budget therefore constructs the recursive physical
radius proof consumed by the compact-real-slice tower. -/
noncomputable def CMP99ComplexClosedRadiusBudget.toSourceUbarRadiusChain
    {d M Nc depth : ℕ} [NeZero M] [NeZero Nc]
    (hd : 2 ≤ d) (hM : 2 ≤ M) {r0 R : ℝ}
    (B : @CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth
      ⟨d_mul_m_sub_one_ne_zero hd hM⟩ inferInstance
      r0 R (cmp99UbarNoWindingThreshold Nc)) :
    letI : NeZero d := ⟨by omega⟩
    CMP99SourceUbarRadiusChain d M Nc depth r0 := by
  letI : NeZero d := ⟨by omega⟩
  letI : NeZero (d * (M - 1)) :=
    ⟨d_mul_m_sub_one_ne_zero hd hM⟩
  exact (B.toSourceUbarClosedBudget hd hM).toRadiusChain

end

end YangMills.RG
