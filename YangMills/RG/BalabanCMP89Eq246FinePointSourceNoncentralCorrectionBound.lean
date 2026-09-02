/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246FinePointSourceMomentBound

/-!
# PRE-VALIDATION: noncentral rank-one correction below CMP89 (2.46)

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

This leaf bounds only the rank-one correction in a noncentral component of
the fine-point-source solution.  It deliberately does not bound the bare
diagonal term `source m / fine m`, whose alias sum carries the visible
inverse-Laplacian scale `O((L^j)^2)`.
-/

namespace YangMills.RG

noncomputable section

/-- Scale-uniform coefficient for one noncentral rank-one correction. -/
def cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound
    (a rho : ℝ) : ℝ :=
  |a| * cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
    cmp89Eq246FinePointSourceMomentAmplitudeBound a rho

/-- The rank-one correction is summable with the existing source weight.
The unsmoothed diagonal branch is intentionally absent from the statement. -/
theorem norm_cmp89Eq246FinePointSourceNoncentralCorrection_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (sourceEndpoint : Fin 4 → ℝ)
    (m : CMP89Eq246AliasIndex 4 L j)
    (hm : m ≠ cmp89Eq249CentralAliasIndex 4 L j) :
    ‖(a : ℂ) * cmp89Eq246EntireAliasAverageColumn 4 L j z m *
          cmp89Eq246StabilizedFinePointSourceSolutionMoment
            4 L j mass a sourceEndpoint z /
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z m‖ ≤
      cmp89Eq251ContourPhaseGrowth rho sourceEndpoint *
        (cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound a rho *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m.1) := by
  have hm0 : m.1 ≠ cmp89Eq249ZeroAlias 4 := by
    intro hz
    apply hm
    apply Subtype.ext
    exact hz
  let qbound := cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho
  let weight := cmp89Eq251MultidimensionalAliasWeight
    (cmp89Eq251AliasSeriesExponent 4 (-1)) m.1
  let growth := cmp89Eq251ContourPhaseGrowth rho sourceEndpoint
  let mbound := cmp89Eq246FinePointSourceMomentAmplitudeBound a rho
  have hquot :
      ‖cmp89Eq246EntireAliasAverageColumn 4 L j z m /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z m‖ ≤
        qbound * weight := by
    simpa [qbound, weight, cmp89Eq246EntireAliasAverageColumn,
      cmp89Eq246EntireAliasFineSymbol] using
      (norm_cmp89Eq248ComplexNoncentralGreenQuotient_le_sourceWeight_draft
        (N := L ^ j) (mass := mass)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
        hrho hradius m.2 hm0 hp hreal himag hamplitude)
  have hmoment :
      ‖cmp89Eq246StabilizedFinePointSourceSolutionMoment
          4 L j mass a sourceEndpoint z‖ ≤ growth * mbound := by
    simpa [growth, mbound] using
      (norm_cmp89Eq246StabilizedFinePointSourceSolutionMoment_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hwindow hamplitude hp hreal himag
        sourceEndpoint)
  have hqbound : 0 ≤ qbound := by
    dsimp [qbound, cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
      cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hweight : 0 ≤ weight := by
    exact cmp89Eq251MultidimensionalAliasWeight_nonneg _ m.1
  have hleft :
      |a| * ‖cmp89Eq246EntireAliasAverageColumn 4 L j z m /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z m‖ ≤
        |a| * (qbound * weight) :=
    mul_le_mul_of_nonneg_left hquot (abs_nonneg a)
  have hleftNonneg : 0 ≤ |a| * (qbound * weight) :=
    mul_nonneg (abs_nonneg a) (mul_nonneg hqbound hweight)
  have hmul := mul_le_mul hleft hmoment (norm_nonneg _) hleftNonneg
  have hreassoc :
      (a : ℂ) * cmp89Eq246EntireAliasAverageColumn 4 L j z m *
          cmp89Eq246StabilizedFinePointSourceSolutionMoment
            4 L j mass a sourceEndpoint z /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z m =
        (a : ℂ) *
          (cmp89Eq246EntireAliasAverageColumn 4 L j z m /
            cmp89Eq246EntireAliasFineSymbol 4 L j mass z m) *
          cmp89Eq246StabilizedFinePointSourceSolutionMoment
            4 L j mass a sourceEndpoint z := by
    simp [div_eq_mul_inv]
    ring
  rw [hreassoc, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simpa [qbound, weight, growth, mbound,
    cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound,
    mul_assoc, mul_left_comm, mul_comm] using hmul

end

end YangMills.RG
