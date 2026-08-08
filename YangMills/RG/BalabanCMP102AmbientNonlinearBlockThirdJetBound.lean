/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientExpAverageThirdJetBound
import YangMills.RG.BalabanCMP102AmbientNonlinearBlockFDeriv
import YangMills.RG.BalabanCMP102AmbientNonlinearBlockSourceBudget

/-!
# Third jet of the represented CMP102 nonlinear block

The represented block is the literal ordered product of the exponential
block average and the straight coarse Wilson contour.  This file applies the
quantitative noncommutative Leibniz rule to the two already generated
physical jet families.  No third derivative of the represented product is
accepted from the caller.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102AmbientNonlinearBlockThirdJetMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

local instance cmp102AmbientNonlinearBlockThirdJetCMLSeminormed (n : ℕ) :
    SeminormedAddCommGroup
      (PhysicalAmbientMatrixTangent d (M * N') Nc [×n]→L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousMultilinearMap.seminormedAddCommGroup

/-- One common budget for the value and the positive jets through order
three of the exponential block average. -/
def cmp102SourceExpAverageOrderThreeJetBudget
    (d M : ℕ) (r q : NNReal) : ℝ :=
  max (cmp102SourceExpAverageValueBudget q)
    (cmp102SourceExpAverageThirdJetBudget
      (Nc := Nc) d M r q)

/-- One common budget for every jet through order three of the represented
nonlinear block.  The factor eight is the sum of binomial coefficients in
the worst allowed order. -/
def cmp102SourceAmbientNonlinearBlockThirdJetBudget
    (d M : ℕ) (r q : NNReal) : ℝ :=
  8 * cmp102SourceExpAverageOrderThreeJetBudget
        (Nc := Nc) d M r q *
    cmp102AmbientWilsonLineOrderThreeJetBudget
      (Nc := Nc) r M

theorem cmp102SourceExpAverageOrderThreeJetBudget_nonneg
    (d M : ℕ) (r q : NNReal) :
    0 ≤ cmp102SourceExpAverageOrderThreeJetBudget
      (Nc := Nc) d M r q := by
  exact
    (cmp102SourceExpAverageValueBudget_nonneg q.2).trans
      (le_max_left _ _)

set_option maxHeartbeats 1200000 in
/-- Every jet through order three of the literal represented nonlinear
block is generated from its two physical factors, uniformly in the ambient
periodic volume. -/
theorem norm_iteratedFDeriv_cmp102AmbientNonlinearBlock_le_orderThreeBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r q : NNReal) (hZ : ‖Z‖ < r)
    (hq : (q : ℝ) < 1)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < q)
    (i : ℕ) (hi : i ≤ 3) :
    ‖iteratedFDeriv ℝ i
        (cmp102AmbientNonlinearBlock U b) Z‖ ≤
      cmp102SourceAmbientNonlinearBlockThirdJetBudget
        (Nc := Nc) d M r q := by
  let E := cmp98UbarExpAverage U b
  let C :
      PhysicalAmbientMatrixTangent d (M * N') Nc →
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun W => cmp98AmbientWilsonLineMatrix U W
      (cmp98SourceCoarseBondPath (Nc := Nc) b)
  let BE := cmp102SourceExpAverageOrderThreeJetBudget
    (Nc := Nc) d M r q
  let BC := cmp102AmbientWilsonLineOrderThreeJetBudget
    (Nc := Nc) r M
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1 :=
    fun x hx => (hD x hx).trans hq
  have hEat : ContDiffAt ℝ 3 E Z :=
    (analyticAt_cmp98UbarExpAverage_of_norm_lt_one U b Z hsmall
      ).contDiffAt
  have hCsmooth : ContDiff ℝ 3 C :=
    contDiff_iff_contDiffAt.mpr fun W =>
      (analyticAt_cmp98AmbientWilsonLineMatrix U W
        (cmp98SourceCoarseBondPath (Nc := Nc) b)).contDiffAt
  have hEjets : ∀ j, j ≤ i →
      ‖iteratedFDeriv ℝ j E Z‖ ≤ BE := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      calc
        ‖iteratedFDeriv ℝ 0 E Z‖ = ‖E Z‖ :=
          norm_iteratedFDeriv_zero
        _ ≤ cmp102SourceExpAverageValueBudget q := by
          simpa [E] using
            norm_cmp98UbarExpAverage_le_sourceBudget
              U b Z q.2 hq (fun x hx => (hD x hx).le)
        _ ≤ BE := le_max_left _ _
    · have hj1 : 1 ≤ j := by omega
      exact
        (norm_iteratedFDeriv_cmp98UbarExpAverage_le_sourceThirdJetBudget
          U b Z r q hZ hq hD j hj1 (hj.trans hi)).trans
          (le_max_right _ _)
  have hZpath :
      ∀ e ∈ cmp98SourceCoarseBondPath (Nc := Nc) b,
        ‖Z (physicalBondOfEdge e)‖ < r := by
    intro e he
    exact (norm_physicalAmbientMatrixTangent_apply_le Z _).trans_lt hZ
  have hCjets : ∀ j, j ≤ i →
      ‖iteratedFDeriv ℝ j C Z‖ ≤ BC := by
    intro j hj
    simpa only [C, BC, cmp98SourceCoarseBondPath_length] using
      norm_iteratedFDeriv_cmp98AmbientWilsonLineMatrix_le_orderThreeBudget
        U Z (cmp98SourceCoarseBondPath (Nc := Nc) b) r hZpath
        j (hj.trans hi)
  rcases hEat.contDiffOn
      (m := (3 : WithTop ℕ∞)) le_rfl (by simp) with
    ⟨u, hu, hEu⟩
  rcases mem_nhds_iff.mp hu with
    ⟨s, hsu, hsOpen, hZs⟩
  have hEs : ContDiffOn ℝ 3 E s := hEu.mono hsu
  have hsUnique : UniqueDiffOn ℝ s := hsOpen.uniqueDiffOn
  have hLeibniz :=
    (ContinuousLinearMap.mul ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ)
      ).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
        hEs hCsmooth.contDiffOn hsUnique hZs (n := i)
        (WithTop.coe_le_coe.mpr
          (WithTop.coe_le_coe.mpr hi))
        (norm_cmp102AmbientMatrixMulCLM_le_one (Nc := Nc))
  change
    ‖iteratedFDerivWithin ℝ i
        (fun W => E W * C W) s Z‖ ≤ _ at hLeibniz
  have hcombined :
      ContDiffAt ℝ 3 (fun W => E W * C W) Z :=
    hEat.mul hCsmooth.contDiffAt
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    hsUnique (hcombined.of_le
      (WithTop.coe_le_coe.mpr
        (WithTop.coe_le_coe.mpr hi))) hZs] at hLeibniz
  have hEEq : ∀ j, j ≤ i →
      iteratedFDerivWithin ℝ j E s Z =
        iteratedFDeriv ℝ j E Z := by
    intro j hj
    exact iteratedFDerivWithin_eq_iteratedFDeriv
      hsUnique
      (hEat.of_le
        (WithTop.coe_le_coe.mpr
          (WithTop.coe_le_coe.mpr (hj.trans hi)))) hZs
  have hCEq : ∀ j, j ≤ i →
      iteratedFDerivWithin ℝ j C s Z =
        iteratedFDeriv ℝ j C Z := by
    intro j hj
    exact iteratedFDerivWithin_eq_iteratedFDeriv
      hsUnique
      (hCsmooth.contDiffAt.of_le
        (WithTop.coe_le_coe.mpr
          (WithTop.coe_le_coe.mpr (hj.trans hi)))) hZs
  have hBE : 0 ≤ BE :=
    cmp102SourceExpAverageOrderThreeJetBudget_nonneg
      (Nc := Nc) d M r q
  have hBC : 0 ≤ BC :=
    cmp102AmbientWilsonLineOrderThreeJetBudget_nonneg
      (Nc := Nc) r M
  change
    ‖iteratedFDeriv ℝ i (fun W => E W * C W) Z‖ ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) *
            ‖iteratedFDerivWithin ℝ j E s Z‖ *
            ‖iteratedFDerivWithin ℝ (i - j) C s Z‖ :=
      hLeibniz
    _ ≤ ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) * BE * BC := by
      apply Finset.sum_le_sum
      intro j hj
      have hji : j ≤ i :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hsub : i - j ≤ i := Nat.sub_le i j
      rw [hEEq j hji, hCEq (i - j) hsub]
      calc
        (i.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j E Z‖ *
              ‖iteratedFDeriv ℝ (i - j) C Z‖
            ≤ (i.choose j : ℝ) * BE *
                ‖iteratedFDeriv ℝ (i - j) C Z‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left
                  (hEjets j hji) (Nat.cast_nonneg _))
                (norm_nonneg _)
        _ ≤ (i.choose j : ℝ) * BE * BC := by
              exact mul_le_mul_of_nonneg_left
                (hCjets (i - j) hsub)
                (mul_nonneg (Nat.cast_nonneg _) hBE)
    _ ≤ 8 * BE * BC := by
      have hprod : 0 ≤ BE * BC := mul_nonneg hBE hBC
      interval_cases i <;>
        norm_num [Finset.sum_range_succ] <;>
        nlinarith
    _ = cmp102SourceAmbientNonlinearBlockThirdJetBudget
        (Nc := Nc) d M r q := rfl

/-- The third derivative of the literal represented nonlinear block. -/
theorem norm_iteratedFDeriv_three_cmp102AmbientNonlinearBlock_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r q : NNReal) (hZ : ‖Z‖ < r)
    (hq : (q : ℝ) < 1)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < q) :
    ‖iteratedFDeriv ℝ 3
        (cmp102AmbientNonlinearBlock U b) Z‖ ≤
      cmp102SourceAmbientNonlinearBlockThirdJetBudget
        (Nc := Nc) d M r q :=
  norm_iteratedFDeriv_cmp102AmbientNonlinearBlock_le_orderThreeBudget
    U b Z r q hZ hq hD 3 (by omega)

end

end YangMills.RG
