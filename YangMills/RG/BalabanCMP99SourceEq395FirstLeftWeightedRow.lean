/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395FirstLeftDecay

/-!
# Fixed-rate weighted row of the first left factor in CMP99 equation (3.95)

The ambient exponential estimate is converted to a weighted row at half its
rate by the uniform polynomial shell sum on the complete periodic box.
-/

namespace YangMills.RG
open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

/-- Fixed rate used for the first atom: one half of the already exposed
ambient global-middle rate. -/
noncomputable def cmp99Eq395FirstAtomDecayRate
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 8

/-- Weighted-row amplitude of the exterior-cut global middle. -/
noncomputable def cmp99Eq395PhysicalFirstLeftWeightedRowAmplitude
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon *
    cmp99OmegaSiteExpSumBound
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon)

/-- The full four-dimensional periodic box satisfies the same shell bound as
every active subregion. -/
theorem finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound
    (source : FinBox 4 (2 * Q)) {sigma : ℝ} (hsigma : 0 < sigma) :
    ∑ target : FinBox 4 (2 * Q),
      Real.exp (-(sigma * (finBoxDist target source : ℝ))) ≤
        cmp99OmegaSiteExpSumBound sigma := by
  unfold cmp99OmegaSiteExpSumBound
  have hN : ∀ k,
      ((Finset.univ.filter
        (fun target : FinBox 4 (2 * Q) =>
          finBoxDist target source = k)).card : ℝ) ≤
        (((2 * k + 1) ^ 4 : ℕ) : ℝ) := by
    intro k
    exact_mod_cast (Finset.card_le_card
      (show Finset.univ.filter
          (fun target : FinBox 4 (2 * Q) => finBoxDist target source = k) ⊆
        Finset.univ.filter (fun target => finBoxDist source target ≤ k) by
        intro target htarget
        rw [Finset.mem_filter] at htarget ⊢
        exact ⟨htarget.1, by simpa [finBoxDist_comm] using htarget.2.le⟩)).trans
          (finBoxDist_ball_card_le_two_mul_add_one_pow source k)
  have hsummable : Summable
      (fun k : ℕ => (((2 * k + 1) ^ 4 : ℕ) : ℝ) *
        Real.exp (-sigma * (k : ℝ))) := by
    simpa only [neg_mul] using summable_cmp99OmegaSiteExpSumBound hsigma
  simpa only [neg_mul] using
    (lattice_exp_sum_le_of_shell
      (fun target : FinBox 4 (2 * Q) => finBoxDist target source)
      (σ := sigma) (fun k => (((2 * k + 1) ^ 4 : ℕ) : ℝ))
      hN hsummable)

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 4000 in
set_option maxHeartbeats 12000000 in
/-- The exterior-cut global middle has a fixed-rate weighted-row bound with
no ambient-volume factor. -/
theorem cmp99Eq395PhysicalFirstLeft_weightedRow
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    FinitePiLpTypedWeightedRowKernelBound
      (cmp99Eq395PhysicalFirstLeft hM depth hspacing background budget
        fineSmall hsmall cell)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalFirstLeftWeightedRowAmplitude
        M depth spacing epsilon)
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon) := by
  let theta := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound rate
  let A := cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon
  have htheta : 0 < theta :=
    cmp99SourceGeneratedCombesThomasRate_pos 4 M depth hspacing hsmall
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395FirstAtomDecayRate, theta]
    positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hcut : FinitePiLpTypedExponentialKernelBound
      (cmp99Eq395PhysicalFirstLeft hM depth hspacing background budget
        fineSmall hsmall cell)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      A (theta / 4) :=
    cmp99Eq395PhysicalFirstLeft_exponentialKernelBound
      hM depth hspacing background budget fineSmall hsmall cell
  have hmargin : theta / 4 - rate = rate := by
    dsimp [rate, cmp99Eq395FirstAtomDecayRate, theta]
    ring
  refine ⟨mul_nonneg hcut.1 hS, hrate.le, ?_⟩
  intro source v
  calc
    ∑ target : FinBox 4 (2 * Q),
          Real.exp (rate * (finBoxDist target source : ℝ)) *
            ‖cmp99Eq395PhysicalFirstLeft hM depth hspacing background budget
              fineSmall hsmall cell (singleFinitePiLp source v) target‖
        ≤ ∑ target : FinBox 4 (2 * Q),
            A * Real.exp (-(rate *
              (finBoxDist target source : ℝ))) * ‖v‖ := by
          apply Finset.sum_le_sum
          intro target _
          calc
            Real.exp (rate * (finBoxDist target source : ℝ)) *
                ‖cmp99Eq395PhysicalFirstLeft hM depth hspacing background
                  budget fineSmall hsmall cell
                  (singleFinitePiLp source v) target‖
              ≤ Real.exp (rate * (finBoxDist target source : ℝ)) *
                  (A * Real.exp (-((theta / 4) *
                    (finBoxDist target source : ℝ))) * ‖v‖) :=
                mul_le_mul_of_nonneg_left
                  (hcut.2.2 source target v) (Real.exp_pos _).le
            _ = A * Real.exp (-(rate *
                  (finBoxDist target source : ℝ))) * ‖v‖ := by
                rw [show Real.exp (rate *
                      (finBoxDist target source : ℝ)) *
                    (A * Real.exp (-((theta / 4) *
                      (finBoxDist target source : ℝ))) * ‖v‖) =
                    A * (Real.exp (rate *
                      (finBoxDist target source : ℝ)) *
                    Real.exp (-((theta / 4) *
                      (finBoxDist target source : ℝ)))) * ‖v‖ by ring]
                rw [← Real.exp_add]
                have hexponent :
                    rate * (finBoxDist target source : ℝ) +
                        -((theta / 4) *
                          (finBoxDist target source : ℝ)) =
                      -(rate * (finBoxDist target source : ℝ)) := by
                  nlinarith [hmargin]
                rw [hexponent]
    _ = (A * ‖v‖) * ∑ target : FinBox 4 (2 * Q),
          Real.exp (-(rate * (finBoxDist target source : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro target _
        ring
    _ ≤ (A * ‖v‖) * S := by
      apply mul_le_mul_of_nonneg_left
      · exact finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound source hrate
      · exact mul_nonneg hcut.1 (norm_nonneg v)
    _ = (A * S) * ‖v‖ := by ring

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
