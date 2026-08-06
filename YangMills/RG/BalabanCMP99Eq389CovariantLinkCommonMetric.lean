/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389BlockShiftGeometry

/-!
# PRE-VALIDATION: common block metric for the first CMP99 (3.89) species

The source of this module is present, but its `.olean` has not yet been
materialized and its declarations have not yet been verified by the Lean
compiler.

The literal one-step block geometry transports each backward incident
regional-Green decay factor to the central output metric.  The only loss is
the explicit `exp(delta0)` dictated by one coarse step.  This module then
applies that transport to the sealed eight-entry link bound.

The finite four-direction sum stays visible.  No overlap, cell, layer, Schur,
Poincare or operator-norm constant is introduced, and the three species of
CMP99 (3.89) are not yet combined.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d m n : ℕ} [NeZero m] [NeZero n]

/-- Moving the output by one backward fine step costs at most one explicit
`exp(delta)` factor in the literal block-scale decay metric. -/
theorem exp_neg_blockShift_dist_le_exp_mul
    (x y : FinBox d (m * n)) (i : Fin d)
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    Real.exp (-(delta *
        (finBoxDist (blockSite m n (x.shiftBack i))
          (blockSite m n y) : ℝ))) ≤
      Real.exp delta *
        Real.exp (-(delta *
          (finBoxDist (blockSite m n x) (blockSite m n y) : ℝ))) := by
  have hstep := finBoxDist_blockSite_shiftBack_le_one (m := m) (n := n) x i
  have hdist :
      finBoxDist (blockSite m n x) (blockSite m n y) ≤
        1 + finBoxDist (blockSite m n (x.shiftBack i)) (blockSite m n y) :=
    (finBoxDist_triangle (blockSite m n x)
      (blockSite m n (x.shiftBack i)) (blockSite m n y)).trans
        (Nat.add_le_add_right hstep _)
  have hdistR :
      (finBoxDist (blockSite m n x) (blockSite m n y) : ℝ) ≤
        1 + (finBoxDist (blockSite m n (x.shiftBack i))
          (blockSite m n y) : ℝ) := by
    exact_mod_cast hdist
  have harg :
      -(delta * (finBoxDist (blockSite m n (x.shiftBack i))
          (blockSite m n y) : ℝ)) ≤
        delta + -(delta *
          (finBoxDist (blockSite m n x) (blockSite m n y) : ℝ)) := by
    nlinarith
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr harg

variable {q Nc : ℕ} [NeZero q] [NeZero Nc]

/-- The first regional-Green species with one common central block metric.

The backward entries pay the exact one-step `exp(delta0)` loss.  The four
directions remain an explicit finite sum so no later cell-count convention is
hidden here. -/
theorem norm_cmp99CovariantCutoffLinkDerivative_regionalGreen_commonMetric
    (Omega : ActiveGaugeRegion 4 (m * (2 * q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (m * (2 * q)) Nc)
    (K : GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hKcoer : IsCoerciveCLM K c)
    (B0 delta0 ell : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U 1 K c hc hKcoer
      B0 delta0 ell)
    (h : FinBox 4 (m * (2 * q)) → ℝ)
    (source : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc)
    (x : FinBox 4 (m * (2 * q))) (slope : ℝ) (hslope : 0 ≤ slope)
    (hforward : ∀ i : Fin 4, ‖h x - h (x.shift i)‖ ≤ slope)
    (hback : ∀ i : Fin 4, ‖h x - h (x.shiftBack i)‖ ≤ slope) :
    ‖cmp99CovariantCutoffLinkDerivative rho U 1 h
        (extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega K hc hKcoer
            (singleFinitePiLp source v))) x‖ ≤
      slope * ∑ _i : Fin 4,
        ((B0 * ell) *
              Real.exp (-(delta0 *
                (cmp99Eq342RescaledBlockDist m q x source.1 : ℝ))) * ‖v‖ +
          (B0 * ell) *
              (Real.exp delta0 * Real.exp (-(delta0 *
                (cmp99Eq342RescaledBlockDist m q x source.1 : ℝ)))) * ‖v‖) := by
  refine (norm_cmp99CovariantCutoffLinkDerivative_regionalGreen_one_le
    Omega rho U K c hc hKcoer B0 delta0 ell C h source v x slope hslope
      hforward hback).trans ?_
  apply mul_le_mul_of_nonneg_left _ hslope
  apply Finset.sum_le_sum
  intro i _hi
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg C.B0_nonneg C.ell_pos.le)
  simpa [cmp99Eq342RescaledBlockDist] using
    (exp_neg_blockShift_dist_le_exp_mul (m := m) (n := 2 * q)
      x source.1 i C.delta0_pos.le)

end

end YangMills.RG
