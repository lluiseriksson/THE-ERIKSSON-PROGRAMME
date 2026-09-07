/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220CenteredResidualQuadraticBudget
import YangMills.RG.BalabanCMP116Eq220CenteredSourcePotential

/-!
# Combining the centered quadratic and cubic-residual budgets

This module combines two estimates before the source potential is summed:

* the radial quadratic operator is charged to a localized quadratic rate;
* the genuine cubic Taylor residual is charged to a second quadratic rate
  at the interpolation center and only its contour displacement is charged
  to the printed equation-(2.20) ledger.

Consequently the final ledger contains one `Eq220` weight per domain and no
additional copy of the equation-(1.36) majorant.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- Compose a physical centered-contour quadratic estimate with a genuine
cubic-residual estimate.  `quadraticRate` and `residualRate` are kept
separate until their finite sums are charged to `potentialRate`. -/
theorem cmp116Eq220_re_physicalComplexTauPotential_le_quadratic_add_eq220
    {nY d N Nc : ℕ} [NeZero N]
    (D : Finset (Fin nY)) (tau : Fin nY → ℂ)
    (total residual :
      Fin nY → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore total residual y))
    (B : PhysicalGaugeOneCochain d N Nc)
    (energy potentialRate : ℝ)
    (quadraticRate residualRate domainDist : Fin nY → ℝ)
    (E0 epsilon1 C1 alpha4 C2 kappa1 delta kappa : ℝ)
    (M q : ℕ)
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (henergy : 0 ≤ energy)
    (hcentered :
      CMP116Eq214CenteredPolydisc nY
        (fun y =>
          cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa (domainDist y))
        tau)
    (hquadratic : ∀ y ∈ D,
      ‖tau y‖ *
          |inner ℝ B
            (cmp116Eq142PhysicalSourceQuadratic
              total residual hsmooth y B B)| ≤
        quadraticRate y * energy)
    (hresidualCenter : ∀ y ∈ D,
      |residual y B| ≤ residualRate y / 2 * energy)
    (h136 : ∀ y ∈ D,
      |residual y B| ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y))
    (hrate :
      ∑ y ∈ D, (quadraticRate y + residualRate y) ≤ potentialRate) :
    (cmp116Eq214PhysicalComplexTauPotential D tau
        (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
        residual B).re ≤
      potentialRate / 2 * energy +
        ∑ y ∈ D,
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) := by
  have hterm : ∀ y ∈ D,
      (tau y).re *
          cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B ≤
        (quadraticRate y + residualRate y) / 2 * energy +
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) := by
    intro y hy
    obtain ⟨s, hs, htau⟩ := hcentered y
    have hremainder :
        ‖tau y‖ * |residual y B| ≤
          residualRate y / 2 * energy +
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y) :=
      cmp116Eq136_centeredContour_residual_le_quadratic_add_eq220
        hE0 hepsilon1 hC1 halpha4 hM hs htau
        (abs_nonneg (residual y B)) (hresidualCenter y hy) (h136 y hy)
    have hpotentialAbs :
        |cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B| ≤
          (1 / 2 : ℝ) *
              |inner ℝ B
                (cmp116Eq142PhysicalSourceQuadratic
                  total residual hsmooth y B B)| +
            |residual y B| := by
      dsimp [cmp116Eq142PhysicalPotentialTerm]
      calc
        |(1 / 2 : ℝ) *
              inner ℝ B
                (cmp116Eq142PhysicalSourceQuadratic
                  total residual hsmooth y B B) +
            residual y B| ≤
          |(1 / 2 : ℝ) *
              inner ℝ B
                (cmp116Eq142PhysicalSourceQuadratic
                  total residual hsmooth y B B)| +
            |residual y B| := abs_add_le _ _
        _ = (1 / 2 : ℝ) *
              |inner ℝ B
                (cmp116Eq142PhysicalSourceQuadratic
                  total residual hsmooth y B B)| +
            |residual y B| := by norm_num [abs_mul]
    calc
      (tau y).re *
          cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B ≤
        |(tau y).re *
          cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B| := le_abs_self _
      _ = |(tau y).re| *
          |cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B| := abs_mul _ _
      _ ≤ ‖tau y‖ *
          ((1 / 2 : ℝ) *
              |inner ℝ B
                (cmp116Eq142PhysicalSourceQuadratic
                  total residual hsmooth y B B)| +
            |residual y B|) := by
        exact mul_le_mul
          (Complex.abs_re_le_norm (tau y)) hpotentialAbs
          (abs_nonneg _)
          (le_trans (abs_nonneg _)
            (Complex.abs_re_le_norm (tau y)))
      _ = (1 / 2 : ℝ) *
            (‖tau y‖ *
              |inner ℝ B
                (cmp116Eq142PhysicalSourceQuadratic
                  total residual hsmooth y B B)|) +
          ‖tau y‖ * |residual y B| := by ring
      _ ≤ (1 / 2 : ℝ) * (quadraticRate y * energy) +
          (residualRate y / 2 * energy +
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hquadratic y hy) (by norm_num))
          hremainder
      _ = (quadraticRate y + residualRate y) / 2 * energy +
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) := by ring
  calc
    (cmp116Eq214PhysicalComplexTauPotential D tau
        (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
        residual B).re =
      ∑ y ∈ D,
        (tau y).re *
          cmp116Eq142PhysicalPotentialTerm
            (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
            residual y B := by
      simp [cmp116Eq214PhysicalComplexTauPotential_re]
    _ ≤ ∑ y ∈ D,
        ((quadraticRate y + residualRate y) / 2 * energy +
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y)) :=
      Finset.sum_le_sum hterm
    _ =
        (∑ y ∈ D, (quadraticRate y + residualRate y)) / 2 * energy +
          ∑ y ∈ D,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y) := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ y ∈ D,
            (quadraticRate y + residualRate y) / 2 * energy) =
          ∑ y ∈ D,
            (quadraticRate y + residualRate y) * (energy / 2) := by
              apply Finset.sum_congr rfl
              intro y _
              ring
        _ =
          (∑ y ∈ D, (quadraticRate y + residualRate y)) *
              (energy / 2) := by
            rw [Finset.sum_mul]
        _ =
          (∑ y ∈ D, (quadraticRate y + residualRate y)) / 2 *
              energy := by ring
    _ ≤ potentialRate / 2 * energy +
          ∑ y ∈ D,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y) := by
      gcongr

end

end YangMills.RG
