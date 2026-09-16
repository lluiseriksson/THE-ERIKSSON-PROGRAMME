/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq136To220
import YangMills.RG.BalabanCMP116RadialResidualQuadraticBudget

/-!
# A centered residual with an Eq220-only displacement ledger

On a source Cauchy circle `z = s + (z-s)`, the interpolation center and the
contour displacement must be charged differently.  The center multiplies the
genuine cubic Taylor residual and is absorbed into the localized quadratic
rate on cutoff support.  Only the displacement consumes the solved Cauchy
radius and becomes the printed equation-(2.20) domain weight.

This module formalizes that split first for one domain and then for a finite
domain family.  It does not assume that the center contribution vanishes and
does not charge it a second time to the Eq220 residual ledger.
-/

namespace YangMills.RG

open Set
open scoped BigOperators

noncomputable section

/-- Refined centered-contour residual estimate: the center is paid by a
quadratic rate, while the displacement is paid by the exact Eq220 weight. -/
theorem cmp116Eq136_centeredContour_residual_le_quadratic_add_eq220
    {E0 epsilon1 C1 alpha4 C2 kappa1 delta kappa domainDist : ℝ}
    {residualAbs centerRate energy : ℝ}
    {M q : ℕ} {s : ℝ} {z : ℂ}
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (hs : s ∈ Set.uIoc (0 : ℝ) 1)
    (hz : ‖z - (s : ℂ)‖ ≤
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa domainDist)
    (hresidual : 0 ≤ residualAbs)
    (hcenter : residualAbs ≤ centerRate / 2 * energy)
    (h136 : residualAbs ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist) :
    ‖z‖ * residualAbs ≤
      centerRate / 2 * energy +
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa domainDist := by
  have hs0 : 0 < s := by simpa using hs.1
  have hs1 : s ≤ 1 := by simpa using hs.2
  have hcenterNorm : ‖(s : ℂ)‖ ≤ 1 := by
    simpa [abs_of_pos hs0] using hs1
  let radius :=
    cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa domainDist
  have hradius : 0 ≤ radius := by
    dsimp [radius, cmp116Eq218TauAbsSolved]
    positivity
  have hznorm : ‖z‖ ≤ 1 + radius := by
    calc
      ‖z‖ = ‖(z - (s : ℂ)) + (s : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (s : ℂ)‖ + ‖(s : ℂ)‖ := norm_add_le _ _
      _ ≤ radius + 1 := add_le_add hz hcenterNorm
      _ = 1 + radius := by ring
  have hdisplacement :
      radius * residualAbs ≤
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa domainDist := by
    dsimp [radius]
    exact
      cmp116Eq136_bound_mul_tauAbsSolved_le_eq220ResidualDomainWeight
        hE0 hepsilon1 hC1 halpha4 hM h136
  calc
    ‖z‖ * residualAbs ≤ (1 + radius) * residualAbs :=
      mul_le_mul_of_nonneg_right hznorm hresidual
    _ = residualAbs + radius * residualAbs := by ring
    _ ≤ centerRate / 2 * energy +
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa domainDist :=
      add_le_add hcenter hdisplacement

/-- Finite-domain version of the refined split.  A bound on the sum of the
center rates produces one quadratic `potentialRate`; the residual ledger
contains only the printed Eq220 weights. -/
theorem sum_centeredContour_residual_le_potentialRate_add_eq220
    {Y : Type*} [DecidableEq Y]
    (D : Finset Y)
    (domainDist residualAbs centerRate : Y → ℝ)
    {E0 epsilon1 C1 alpha4 C2 kappa1 delta kappa : ℝ}
    {potentialRate energy : ℝ} {M q : ℕ}
    (s : Y → ℝ) (z : Y → ℂ)
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (henergy : 0 ≤ energy)
    (hs : ∀ y ∈ D, s y ∈ Set.uIoc (0 : ℝ) 1)
    (hz : ∀ y ∈ D,
      ‖z y - (s y : ℂ)‖ ≤
        cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa (domainDist y))
    (hresidual : ∀ y ∈ D, 0 ≤ residualAbs y)
    (hcenter : ∀ y ∈ D,
      residualAbs y ≤ centerRate y / 2 * energy)
    (h136 : ∀ y ∈ D,
      residualAbs y ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y))
    (hrate : ∑ y ∈ D, centerRate y ≤ potentialRate) :
    ∑ y ∈ D, ‖z y‖ * residualAbs y ≤
      potentialRate / 2 * energy +
        ∑ y ∈ D,
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) := by
  have hterm : ∀ y ∈ D,
      ‖z y‖ * residualAbs y ≤
        centerRate y / 2 * energy +
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) := by
    intro y hy
    exact
      cmp116Eq136_centeredContour_residual_le_quadratic_add_eq220
        hE0 hepsilon1 hC1 halpha4 hM (hs y hy) (hz y hy)
        (hresidual y hy) (hcenter y hy) (h136 y hy)
  calc
    ∑ y ∈ D, ‖z y‖ * residualAbs y ≤
        ∑ y ∈ D,
          (centerRate y / 2 * energy +
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y)) :=
      Finset.sum_le_sum hterm
    _ =
        (∑ y ∈ D, centerRate y) / 2 * energy +
          ∑ y ∈ D,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y) := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ y ∈ D, centerRate y / 2 * energy) =
            ∑ y ∈ D, centerRate y * (energy / 2) := by
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ = (∑ y ∈ D, centerRate y) * (energy / 2) := by
          rw [Finset.sum_mul]
        _ = (∑ y ∈ D, centerRate y) / 2 * energy := by ring
    _ ≤ potentialRate / 2 * energy +
          ∑ y ∈ D,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainDist y) := by
      gcongr

end

end YangMills.RG
