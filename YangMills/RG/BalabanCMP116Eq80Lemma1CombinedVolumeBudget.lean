/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedRootedResidual
import YangMills.RG.BalabanCMP116SourceRestrictedConditionedPhysicalOuterCardinality

/-!
# Canonical combined equation-(2.26) volume rate

The centered conditioned term source consumes the sum of the rooted residual
rate and the complete physical outer-bound cost.  This module keeps that
literal sum visible and fixes `volumeRate` to its least exact value after
division by the positive interaction parameter `alpha`.

This normalization discharges the local `volume_budget`; it does not erase
the later source comparison.  The latter becomes exactly the scalar window
`combinedVolumeCost ≤ C_alpha5 * alpha5`, with no freely enlarged
`volumeRate`.  The region argument is intended to be instantiated by
`cmp116Eq80Lemma1CombinedCenteredRegion`, so every native boundary domain
remains present.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev CombinedPhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Literal numerator of the combined direct/Lemma-1 Gaussian volume rate. -/
noncomputable def cmp116Eq80Lemma1CombinedPhysicalVolumeCost
    {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : CombinedPhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ)
    (radius rate Ahead rho alpha sourceRate qBound determinantCost : ℝ)
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ) : ℝ :=
  cmp116Eq80Lemma1CombinedPhysicalRootBound
      E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 +
    cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost
      K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
        qBound determinantCost

/-- Canonical least volume coefficient for positive `alpha`. -/
noncomputable def cmp116Eq80Lemma1CombinedPhysicalVolumeRate
    {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : CombinedPhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ)
    (radius rate Ahead rho alpha sourceRate qBound determinantCost : ℝ)
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ) : ℝ :=
  cmp116Eq80Lemma1CombinedPhysicalVolumeCost (q := q)
      K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
        qBound determinantCost E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 /
    alpha

/-- The canonical coefficient pays the terminal volume ledger with equality,
not by choosing an arbitrarily large free rate. -/
theorem cmp116Eq80Lemma1CombinedPhysicalVolumeRate_mul_alpha
    {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : CombinedPhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ)
    (radius rate Ahead rho alpha sourceRate qBound determinantCost : ℝ)
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ)
    (halpha : 0 < alpha) :
    cmp116Eq80Lemma1CombinedPhysicalVolumeRate (q := q)
        K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
          qBound determinantCost E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 *
      alpha =
    cmp116Eq80Lemma1CombinedPhysicalVolumeCost (q := q)
      K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
        qBound determinantCost E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 := by
  unfold cmp116Eq80Lemma1CombinedPhysicalVolumeRate
  exact div_mul_cancel₀ _ halpha.ne'

/-- Exact terminal `volume_budget` after choosing the canonical rate. -/
theorem cmp116Eq80Lemma1CombinedPhysical_volume_budget
    {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : CombinedPhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ)
    (radius rate Ahead rho alpha sourceRate qBound determinantCost : ℝ)
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ)
    (halpha : 0 < alpha) :
    cmp116Eq80Lemma1CombinedPhysicalRootBound
        E0 epsilon1 C1 M q C2 kappa1 delta kappa alpha4 +
      cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost
        K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
          qBound determinantCost ≤
    cmp116Eq80Lemma1CombinedPhysicalVolumeRate (q := q)
        K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
          qBound determinantCost E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 *
      alpha := by
  rw [cmp116Eq80Lemma1CombinedPhysicalVolumeRate_mul_alpha
    K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
      qBound determinantCost E0 epsilon1 C1 C2 kappa1 delta kappa alpha4
      halpha]
  rfl

/-- The downstream source comparison retains exactly the full combined
cost.  Thus normalizing `volumeRate` closes no scalar window by fiat. -/
theorem cmp116Eq80Lemma1CombinedPhysical_volume_target_iff
    {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : CombinedPhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ)
    (radius rate Ahead rho alpha sourceRate qBound determinantCost : ℝ)
    (E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 target : ℝ)
    (halpha : 0 < alpha) :
    cmp116Eq80Lemma1CombinedPhysicalVolumeRate (q := q)
          K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
            qBound determinantCost E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 *
        alpha ≤ target ↔
      cmp116Eq80Lemma1CombinedPhysicalVolumeCost (q := q)
          K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
            qBound determinantCost E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 ≤
        target := by
  rw [cmp116Eq80Lemma1CombinedPhysicalVolumeRate_mul_alpha
    K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
      qBound determinantCost E0 epsilon1 C1 C2 kappa1 delta kappa alpha4
      halpha]

/-- The full combined numerator is nonnegative under the already named
animal, contour, and Neumann windows. -/
theorem cmp116Eq80Lemma1CombinedPhysicalVolumeCost_nonneg
    {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : CombinedPhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ)
    {radius rate Ahead rho alpha sourceRate qBound determinantCost : ℝ}
    {E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 : ℝ}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hanimal1 :
      64 * Real.exp (-(((1 - 2 * delta) * kappa) / 24)) < 1)
    (hanimal2 :
      64 * Real.exp (-((delta * kappa) / 24)) < 1)
    (hradius : 0 ≤ radius) (hAhead : 0 ≤ Ahead)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius (1 + radius) < 1)
    (hneumannTranspose :
      cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound
        K Delta Ahead rho rate radius (1 + radius) < 1)
    (hqBound : qBound < 1) :
    0 ≤ cmp116Eq80Lemma1CombinedPhysicalVolumeCost (q := q)
      K root hc hmass hK Z0 Delta radius rate Ahead rho alpha sourceRate
        qBound determinantCost E0 epsilon1 C1 C2 kappa1 delta kappa alpha4 := by
  unfold cmp116Eq80Lemma1CombinedPhysicalVolumeCost
  exact add_nonneg
    (cmp116Eq80Lemma1CombinedPhysicalRootBound_nonneg
      hE0 hepsilon1 hC1 halpha4 hanimal1 hanimal2)
    (cmp116SourceRestrictedConditionedPhysicalOuterPerCarrierCost_nonneg
      K root hc hmass hK Z0 Delta hradius hAhead hgeom
        hneumann hneumannTranspose hqBound)

end

end YangMills.RG
