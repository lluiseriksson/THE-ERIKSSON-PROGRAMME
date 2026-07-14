/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHoleCompression
import YangMills.RG.AppendixFParameterWitness
import YangMills.RG.LocalKP

/-!
# Appendix-F residual activity: bounded-hole cardinality tilt

This module closes P3.5 brick B3 of the `hRpoly` campaign.  A residual
`H#` estimate at rate

`polymerClusterResidualRate (4 * kappa0 + 3 + theta) kappa0`

is combined with the bounded-hole compression

`#X <= theta * (d_M(X) + 1)`, `theta = 1 + 3^d * B`,

to absorb the KP factor `exp (#X)`.  The shifted residual identity leaves
exactly the rate `kappa0`, so the resulting pointwise activity majorant feeds
the already verified volume-uniform active-skeleton KP criterion.

Honest scope: this is the source-facing residual-to-KP bridge.  The residual
`H#` bound and the final scalar KP smallness inequalities remain explicit
hypotheses.  In particular, no raw Yang--Mills fluctuation estimate is asserted
here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

/-- The full-cardinality tilt paid by a uniform hole-cardinality bound `B`. -/
def boundedHoleCardinalityTilt (d B : ℕ) : ℝ :=
  1 + (3 ^ d : ℝ) * (B : ℝ)

/-- A residual `H#` estimate at the B3 shifted rate supplies the exact
pointwise activity majorant required by the local `Omega`-active KP theorem.

The only geometric input beyond the standard hole separation hypotheses is a
uniform bound `#H <= B` for every hole. -/
theorem appendixFHoleHsharp_tilted_majorant_of_residual_bounded_holes
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zH : Finset (Cube d L) → ℂ)
    (B : ℕ) (kappa0 s C A : ℝ)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hB : ∀ H0 ∈ HF.holes, H0.card ≤ B)
    (hC : 0 ≤ C)
    (hA : Real.exp s * C ≤ A)
    (hresidual : ∀ Y : OmegaPolymerType HF zH,
      ‖zH Y.val‖ ≤
        C * appendixFHoleExpWeight HF
          (polymerClusterResidualRate
            (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) kappa0)
          Y.val) :
    ∀ Y : OmegaPolymerType HF zH,
      Real.exp s * ‖(omegaHolePolymerSystem HF zH).activity Y‖ *
          Real.exp (Y.val.card : ℝ)
        ≤ A * Real.exp (-kappa0) ^
          (discreteModifiedMetric HF Y.val + 1) := by
  intro Y
  let theta : ℝ := boundedHoleCardinalityTilt d B
  let rate : ℝ := polymerClusterResidualRate (4 * kappa0 + 3 + theta) kappa0
  have hcard :
      (Y.val.card : ℝ) ≤ theta *
        (((discreteModifiedMetric HF Y.val + 1 : ℕ) : ℝ)) := by
    simpa [theta, boundedHoleCardinalityTilt] using
      (omegaPolymerType_card_le_of_bounded_holes HF zH
        hdisj hnoedges hholes_ne hB Y)
  have hrate : rate - theta = kappa0 := by
    simpa [rate] using appendixF_thetaShifted_residual_budget kappa0 theta
  have htilt :=
    appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric
      HF rate theta s C A (Real.exp (-kappa0)) Y.val
      hC hA (by simp [hrate]) hcard
  have hnorm :
      ‖(omegaHolePolymerSystem HF zH).activity Y‖ ≤
        C * appendixFHoleExpWeight HF rate Y.val := by
    simpa [omegaHolePolymerSystem, rate, theta] using hresidual Y
  calc
    Real.exp s * ‖(omegaHolePolymerSystem HF zH).activity Y‖ *
          Real.exp (Y.val.card : ℝ)
        ≤ Real.exp s *
            (C * appendixFHoleExpWeight HF rate Y.val) *
              Real.exp (Y.val.card : ℝ) := by
            gcongr
    _ ≤ A * Real.exp (-kappa0) ^
          (discreteModifiedMetric HF Y.val + 1) := htilt

/-- **P3.5--B3 closure.**  Residual `H#` decay plus bounded-hole compression
and the shifted-rate budget imply the volume-uniform local KP criterion.

This removes the formerly carried pointwise `hact` binder from the B3 lane;
the residual activity estimate and explicit scalar smallness window remain
visible. -/
theorem omegaHolePolymerSystem_KPCriterion_of_Hsharp_residual_bounded_holes
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zH : Finset (Cube d L) → ℂ)
    (B : ℕ) (kappa0 s C A : ℝ)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hB : ∀ H0 ∈ HF.holes, H0.card ≤ B)
    (hC : 0 ≤ C)
    (hA0 : 0 ≤ A)
    (hA : Real.exp s * C ≤ A)
    (hresidual : ∀ Y : OmegaPolymerType HF zH,
      ‖zH Y.val‖ ≤
        C * appendixFHoleExpWeight HF
          (polymerClusterResidualRate
            (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) kappa0)
          Y.val)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1)
    (hsmall : A *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    KP.KPCriterion
      ((omegaHolePolymerSystem HF zH).scaleActivity (Real.exp s))
      (fun Y => (Y.val.card : ℝ)) := by
  exact
    omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound
      HF zH s (Real.exp (-kappa0)) A hA0
      (appendixFHoleHsharp_tilted_majorant_of_residual_bounded_holes
        HF zH B kappa0 s C A hdisj hnoedges hholes_ne hB hC hA hresidual)
      hdisj hnoedges hholes_ne (Real.exp_nonneg _)
      hCq hsmall

end YangMills.RG
