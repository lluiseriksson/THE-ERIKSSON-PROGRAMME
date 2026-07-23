/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214CauchyEstimate

/-!
# The actual polydisc traversed by the CMP116 Cauchy contours

Every Cauchy circle in equation (2.14) is centered at an interpolation point
`s ∈ (0,1]`, not at the origin.  A point on the circle of radius `r` therefore
satisfies `‖z‖ ≤ 1 + r`.  This module propagates that elementary estimate
through the source-ordered recursive Cauchy families.

The result replaces the unnecessarily strong demand for a bound at every
complex parameter by a bound only on the shifted closed polydiscs actually
visited by the `sigma` and `tau` contours.
-/

namespace YangMills.RG

open Set Metric
open scoped Real Topology

/-- Shifted closed polydisc containing every recursive Cauchy contour. -/
def CMP116Eq214ShiftedPolydisc
    (n : ℕ) (radius : Fin n → ℝ) (z : Fin n → ℂ) : Prop :=
  ∀ i, ‖z i‖ ≤ 1 + radius i

/-- One source Cauchy circle is contained in the shifted disc `‖z‖ ≤ 1+r`. -/
theorem norm_le_one_add_radius_of_mem_sourceCauchyCircle
    {s r : ℝ} {z : ℂ}
    (hs : s ∈ Set.uIoc (0 : ℝ) 1)
    (hz : z ∈ Metric.sphere (s : ℂ) r) :
    ‖z‖ ≤ 1 + r := by
  have hs0 : 0 < s := by simpa using hs.1
  have hs1 : s ≤ 1 := by simpa using hs.2
  have hdist : ‖z - (s : ℂ)‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  calc
    ‖z‖ = ‖(z - (s : ℂ)) + (s : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - (s : ℂ)‖ + ‖(s : ℂ)‖ := norm_add_le _ _
    _ = r + s := by simp [hdist, abs_of_pos hs0]
    _ ≤ r + 1 := by simpa [add_comm] using add_le_add_right hs1 r
    _ = 1 + r := by ring

/-- A bound on the shifted polydisc supplies the exact recursive boundary
condition for one Cauchy family. -/
theorem cmp116Eq214CauchyBoundaryBound_of_shiftedPolydisc
    (n : ℕ) (radius : Fin n → ℝ)
    (F : (Fin n → ℂ) → ℂ) (M : ℝ)
    (hF : ∀ z, CMP116Eq214ShiftedPolydisc n radius z → ‖F z‖ ≤ M) :
    CMP116Eq214CauchyBoundaryBound n radius F M := by
  induction n with
  | zero =>
      simpa [CMP116Eq214CauchyBoundaryBound] using
        hF Fin.elim0 (by
          intro i
          exact Fin.elim0 i)
  | succ n ih =>
      simp only [CMP116Eq214CauchyBoundaryBound]
      intro s hs z hz
      apply ih (fun i => radius i.succ) (fun tail => F (Fin.cons z tail))
      intro tail htail
      apply hF (Fin.cons z tail)
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using norm_le_one_add_radius_of_mem_sourceCauchyCircle hs hz
      · simpa using htail j

/-- Two shifted-polydisc bounds generate the source-ordered nested boundary
condition for the `sigma` and `tau` Cauchy families. -/
theorem cmp116Eq214NestedCauchyBoundaryBound_of_shiftedPolydiscs
    (nDelta nY : ℕ)
    (deltaRadius : Fin nDelta → ℝ) (yRadius : Fin nY → ℝ)
    (F : (Fin nDelta → ℂ) → (Fin nY → ℂ) → ℂ) (M : ℝ)
    (hF : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY yRadius tau →
      ‖F sigma tau‖ ≤ M) :
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      deltaRadius yRadius F M := by
  induction nDelta with
  | zero =>
      simp only [CMP116Eq214NestedCauchyBoundaryBound]
      apply cmp116Eq214CauchyBoundaryBound_of_shiftedPolydisc
      intro tau htau
      exact hF Fin.elim0 tau (by
        intro i
        exact Fin.elim0 i) htau
  | succ nDelta ih =>
      simp only [CMP116Eq214NestedCauchyBoundaryBound]
      intro s hs z hz
      apply ih (fun i => deltaRadius i.succ)
        (fun sigmaTail tau => F (Fin.cons z sigmaTail) tau)
      intro sigmaTail tau hsigma htau
      apply hF (Fin.cons z sigmaTail) tau
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using norm_le_one_add_radius_of_mem_sourceCauchyCircle hs hz
        · simpa using hsigma j
      · exact htau

end YangMills.RG
