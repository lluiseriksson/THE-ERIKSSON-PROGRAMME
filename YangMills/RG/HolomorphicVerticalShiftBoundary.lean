/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PeriodicHolomorphicVerticalShift

/-!
# Vertical contour shift from a boundary seam

Compiler-verified at exact source checkpoint
`2e1df044b6210ca418a0132ffe62216e46f75157` by cold GitHub Actions run
`31286165205`. Restoration and saving of `.lake/build` were skipped. The focal
completed 2,744 jobs, the audit exited zero, and the audited declaration uses
exactly `[propext, Classical.choice, Quot.sound]`.

The rectangular Cauchy argument does not require a global periodicity
hypothesis.  It only requires equality of the integrand on the two vertical
edges of the particular rectangle.  This form is important for the stabilized
CMP89 integrand: its physical seam can be proved at the Brillouin-zone
boundary without reintroducing cancelled denominators throughout the strip.
-/

namespace YangMills.RG

noncomputable section

/-- A complex-differentiable function has equal integrals on the lower and
upper horizontal edges of a rectangle when its two vertical boundary values
agree pointwise on that rectangle.

Unlike `intervalIntegral_eq_verticalShift_of_periodic_of_differentiableOn`,
this theorem assumes only the boundary seam actually consumed by the Cauchy
argument; it does not promote that seam to global periodicity. -/
theorem intervalIntegral_eq_verticalShift_of_boundary_eq_of_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (T eta : ℝ)
    (hboundary : ∀ y ∈ Set.uIcc (0 : ℝ) eta,
      f ((T : ℂ) + y * Complex.I) = f (y * Complex.I))
    (hdiff : DifferentiableOn ℂ f (Set.uIcc 0 T ×ℂ Set.uIcc 0 eta)) :
    (∫ x : ℝ in 0..T, f (x : ℂ)) =
      ∫ x : ℝ in 0..T, f ((x : ℂ) + eta * Complex.I) := by
  have hboundaryIntegral :
      (∫ y : ℝ in 0..eta, f ((T : ℂ) + y * Complex.I)) =
        ∫ y : ℝ in 0..eta, f (y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact hboundary y hy
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f (0 : ℂ) ((T : ℂ) + eta * Complex.I) (by simpa using hdiff)
  simp at hrect
  rw [hboundaryIntegral] at hrect
  have hsub :
      (∫ x : ℝ in 0..T, f (x : ℂ)) -
        (∫ x : ℝ in 0..T, f ((x : ℂ) + eta * Complex.I)) = 0 := by
    simpa using hrect
  exact sub_eq_zero.mp hsub

end

end YangMills.RG
