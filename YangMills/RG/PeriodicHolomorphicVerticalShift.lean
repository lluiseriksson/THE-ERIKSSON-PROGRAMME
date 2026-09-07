/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Periodic holomorphic vertical contour shift

Cold validation: exact source checkpoint
`94e7b193304c65ec8aae5c4026056109b9b8c281` passed GitHub Actions run
`31276160414` with restore and save of `.lake/build` both skipped. The focal
completed 2,743 jobs, and the audited declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.

This module isolates the one-dimensional analytic engine needed to move one
Fourier coordinate off the real axis.  It derives equality of the lower and
upper horizontal integrals from the rectangular Cauchy theorem.  Periodicity
cancels the two vertical sides; equality of the two horizontal integrals is
not accepted as a hypothesis.

This is generic infrastructure.  It does not yet prove periodicity or
holomorphy of the literal CMP89 stabilized alias sum, iterate the shift over
all momentum coordinates, construct `B0`, or attain window 15.
-/

namespace YangMills.RG

open Set

noncomputable section

/-- A complex-differentiable function with real period `T` has the same
interval integral on the real segment `[0,T]` and on its vertical translate
by `eta * I`.

The proof is the rectangular Cauchy theorem.  The two vertical boundary
integrals cancel by periodicity, leaving precisely the asserted equality of
the horizontal boundary integrals. -/
theorem intervalIntegral_eq_verticalShift_of_periodic_of_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (T eta : ℝ)
    (hperiod : Function.Periodic f (T : ℂ))
    (hdiff : DifferentiableOn ℂ f (uIcc 0 T ×ℂ uIcc 0 eta)) :
    (∫ x : ℝ in 0..T, f (x : ℂ)) =
      ∫ x : ℝ in 0..T, f ((x : ℂ) + eta * Complex.I) := by
  have hboundary :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f (0 : ℂ) ((T : ℂ) + eta * Complex.I) (by simpa using hdiff)
  have hvertical :
      (∫ y : ℝ in 0..eta, f ((T : ℂ) + y * Complex.I)) =
        ∫ y : ℝ in 0..eta, f (y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y _
    simpa [add_comm] using hperiod (y * Complex.I)
  simp at hboundary
  rw [hvertical] at hboundary
  have hsub :
      (∫ x : ℝ in 0..T, f (x : ℂ)) -
        (∫ x : ℝ in 0..T, f ((x : ℂ) + eta * Complex.I)) = 0 := by
    simpa using hboundary
  exact sub_eq_zero.mp hsub

end

end YangMills.RG
