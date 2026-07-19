/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLog
import Mathlib.Analysis.CStarAlgebra.Exponential

/-!
# The unitary layer of the CMP99 background average

CMP109 (0.12) has the represented form

`exp (L⁻ᵈ ∑ x, log D_x) * U(c)`.

This file closes the part of the return-to-group argument that follows from
anti-adjointness.  It proves that the Mercator logarithm commutes with `star`,
packages the exact remaining inverse-log identity for a unitary deviation,
and constructs the exponential factor and the full block canonically in the
unitary group.

It deliberately does **not** claim membership in `SU(N)`.  Two further facts
are required for that stronger codomain:

* `nearLog (D⁻¹ - 1) = -nearLog (D - 1)` in the near-identity ball;
* determinant one for the exponential of the resulting traceless matrix.

The second statement is the explicit TODO in Mathlib's
`Analysis/Normed/Algebra/MatrixExponential.lean`; no local axiom or arbitrary
choice of a preimage is used here.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [ContinuousStar A] [StarModule ℝ A]

/-- The Mercator logarithm commutes with the continuous star operation.
This is termwise: its coefficients are real and star commutes with powers and
convergent sums. -/
theorem star_nearLog (Y : A) :
    star (nearLog Y) = nearLog (star Y) := by
  rw [nearLog, nearLog, tsum_star]
  apply tsum_congr
  intro n
  rw [star_smul, star_pow]
  simp only [star_trivial]

/-- For a unitary element, star sends the Mercator coordinate at `D - 1` to
the Mercator coordinate at the inverse unitary deviation. -/
theorem star_nearLog_unitary_sub_one (D : unitary A) :
    star (nearLog ((D : A) - 1)) =
      nearLog (((star D : unitary A) : A) - 1) := by
  rw [star_nearLog]
  congr 1
  simp

/-- Exact identification of the remaining analytic obligation: the Mercator
coordinate of a near-identity unitary is skew-adjoint precisely when its value
at the inverse deviation is its negative. -/
theorem nearLog_unitary_sub_one_mem_skewAdjoint_iff (D : unitary A) :
    nearLog ((D : A) - 1) ∈ skewAdjoint A ↔
      nearLog (((star D : unitary A) : A) - 1) =
        -nearLog ((D : A) - 1) := by
  rw [skewAdjoint.mem_iff, star_nearLog_unitary_sub_one]

/-- The literal exponent in the represented CMP109 (0.12) block. -/
noncomputable def cmp99UbarExponent {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (D : ι → A) : A :=
  ∑ i ∈ s, w i • nearLog (D i - 1)

/-- A finite real-weighted sum of certified skew-adjoint logarithmic
coordinates is skew-adjoint. -/
theorem cmp99UbarExponent_mem_skewAdjoint {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (D : ι → A)
    (hlog : ∀ i ∈ s, nearLog (D i - 1) ∈ skewAdjoint A) :
    cmp99UbarExponent s w D ∈ skewAdjoint A := by
  unfold cmp99UbarExponent
  exact (skewAdjoint A).sum_mem fun i hi =>
    skewAdjoint.smul_mem (w i) (hlog i hi)

/-- The exponential factor of CMP109 (0.12), canonically valued in the
unitary group once the logarithmic coordinates are skew-adjoint. -/
noncomputable def cmp99UbarUnitaryFactor {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (D : ι → A)
    (hlog : ∀ i ∈ s, nearLog (D i - 1) ∈ skewAdjoint A) :
    unitary A :=
  ⟨NormedSpace.exp (cmp99UbarExponent s w D),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (cmp99UbarExponent_mem_skewAdjoint s w D hlog)⟩

@[simp] theorem cmp99UbarUnitaryFactor_coe {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (D : ι → A)
    (hlog : ∀ i ∈ s, nearLog (D i - 1) ∈ skewAdjoint A) :
    (cmp99UbarUnitaryFactor s w D hlog : A) =
      NormedSpace.exp (cmp99UbarExponent s w D) :=
  rfl

/-- The full represented CMP109 (0.12) block in the unitary group. -/
noncomputable def cmp99UbarUnitaryBlock {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (D : ι → A)
    (hlog : ∀ i ∈ s, nearLog (D i - 1) ∈ skewAdjoint A)
    (coarse : unitary A) : unitary A :=
  cmp99UbarUnitaryFactor s w D hlog * coarse

@[simp] theorem cmp99UbarUnitaryBlock_coe {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (D : ι → A)
    (hlog : ∀ i ∈ s, nearLog (D i - 1) ∈ skewAdjoint A)
    (coarse : unitary A) :
    (cmp99UbarUnitaryBlock s w D hlog coarse : A) =
      NormedSpace.exp (cmp99UbarExponent s w D) * (coarse : A) :=
  rfl

end

end YangMills.RG
