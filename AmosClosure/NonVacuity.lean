/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.Core

/-!
# Non-vacuity witnesses (charter judge J-C2-3)

Rational instance terms — not existentials — satisfying every
hypothesis of both consumer families, with the Amos bound verified
EXACTLY: the calibration point `ν + 1/2 = 3/2`, `x = 2` makes the
square root Pythagorean, `√((3/2)² + 2²) = √(25/4) = 5/2`, so
`amosRHS = 2/(3/2 + 5/2) = 1/2` exactly and every hypothesis check is
rational arithmetic.  (The witnesses satisfy the HYPOTHESES; they are
not claimed to be true Bessel values.)
-/

namespace AmosClosure
namespace NonVacuity

/-- The Pythagorean square root at the witness point. -/
lemma sqrt_witness : Real.sqrt (((1:ℝ) + 1/2) ^ 2 + 2 ^ 2) = 5/2 := by
  rw [show ((1:ℝ) + 1/2) ^ 2 + 2 ^ 2 = (5/2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- The Amos bound holds at the witness ratio `2/5` (order 1,
argument 2): `2/5 < 1/2 = amosRHS 1 2`, exactly. -/
lemma amos_witness : AmosBound 1 2 (2/5) := by
  rw [amosBound_iff, sqrt_witness]
  norm_num

/-- **φ-step consumer instantiated** at the rational witness
`m = 1, b = 2, R0 = 5/7, R1 = 2/5, R2 = 1/2` (all hypotheses checked
by rational arithmetic; conclusion `8/25 < 7/2` strict). -/
theorem nonvacuous_phi_step :
    ((1-1)/((5:ℝ)/7)^2 + (1+1)*((2:ℝ)/5)^2) / 1
      < (1/((2:ℝ)/5)^2 + (1+2)*((1:ℝ)/2)^2) / (1+1) :=
  phi_step_of_recurrences 1 2 (5/7) (2/5) (1/2)
    le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) amos_witness

/-- **Unit-step consumer instantiated** at the rational witness
`ν = 1, x = 2, I0 = 1, I1 = 2/5, I2 = 1/5` (recurrence:
`1 − 1/5 = 4/5 = 2·2/2·(2/5)`; all values positive). -/
theorem nonvacuous_unit_step :
    (2:ℝ)/5 / 1 - (1:ℝ)/5 / ((2:ℝ)/5) < 1 / 2 := by
  have h := unit_step_of_recurrence_and_amos 2 1 1 (2/5) (1/5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by simpa using amos_witness)
  simpa using h

end NonVacuity
end AmosClosure
