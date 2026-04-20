/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.SchurZeroMean

/-!
# Milestone L2.4: Schur norm-squared — structural lemmas for SU(N_c)

Pointwise identities preparing the character inner product
`⟨χ_fund, χ_fund⟩ = ∫ |tr U|² dHaar = 1` on SU(N_c):

* `trace_star_eq_star_trace`         — `tr(star A) = star (tr A)`.
* `normSq_trace_eq_mul_conj_re`      — `|tr A|² = Re(tr A · conj (tr A))`.
* `trace_mul_conj_trace_eq_normSq`   — `tr A · conj (tr A) = (|tr A|² : ℂ)`.
* `trace_inv_eq_star_trace_SU`       — `tr(U⁻¹) = star (tr U)` for `U ∈ SU(N_c)`.

For `U ∈ SU(N_c)` the matrix inverse coincides with `star U`, so the
pointwise identity

  `|tr U|² = tr U · conj (tr U) = tr U · tr (U⁻¹)`

reduces the character inner product to an integral of matrix-coefficient
products.  The remaining step

  `∫_SU(N_c) |tr U|² dHaar = 1`

requires Schur orthogonality of matrix coefficients of the fundamental
representation and is deferred to Milestone L2.5.

Source: PETER_WEYL_ROADMAP.md Layer 2, Milestone L2.4 (structural part).
-/

namespace YangMills

open Matrix Complex

variable {N_c : ℕ}

/-- `tr (star A) = star (tr A)` for any square complex matrix. -/
theorem trace_star_eq_star_trace
    (A : Matrix (Fin N_c) (Fin N_c) ℂ) :
    (star A).trace = star A.trace := by
  rw [show (star A : Matrix (Fin N_c) (Fin N_c) ℂ) = Aᴴ from rfl]
  exact Matrix.trace_conjTranspose A

/-- `|tr A|² = Re (tr A · conj (tr A))`. -/
theorem normSq_trace_eq_mul_conj_re
    (A : Matrix (Fin N_c) (Fin N_c) ℂ) :
    Complex.normSq A.trace =
    (A.trace * starRingEnd ℂ A.trace).re := by
  rw [Complex.mul_conj]
  simp

/-- `tr A · conj (tr A) = (|tr A|² : ℂ)` coerced back to ℂ. -/
theorem trace_mul_conj_trace_eq_normSq
    (A : Matrix (Fin N_c) (Fin N_c) ℂ) :
    A.trace * starRingEnd ℂ A.trace = (Complex.normSq A.trace : ℂ) := by
  exact Complex.mul_conj A.trace

/-- For `U ∈ SU(N_c)`, `tr(U⁻¹) = star (tr U)`.

The `specialUnitaryGroup` instance sets `Inv := star`, so
`(U⁻¹).val = star U.val` holds by `rfl`.  Combined with the
`trace_star_eq_star_trace` identity this gives the claim. -/
theorem trace_inv_eq_star_trace_SU [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    (U⁻¹).val.trace = star U.val.trace := by
  have h : (U⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)).val
      = star U.val := rfl
  rw [h]
  exact trace_star_eq_star_trace U.val

end YangMills
