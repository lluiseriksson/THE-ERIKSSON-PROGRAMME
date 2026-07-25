/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexOuterGaussian
import YangMills.RG.BalabanCMP116DeterminantNearLog
import YangMills.RG.BalabanCMP116MatrixTraceNearLog

/-!
# Trace-log control of the global complex outer Gaussian

The exact global outer Gaussian is an inverse square root determinant.  On
the Mercator ball this determinant can instead be controlled by the trace of
the matrix near logarithm.  This is the interface needed by the physical
first-hit expansion: trace powers can have a carrier-linear bound even when
the complete correction has neither finite support nor carrier-linear rank.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator

noncomputable section

/-- The exact global complex outer Gaussian is controlled by the traced
Mercator logarithm of its shifted symmetric real correction. -/
theorem integral_exp_re_complexQuadratic_standardGaussianPi_le_exp_traceNearLog
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A).PosDef)
    (hsmall :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
        Complex.ofRealHom‖ < 1) :
    (∫ x : ι → ℝ,
        Real.exp ((cmp116Eq214ComplexQuadratic A x).re)
        ∂standardGaussianPi ι) ≤
      Real.exp
        (‖Matrix.trace
          (nearLog
            ((-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
              Complex.ofRealHom))‖ / 2) := by
  let H := cmp116Eq214ComplexQuadraticSymmetricRealPart A
  let D : Matrix ι ι ℂ := (-H).map Complex.ofRealHom
  let r : ℝ := Matrix.det (1 - H)
  have hr : 0 < r := by
    dsimp [r]
    exact hpos.det_pos
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have honeAdd :
      1 + D = (1 - H).map Complex.ofRealHom := by
    ext i j
    by_cases hij : i = j <;>
      simp [D, hij, sub_eq_add_neg]
  have hdet :
      Matrix.det (1 + D) = Complex.ofReal r := by
    rw [honeAdd]
    change
      (Complex.ofRealHom.mapMatrix (1 - H)).det =
        Complex.ofRealHom (Matrix.det (1 - H))
    rw [← Complex.ofRealHom.map_det]
  have hsqrtSq : (Real.sqrt r) ^ 2 = r :=
    Real.sq_sqrt hr.le
  have hdensity :
      (((Real.sqrt r)⁻¹ : ℝ) : ℂ) ^ 2 *
          Matrix.det (1 + D) = 1 := by
    rw [hdet]
    have hreal : (Real.sqrt r)⁻¹ ^ 2 * r = 1 := by
      calc
        (Real.sqrt r)⁻¹ ^ 2 * r =
            (Real.sqrt r)⁻¹ ^ 2 * (Real.sqrt r) ^ 2 :=
          congrArg (fun t : ℝ => (Real.sqrt r)⁻¹ ^ 2 * t) hsqrtSq.symm
        _ = 1 := by field_simp [ne_of_gt hsqrt]
    exact_mod_cast hreal
  have hnorm :=
    norm_density_le_exp_half_norm_trace_nearLog
      ((((Real.sqrt r)⁻¹ : ℝ) : ℂ)) D (by simpa [D, H] using hsmall)
      hdensity
  have hnorm' :
      (Real.sqrt r)⁻¹ ≤
        Real.exp (‖Matrix.trace (nearLog D)‖ / 2) := by
    simpa [Complex.norm_real, abs_of_pos hsqrt] using hnorm
  rw [integral_exp_re_complexQuadratic_standardGaussianPi A hpos]
  simpa [r, D, H] using hnorm'

/-- A carrier-linear geometric bound for the positive trace powers gives the
corresponding exponential bound for the exact global outer Gaussian. -/
theorem integral_exp_re_complexQuadratic_standardGaussianPi_le_of_tracePowers
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart A).PosDef)
    (hsmall :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
        Complex.ofRealHom‖ < 1)
    {L q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (htrace : ∀ m : ℕ,
      ‖Matrix.trace
        (((-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
          Complex.ofRealHom) ^ (m + 1))‖ ≤
        L * q ^ m) :
    (∫ x : ι → ℝ,
        Real.exp ((cmp116Eq214ComplexQuadratic A x).re)
        ∂standardGaussianPi ι) ≤
      Real.exp ((L / (1 - q)) / 2) := by
  let D : Matrix ι ι ℂ :=
    (-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map Complex.ofRealHom
  calc
    (∫ x : ι → ℝ,
        Real.exp ((cmp116Eq214ComplexQuadratic A x).re)
        ∂standardGaussianPi ι) ≤
        Real.exp (‖Matrix.trace (nearLog D)‖ / 2) := by
      exact
        integral_exp_re_complexQuadratic_standardGaussianPi_le_exp_traceNearLog
          A hpos (by simpa [D] using hsmall)
    _ ≤ Real.exp ((L / (1 - q)) / 2) := by
      apply Real.exp_le_exp.mpr
      gcongr
      exact
        norm_trace_nearLog_le_of_trace_pow_geometric
          D (by simpa [D] using hsmall) hq0 hq1 (by
            intro m
            simpa [D] using htrace m)

end

end YangMills.RG
