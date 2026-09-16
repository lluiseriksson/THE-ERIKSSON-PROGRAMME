/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexSymmetricRealFactorization
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

/-- The complexification of the negative symmetric real part is the average
of the matrix, its entrywise conjugate, its transpose, and its conjugate
transpose.  This additive form, rather than a global rank factorization, is
the one used to open the first factor of every trace power. -/
theorem complexified_neg_symmetricRealPart_eq_fourTerms
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) :
    (-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
        Complex.ofRealHom =
      (-1 / 4 : ℂ) •
        (A + Matrix.entrywiseConj A +
          (A.transpose + (Matrix.entrywiseConj A).transpose)) := by
  ext i j
  simp [cmp116Eq214ComplexQuadraticSymmetricRealPart,
    cmp116Eq214RealPartMatrix, Matrix.entrywiseConj_apply,
    Complex.ext_iff]
  all_goals ring

/-- Open only the first factor of a positive trace power of the complexified
negative symmetric real correction.  The remaining power stays ambient and
may be passed unchanged to a first-hit trace estimate. -/
theorem trace_complexified_neg_symmetricRealPart_pow_succ_eq_fourTerms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (m : ℕ) :
    let D :=
      (-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
        Complex.ofRealHom
    Matrix.trace (D ^ (m + 1)) =
      (-1 / 4 : ℂ) *
        (Matrix.trace (A * D ^ m) +
          Matrix.trace (Matrix.entrywiseConj A * D ^ m) +
          Matrix.trace (A.transpose * D ^ m) +
          Matrix.trace ((Matrix.entrywiseConj A).transpose * D ^ m)) := by
  let D :=
    (-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
      Complex.ofRealHom
  change
    Matrix.trace (D ^ (m + 1)) =
      (-1 / 4 : ℂ) *
        (Matrix.trace (A * D ^ m) +
          Matrix.trace (Matrix.entrywiseConj A * D ^ m) +
          Matrix.trace (A.transpose * D ^ m) +
          Matrix.trace ((Matrix.entrywiseConj A).transpose * D ^ m))
  have hD : D =
      (-1 / 4 : ℂ) •
        (A + Matrix.entrywiseConj A +
          (A.transpose + (Matrix.entrywiseConj A).transpose)) := by
    simpa [D] using complexified_neg_symmetricRealPart_eq_fourTerms A
  calc
    Matrix.trace (D ^ (m + 1)) =
        Matrix.trace (D * D ^ m) := by rw [pow_succ']
    _ = (-1 / 4 : ℂ) *
        (Matrix.trace (A * D ^ m) +
          Matrix.trace (Matrix.entrywiseConj A * D ^ m) +
          Matrix.trace (A.transpose * D ^ m) +
          Matrix.trace ((Matrix.entrywiseConj A).transpose * D ^ m)) := by
      rw [hD]
      simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
        Matrix.trace_add, smul_eq_mul]
      ring

/-- Entrywise conjugation commutes with trace. -/
theorem Matrix.trace_entrywiseConj
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.entrywiseConj A) =
      star (Matrix.trace A) := by
  simp [Matrix.trace, Matrix.entrywiseConj_apply]

/-- Against a real symmetric matrix, the four terms in the symmetric-real
expansion reduce to one trace and its conjugate. -/
theorem norm_trace_complexified_neg_symmetricRealPart_pow_succ_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (m : ℕ) :
    let D :=
      (-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
        Complex.ofRealHom
    ‖Matrix.trace (D ^ (m + 1))‖ ≤
      ‖Matrix.trace (A * D ^ m)‖ := by
  let D :=
    (-cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
      Complex.ofRealHom
  let P := D ^ m
  change ‖Matrix.trace (D ^ (m + 1))‖ ≤ ‖Matrix.trace (A * P)‖
  have hDt : D.transpose = D := by
    ext i j
    change
      Complex.ofReal
          (-cmp116Eq214ComplexQuadraticSymmetricRealPart A j i) =
        Complex.ofReal
          (-cmp116Eq214ComplexQuadraticSymmetricRealPart A i j)
    have hsym :=
      congrFun
        (congrFun
          (cmp116Eq214ComplexQuadraticSymmetricRealPart_transpose A) i) j
    simpa using congrArg (fun t : ℝ => Complex.ofReal (-t)) hsym
  have hDc : Matrix.entrywiseConj D = D := by
    ext i j
    simp [D, Matrix.entrywiseConj_apply]
  have hPt : P.transpose = P := by
    dsimp [P]
    rw [Matrix.transpose_pow, hDt]
  have hPc : Matrix.entrywiseConj P = P := by
    have hpow : ∀ n : ℕ,
        Matrix.entrywiseConj (D ^ n) = D ^ n := by
      intro n
      induction n with
      | zero =>
          ext i j
          by_cases hij : i = j <;>
            simp [Matrix.entrywiseConj_apply, hij]
      | succ n ih =>
          rw [pow_succ, Matrix.entrywiseConj_mul, ih, hDc]
    exact hpow m
  let z := Matrix.trace (A * P)
  have hconj :
      Matrix.trace (Matrix.entrywiseConj A * P) = star z := by
    calc
      Matrix.trace (Matrix.entrywiseConj A * P) =
          Matrix.trace
            (Matrix.entrywiseConj A * Matrix.entrywiseConj P) := by
        rw [hPc]
      _ = Matrix.trace (Matrix.entrywiseConj (A * P)) := by
        rw [Matrix.entrywiseConj_mul]
      _ = star z := by
        exact Matrix.trace_entrywiseConj (A * P)
  have htranspose :
      Matrix.trace (A.transpose * P) = z := by
    calc
      Matrix.trace (A.transpose * P) =
          Matrix.trace (Matrix.transpose (A.transpose * P)) := by
        rw [Matrix.trace_transpose]
      _ = Matrix.trace (P.transpose * A) := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = Matrix.trace (P * A) := by rw [hPt]
      _ = Matrix.trace (A * P) := Matrix.trace_mul_comm _ _
      _ = z := rfl
  have hconjTranspose :
      Matrix.trace ((Matrix.entrywiseConj A).transpose * P) = star z := by
    calc
      Matrix.trace ((Matrix.entrywiseConj A).transpose * P) =
          Matrix.trace (Matrix.entrywiseConj A * P) := by
        calc
          Matrix.trace ((Matrix.entrywiseConj A).transpose * P) =
              Matrix.trace
                (Matrix.transpose
                  ((Matrix.entrywiseConj A).transpose * P)) := by
            rw [Matrix.trace_transpose]
          _ = Matrix.trace (P.transpose * Matrix.entrywiseConj A) := by
            rw [Matrix.transpose_mul, Matrix.transpose_transpose]
          _ = Matrix.trace (P * Matrix.entrywiseConj A) := by rw [hPt]
          _ = Matrix.trace (Matrix.entrywiseConj A * P) :=
            Matrix.trace_mul_comm _ _
      _ = star z := hconj
  rw [trace_complexified_neg_symmetricRealPart_pow_succ_eq_fourTerms A m]
  change
    ‖(-1 / 4 : ℂ) *
      (z + Matrix.trace (Matrix.entrywiseConj A * P) +
        Matrix.trace (A.transpose * P) +
        Matrix.trace ((Matrix.entrywiseConj A).transpose * P))‖ ≤ ‖z‖
  rw [hconj, htranspose, hconjTranspose]
  have heq :
      (-1 / 4 : ℂ) * (z + star z + z + star z) =
        Complex.ofReal (-z.re) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  exact Complex.abs_re_le_norm z

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
