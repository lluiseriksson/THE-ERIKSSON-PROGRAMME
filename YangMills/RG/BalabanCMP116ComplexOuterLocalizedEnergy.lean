/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexOuterTracePowers
import YangMills.RG.BalabanCMP116Eq223PhysicalSmallness

/-!
# Adding the localized source energy to the complex outer quadratic

After the inner Gaussian is integrated, its source produces a localized
quadratic energy in the outer field.  This module inserts that energy into
the same complex quadratic matrix as `R₁`, preparing one global Gaussian
integration rather than a pointwise product bound.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

/-- Complex matrix whose quadratic form is the localized real energy
`beta * sum_{i in S} x_i^2`. -/
def cmp116Eq214LocalizedOuterEnergyMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (beta : ℝ) : Matrix ι ι ℂ :=
  ((2 * beta) • cmp116Eq223CoordinateProjection S).map Complex.ofRealHom

set_option maxHeartbeats 1000000 in
/-- The localized energy matrix has exactly the intended complex quadratic
form, with no conjugation and no normalization loss. -/
theorem cmp116Eq214ComplexQuadratic_localizedOuterEnergyMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (beta : ℝ) (x : ι → ℝ) :
    cmp116Eq214ComplexQuadratic
        (cmp116Eq214LocalizedOuterEnergyMatrix S beta) x =
      (beta * ∑ i ∈ S, x i ^ 2 : ℝ) := by
  rw [show
    cmp116Eq214LocalizedOuterEnergyMatrix S beta =
      (2 * beta : ℂ) •
        (cmp116Eq223CoordinateProjection S).map Complex.ofRealHom by
      ext i j
      simp [cmp116Eq214LocalizedOuterEnergyMatrix]]
  unfold cmp116Eq214ComplexQuadratic
  rw [Matrix.smul_mulVec, dotProduct_smul]
  rw [show cmp116Eq214ComplexCoordinate x = (fun i => (x i : ℂ)) by rfl]
  rw [map_mulVec_ofReal]
  rw [← ofReal_dotProduct]
  rw [dotProduct_projection_mulVec]
  push_cast
  simp only [smul_eq_mul]
  ring

/-- Adding the localized source energy to `A` adds its real exponent to the
literal complex `R₁` quadratic. -/
theorem cmp116Eq214ComplexQuadratic_add_localizedOuterEnergyMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (S : Finset ι) (beta : ℝ) (x : ι → ℝ) :
    cmp116Eq214ComplexQuadratic
        (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta) x =
      cmp116Eq214ComplexQuadratic A x +
        (beta * ∑ i ∈ S, x i ^ 2 : ℝ) := by
  rw [show
    cmp116Eq214ComplexQuadratic
        (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta) x =
      cmp116Eq214ComplexQuadratic A x +
        cmp116Eq214ComplexQuadratic
          (cmp116Eq214LocalizedOuterEnergyMatrix S beta) x by
      unfold cmp116Eq214ComplexQuadratic
      rw [Matrix.add_mulVec, dotProduct_add]
      ring]
  rw [cmp116Eq214ComplexQuadratic_localizedOuterEnergyMatrix]

/-- Testing the localized energy matrix against an arbitrary ambient
multiplier costs only the cardinality of the localized carrier. -/
theorem norm_trace_localizedOuterEnergyMatrix_mul_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (beta : ℝ) (P : Matrix ι ι ℂ) :
    ‖Matrix.trace (cmp116Eq214LocalizedOuterEnergyMatrix S beta * P)‖ ≤
      (2 * |beta| * (S.card : ℝ)) * ‖P‖ := by
  have heq :
      Matrix.trace (cmp116Eq214LocalizedOuterEnergyMatrix S beta * P) =
        (2 * beta : ℂ) * ∑ i ∈ S, P i i := by
    classical
    have hdiag : ∀ i,
        (cmp116Eq214LocalizedOuterEnergyMatrix S beta * P) i i =
          if i ∈ S then (2 * beta : ℂ) * P i i else 0 := by
      intro i
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · by_cases hi : i ∈ S <;>
          simp [cmp116Eq214LocalizedOuterEnergyMatrix,
            cmp116Eq223CoordinateProjection, Matrix.diagonal, hi]
      · intro j hj hji
        simp [cmp116Eq214LocalizedOuterEnergyMatrix,
          cmp116Eq223CoordinateProjection, Matrix.diagonal, Ne.symm hji]
      · simp
    rw [Matrix.trace]
    calc
      ∑ i, (cmp116Eq214LocalizedOuterEnergyMatrix S beta * P) i i =
          ∑ i, if i ∈ S then (2 * beta : ℂ) * P i i else 0 := by
        exact Finset.sum_congr rfl fun i _ => hdiag i
      _ = (2 * beta : ℂ) * ∑ i ∈ S, P i i := by
        simp [Finset.mul_sum]
  have hscalar : ‖(2 * beta : ℂ)‖ = 2 * |beta| := by
    rw [norm_mul]
    norm_num
  rw [heq, norm_mul, hscalar]
  calc
    (2 * |beta|) * ‖∑ i ∈ S, P i i‖ ≤
        (2 * |beta|) * ∑ i ∈ S, ‖P i i‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (2 * |beta|) * ∑ _i ∈ S, ‖P‖ := by
      gcongr with i hi
      exact norm_matrix_entry_le_linfty_opNorm P i i
    _ = (2 * |beta| * (S.card : ℝ)) * ‖P‖ := by
      simp
      ring

/-- A symmetric trace-test budget for `A` and the exact localized carrier
budget combine without introducing the ambient coordinate dimension. -/
theorem norm_trace_add_localizedOuterEnergyMatrix_mul_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (S : Finset ι) (beta L : ℝ)
    (P : Matrix ι ι ℂ)
    (htrace : ‖Matrix.trace (A * P)‖ ≤ L * ‖P‖) :
    ‖Matrix.trace
        ((A + cmp116Eq214LocalizedOuterEnergyMatrix S beta) * P)‖ ≤
      (L + 2 * |beta| * (S.card : ℝ)) * ‖P‖ := by
  rw [Matrix.add_mul, Matrix.trace_add]
  calc
    ‖Matrix.trace (A * P) +
        Matrix.trace (cmp116Eq214LocalizedOuterEnergyMatrix S beta * P)‖ ≤
        ‖Matrix.trace (A * P)‖ +
          ‖Matrix.trace
            (cmp116Eq214LocalizedOuterEnergyMatrix S beta * P)‖ :=
      norm_add_le _ _
    _ ≤ L * ‖P‖ +
        (2 * |beta| * (S.card : ℝ)) * ‖P‖ := by
      gcongr
      exact norm_trace_localizedOuterEnergyMatrix_mul_le S beta P
    _ = (L + 2 * |beta| * (S.card : ℝ)) * ‖P‖ := by ring

/-- The `R₁` quadratic and the localized source energy are integrated as one
global Gaussian.  The carrier appears only through its cardinality in the
trace-test budget. -/
theorem integral_exp_re_complexQuadratic_add_localizedEnergy_le_of_multiplier
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (S : Finset ι) (beta : ℝ)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart
        (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)).PosDef)
    (hsmall :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart
        (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)).map
          Complex.ofRealHom‖ < 1)
    {L : ℝ} (hL : 0 ≤ L)
    (htrace : ∀ P : Matrix ι ι ℂ, P.transpose = P →
      ‖Matrix.trace (A * P)‖ ≤ L * ‖P‖) :
    (∫ x : ι → ℝ,
        Real.exp
          ((cmp116Eq214ComplexQuadratic A x).re +
            beta * ∑ i ∈ S, x i ^ 2)
        ∂standardGaussianPi ι) ≤
      Real.exp
        (((L + 2 * |beta| * (S.card : ℝ)) /
          (1 -
            ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart
              (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)).map
                Complex.ofRealHom‖)) / 2) := by
  have hbudget : 0 ≤ L + 2 * |beta| * (S.card : ℝ) := by positivity
  have hcombined :=
    integral_exp_re_complexQuadratic_standardGaussianPi_le_of_multiplier
      (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)
      hpos hsmall hbudget (fun P hPt =>
        norm_trace_add_localizedOuterEnergyMatrix_mul_le
          A S beta L P (htrace P hPt))
  have hexponent : ∀ x : ι → ℝ,
      (cmp116Eq214ComplexQuadratic
        (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta) x).re =
        (cmp116Eq214ComplexQuadratic A x).re +
          beta * ∑ i ∈ S, x i ^ 2 := by
    intro x
    rw [cmp116Eq214ComplexQuadratic_add_localizedOuterEnergyMatrix]
    rw [Complex.add_re, Complex.ofReal_re]
  simpa only [hexponent] using hcombined

/-- Uniform-radius version of the combined outer Gaussian bound.  It is the
form consumed on an entire Cauchy boundary, where one common `q < 1`
dominates the contour-dependent symmetric-real correction. -/
theorem integral_exp_re_complexQuadratic_add_localizedEnergy_le_of_radius
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (S : Finset ι) (beta : ℝ)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart
        (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)).PosDef)
    {q L : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hL : 0 ≤ L)
    (hD :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart
        (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)).map
          Complex.ofRealHom‖ ≤ q)
    (htrace : ∀ P : Matrix ι ι ℂ, P.transpose = P →
      ‖Matrix.trace (A * P)‖ ≤ L * ‖P‖) :
    (∫ x : ι → ℝ,
        Real.exp
          ((cmp116Eq214ComplexQuadratic A x).re +
            beta * ∑ i ∈ S, x i ^ 2)
        ∂standardGaussianPi ι) ≤
      Real.exp
        (((L + 2 * |beta| * (S.card : ℝ)) / (1 - q)) / 2) := by
  let B := A + cmp116Eq214LocalizedOuterEnergyMatrix S beta
  let total := L + 2 * |beta| * (S.card : ℝ)
  have htotal : 0 ≤ total := by
    dsimp [total]
    positivity
  have htraceB : ∀ P : Matrix ι ι ℂ, P.transpose = P →
      ‖Matrix.trace (B * P)‖ ≤ total * ‖P‖ := by
    intro P hPt
    exact
      norm_trace_add_localizedOuterEnergyMatrix_mul_le
        A S beta L P (htrace P hPt)
  have hDB :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart B).map
          Complex.ofRealHom‖ ≤ q := by
    simpa [B] using hD
  have hpowers :=
    norm_trace_complexified_neg_symmetricRealPart_pow_succ_le_of_multiplier
      B htotal hDB htraceB
  have hsmallB :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart B).map
          Complex.ofRealHom‖ < 1 :=
    hDB.trans_lt hq1
  have hbound :=
    integral_exp_re_complexQuadratic_standardGaussianPi_le_of_tracePowers
      B hpos hsmallB
      hq0 hq1 hpowers
  have hexponent : ∀ x : ι → ℝ,
      (cmp116Eq214ComplexQuadratic B x).re =
        (cmp116Eq214ComplexQuadratic A x).re +
          beta * ∑ i ∈ S, x i ^ 2 := by
    intro x
    dsimp [B]
    rw [cmp116Eq214ComplexQuadratic_add_localizedOuterEnergyMatrix,
      Complex.add_re, Complex.ofReal_re]
  simpa only [B, total, hexponent] using hbound

end

end YangMills.RG
