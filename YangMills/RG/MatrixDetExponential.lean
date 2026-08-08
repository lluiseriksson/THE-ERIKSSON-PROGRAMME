/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Determinant of a finite-dimensional matrix exponential

Mathlib's matrix-exponential file lists
`det (exp A) = exp (trace A)` as a TODO.  This module proves that identity
over complex finite matrices.  The proof first computes the Fréchet
derivative of the determinant at the identity from its finite polynomial
formula.  It then solves the scalar differential equation for
`t ↦ det (exp (tA))`.

The Frobenius norm is used only to supply a coherent finite-dimensional
Banach-algebra topology during the calculus proof.  The terminal statement
is purely algebraic.
-/

namespace YangMills.RG

open NormedSpace

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance matrixFrobeniusNormedRing :
    NormedRing (Matrix ι ι ℂ) :=
  Matrix.frobeniusNormedRing

local instance matrixFrobeniusNormedAlgebra :
    NormedAlgebra ℂ (Matrix ι ι ℂ) :=
  Matrix.frobeniusNormedAlgebra

/-- Complex matrix trace as a continuous linear map for the Frobenius
topology used locally in this proof. -/
def matrixTraceFrobeniusCLM : Matrix ι ι ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap ι ℂ ℂ)

/-- The finite determinant polynomial is complex differentiable. -/
theorem differentiable_matrix_det :
    Differentiable ℂ (Matrix.det : Matrix ι ι ℂ → ℂ) := by
  intro A
  rw [show (Matrix.det : Matrix ι ι ℂ → ℂ) =
      fun M => ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M (σ i) i by
    funext M
    exact Matrix.det_apply M]
  refine DifferentiableAt.fun_sum (𝕜 := ℂ) (u := Finset.univ) ?_
  intro σ _
  have hprod :
      DifferentiableAt ℂ (fun M : Matrix ι ι ℂ => ∏ i, M (σ i) i) A := by
    have hraw :
        DifferentiableAt ℂ
          (∏ i : ι, fun M : Matrix ι ι ℂ => M (σ i) i) A :=
      Finset.prod_induction (s := Finset.univ)
        (fun i : ι => fun M : Matrix ι ι ℂ => M (σ i) i)
        (fun f : Matrix ι ι ℂ → ℂ => DifferentiableAt ℂ f A)
        (fun _ _ ha hb => ha.mul hb)
        (differentiableAt_const (c := (1 : ℂ)))
        (by
          intro i _
          let coord : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
            { toFun := fun M => M (σ i) i
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          exact (LinearMap.toContinuousLinearMap coord).differentiableAt)
    have heq :
        (∏ i : ι, fun M : Matrix ι ι ℂ => M (σ i) i) =
          fun M : Matrix ι ι ℂ => ∏ i : ι, M (σ i) i := by
      funext M
      simpa using
        (Finset.prod_apply M Finset.univ
          (fun i : ι => fun N : Matrix ι ι ℂ => N (σ i) i))
    rwa [heq] at hraw
  have hsign :
      (fun M : Matrix ι ι ℂ => Equiv.Perm.sign σ • ∏ i, M (σ i) i) =
        fun M => (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ i, M (σ i) i) := by
    funext M
    simp [Units.smul_def]
  rw [hsign]
  exact
    (differentiableAt_const
      (c := (((Equiv.Perm.sign σ : ℤ) : ℂ)))).mul hprod

/-- The derivative of `t ↦ det (1 + tA)` at zero is `trace A`. -/
theorem hasDerivAt_det_one_add_smul
    (A : Matrix ι ι ℂ) :
    HasDerivAt (fun t : ℂ => (1 + t • A).det) A.trace 0 := by
  let p : Polynomial ℂ :=
    ((1 : Matrix ι ι (Polynomial ℂ)) + (Polynomial.X : Polynomial ℂ) •
      A.map (Polynomial.C : ℂ →+* Polynomial ℂ)).det
  have hp := p.hasDerivAt 0
  have hpderiv : p.derivative.eval 0 = A.trace := by
    simpa [p] using Matrix.derivative_det_one_add_X_smul A
  have heval : ∀ t : ℂ, p.eval t = (1 + t • A).det := by
    intro t
    simp only [p, eval_det]
    congr 1
    ext i j
    simp [Polynomial.eval, mul_comm]
  convert hp using 1
  · funext t
    exact (heval t).symm
  · exact hpderiv.symm

/-- The Fréchet derivative of determinant at the identity is trace. -/
theorem hasFDerivAt_matrix_det_one :
    HasFDerivAt (Matrix.det : Matrix ι ι ℂ → ℂ)
      matrixTraceFrobeniusCLM 1 := by
  have hdiff : DifferentiableAt ℂ
      (Matrix.det : Matrix ι ι ℂ → ℂ) 1 :=
    differentiable_matrix_det 1
  convert hdiff.hasFDerivAt using 1
  apply ContinuousLinearMap.ext
  intro A
  have hline :
      HasDerivAt
        (fun t : ℂ => Matrix.det
          (1 + ((1 : ℂ →L[ℂ] ℂ).smulRight A) t))
        ((fderiv ℂ (Matrix.det : Matrix ι ι ℂ → ℂ) 1) A) 0 := by
    have hinner :
        HasFDerivAt
          (fun t : ℂ => 1 + ((1 : ℂ →L[ℂ] ℂ).smulRight A) t)
          ((1 : ℂ →L[ℂ] ℂ).smulRight A) 0 :=
      (((1 : ℂ →L[ℂ] ℂ).smulRight A).hasFDerivAt.const_add 1)
    have hout :
        HasFDerivAt (Matrix.det : Matrix ι ι ℂ → ℂ)
          (fderiv ℂ (Matrix.det : Matrix ι ι ℂ → ℂ) 1)
          (1 + ((1 : ℂ →L[ℂ] ℂ).smulRight A) 0) := by
      simpa using hdiff.hasFDerivAt
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      one_smul] using (hout.comp 0 hinner).hasDerivAt
  have hpoly := hasDerivAt_det_one_add_smul A
  let dA : ℂ :=
    (fderiv ℂ (Matrix.det : Matrix ι ι ℂ → ℂ) 1) A
  have hline' :
      HasDerivAt (fun t : ℂ => Matrix.det (1 + t • A)) dA 0 := by
    simpa only [ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul] using hline
  have hEq := hline'.unique hpoly
  simpa [dA, matrixTraceFrobeniusCLM,
    LinearMap.coe_toContinuousLinearMap] using hEq.symm

/-- The determinant of a finite complex matrix exponential is the scalar
exponential of its trace. -/
theorem det_matrix_exp_eq_exp_trace
    [Nonempty ι] (A : Matrix ι ι ℂ) :
    Matrix.det (NormedSpace.exp A) = Complex.exp (Matrix.trace A) := by
  let g : ℂ → ℂ := fun t =>
    Matrix.det (NormedSpace.exp (t • A))
  have hg0 : HasDerivAt g A.trace 0 := by
    have hexp0 :
        HasFDerivAt
          (fun t : ℂ => NormedSpace.exp (t • A))
          ((1 : ℂ →L[ℂ] ℂ).smulRight A) 0 := by
      simpa using (hasFDerivAt_exp_smul_const ℂ A (0 : ℂ))
    have hdet0 :
        HasFDerivAt (Matrix.det : Matrix ι ι ℂ → ℂ)
          matrixTraceFrobeniusCLM
          (NormedSpace.exp ((0 : ℂ) • A)) := by
      simpa using (hasFDerivAt_matrix_det_one (ι := ι))
    have hcomp := hdet0.comp 0 hexp0
    simpa [g, matrixTraceFrobeniusCLM,
      LinearMap.coe_toContinuousLinearMap] using hcomp.hasDerivAt
  have gadd (t u : ℂ) : g (t + u) = g t * g u := by
    change Matrix.det (NormedSpace.exp ((t + u) • A)) =
      Matrix.det (NormedSpace.exp (t • A)) *
        Matrix.det (NormedSpace.exp (u • A))
    rw [add_smul]
    rw [Matrix.exp_add_of_commute _ _
      (((Commute.refl A).smul_left t).smul_right u)]
    exact Matrix.det_mul _ _
  have hg (t : ℂ) : HasDerivAt g (g t * A.trace) t := by
    have hgzero : HasDerivAt g A.trace (t - t) := by
      simpa using hg0
    have hshift : HasDerivAt (fun u : ℂ => g (u - t)) A.trace t :=
      hgzero.comp_sub_const t t
    have hmul :
        HasDerivAt (fun u : ℂ => g t * g (u - t))
          (g t * A.trace) t :=
      HasDerivAt.const_mul (g t) hshift
    have heq :
        (fun u : ℂ => g t * g (u - t)) = g := by
      funext u
      rw [← gadd]
      congr 1
      ring
    rwa [heq] at hmul
  let h : ℂ → ℂ := fun t =>
    g t * Complex.exp (-(t * A.trace))
  have hh (t : ℂ) : HasDerivAt h 0 t := by
    have he :
        HasDerivAt
          (fun u : ℂ => Complex.exp (-(u * A.trace)))
          (Complex.exp (-(t * A.trace)) * (-A.trace)) t := by
      simpa [mul_comm] using
        (((hasDerivAt_id t).mul_const A.trace).neg.cexp)
    have hm := (hg t).mul he
    change HasDerivAt
      (fun u : ℂ => g u * Complex.exp (-(u * A.trace))) 0 t
    convert hm using 1 <;> ring
  have hconst : h 0 = h 1 :=
    is_const_of_deriv_eq_zero
      (fun t => (hh t).differentiableAt)
      (fun t => (hh t).deriv) 0 1
  have hproduct :
      Matrix.det (NormedSpace.exp A) *
          Complex.exp (-A.trace) = 1 := by
    simpa [h, g] using hconst.symm
  calc
    Matrix.det (NormedSpace.exp A) =
        Matrix.det (NormedSpace.exp A) *
          (Complex.exp (-A.trace) * Complex.exp A.trace) := by
            rw [← Complex.exp_add]
            simp
    _ = (Matrix.det (NormedSpace.exp A) *
          Complex.exp (-A.trace)) * Complex.exp A.trace := by ring
    _ = Complex.exp A.trace := by rw [hproduct, one_mul]

end

end YangMills.RG
