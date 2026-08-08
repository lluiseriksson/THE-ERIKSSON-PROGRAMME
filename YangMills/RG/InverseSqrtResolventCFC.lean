/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.InverseSqrtResolventScalarIntegral
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Spectral lift of the Balakrishnan scalar integral

This module lifts the exact scalar identity

`∫₀∞ t⁻¹ᐟ² (λ+t)⁻¹ dt = π / √λ`

through the explicit finite-dimensional Hermitian functional calculus.  This
avoids an abstract improper-integral interchange: the spectrum is finite, and
the matrix integral reduces to a finite sum of the already-normalized scalar
integrals.
-/

namespace YangMills.RG

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

attribute [local instance]
  Matrix.instL2OpNormedAddCommGroup
  Matrix.instL2OpNormedSpace

noncomputable section

/-- The scalar Balakrishnan kernel, viewed as a function of the integration
variable and the spectral variable. -/
noncomputable def inverseSqrtResolventSpectralKernel
    (t lam : ℝ) : ℝ :=
  inverseSqrtResolventScalarIntegrand lam t

/-- The inverse square root obtained directly from the Hermitian spectral
resolution of a positive-definite real matrix. -/
noncomputable def spectralInverseSqrtMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Matrix ι ι ℝ :=
  hA.isHermitian.cfc (fun lam => (Real.sqrt lam)⁻¹)

/-- The spectral inverse square root is positive semidefinite. -/
theorem spectralInverseSqrtMatrix_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (spectralInverseSqrtMatrix A hA).PosSemidef := by
  classical
  unfold spectralInverseSqrtMatrix
  rw [Matrix.IsHermitian.cfc]
  apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (Unitary.isUnit_coe
      (U := hA.isHermitian.eigenvectorUnitary))).2
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- Squaring the spectral inverse square root gives the inverse matrix. -/
theorem spectralInverseSqrtMatrix_mul_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    spectralInverseSqrtMatrix A hA *
        spectralInverseSqrtMatrix A hA =
      A⁻¹ := by
  classical
  let U : Matrix ι ι ℝ :=
    hA.isHermitian.eigenvectorUnitary
  let lam : ι → ℝ :=
    hA.isHermitian.eigenvalues
  have hlam_pos (i : ι) : 0 < lam i :=
    hA.eigenvalues_pos i
  have hA_spec :
      A = U * Matrix.diagonal lam * star U := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, mul_assoc] using
      hA.isHermitian.spectral_theorem
  have hA_inv :
      A⁻¹ = U * Matrix.diagonal (fun i => (lam i)⁻¹) * star U := by
    apply hA.isUnit.mul_left_cancel
    letI := hA.isUnit.invertible
    rw [Matrix.mul_inv_of_invertible]
    rw [hA_spec]
    simp only [mul_assoc]
    rw [← mul_assoc (star U) U]
    have hstar_mul : star U * U = 1 := by
      simp [U]
    rw [hstar_mul, one_mul]
    rw [← mul_assoc
      (Matrix.diagonal lam)
      (Matrix.diagonal (fun i => (lam i)⁻¹))]
    rw [Matrix.diagonal_mul_diagonal]
    have hdiag :
        (fun i => lam i * (lam i)⁻¹) =
          (fun _ : ι => (1 : ℝ)) := by
      funext i
      exact mul_inv_cancel₀ (hlam_pos i).ne'
    rw [hdiag]
    rw [Matrix.diagonal_one]
    simp [U]
  unfold spectralInverseSqrtMatrix
  rw [Matrix.IsHermitian.cfc]
  change
    (U * Matrix.diagonal (fun i => (Real.sqrt (lam i))⁻¹) * star U) *
        (U * Matrix.diagonal (fun i => (Real.sqrt (lam i))⁻¹) * star U) =
      A⁻¹
  rw [hA_inv]
  simp only [mul_assoc]
  rw [← mul_assoc (star U) U]
  have hunitary : star U * U = 1 := by
    simp [U]
  rw [hunitary, one_mul]
  rw [← mul_assoc
    (Matrix.diagonal (fun i => (Real.sqrt (lam i))⁻¹))
    (Matrix.diagonal (fun i => (Real.sqrt (lam i))⁻¹))]
  rw [Matrix.diagonal_mul_diagonal]
  have hsqrt :
      (fun i =>
        (Real.sqrt (lam i))⁻¹ *
          (Real.sqrt (lam i))⁻¹) =
        (fun i => (lam i)⁻¹) := by
    funext i
    rw [← mul_inv]
    rw [Real.mul_self_sqrt (hlam_pos i).le]
  rw [hsqrt]

/-- The spectral Balakrishnan kernel is the scalar `t⁻¹ᐟ²` times the
inverse of the shifted precision, expressed as a right-inverse identity. -/
theorem isHermitianCfc_inverseSqrtResolventSpectralKernel_mul_shift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (t : ℝ) (ht : 0 ≤ t) :
    hA.isHermitian.cfc
        (inverseSqrtResolventSpectralKernel t) *
        (A + t • (1 : Matrix ι ι ℝ)) =
      (Real.sqrt t)⁻¹ • (1 : Matrix ι ι ℝ) := by
  classical
  let U : Matrix ι ι ℝ :=
    hA.isHermitian.eigenvectorUnitary
  let lam : ι → ℝ :=
    hA.isHermitian.eigenvalues
  have hlam_pos (i : ι) : 0 < lam i :=
    hA.eigenvalues_pos i
  have hA_spec :
      A = U * Matrix.diagonal lam * star U := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, mul_assoc] using
      hA.isHermitian.spectral_theorem
  have hmul_star : U * star U = 1 := by
    simp [U]
  have hstar_mul : star U * U = 1 := by
    simp [U]
  have hshift :
      A + t • (1 : Matrix ι ι ℝ) =
        U * Matrix.diagonal (fun i => lam i + t) * star U := by
    calc
      A + t • (1 : Matrix ι ι ℝ) =
          U * Matrix.diagonal lam * star U +
            t • (U * star U) := by
        rw [hA_spec, hmul_star]
      _ =
          U * Matrix.diagonal lam * star U +
            U * (t • (1 : Matrix ι ι ℝ)) * star U := by
        congr 1
        simp
      _ =
          U *
            (Matrix.diagonal lam +
              t • (1 : Matrix ι ι ℝ)) *
            star U := by
        noncomm_ring
      _ =
          U * Matrix.diagonal (fun i => lam i + t) * star U := by
        congr 2
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
  rw [hshift]
  unfold inverseSqrtResolventSpectralKernel
  unfold inverseSqrtResolventScalarIntegrand
  rw [Matrix.IsHermitian.cfc]
  change
    (U *
        Matrix.diagonal
          (fun i =>
            (Real.sqrt t)⁻¹ * (lam i + t)⁻¹) *
        star U) *
        (U * Matrix.diagonal (fun i => lam i + t) * star U) =
      (Real.sqrt t)⁻¹ • (1 : Matrix ι ι ℝ)
  simp only [mul_assoc]
  rw [← mul_assoc (star U) U]
  rw [hstar_mul, one_mul]
  rw [← mul_assoc
    (Matrix.diagonal
      (fun i => (Real.sqrt t)⁻¹ * (lam i + t)⁻¹))
    (Matrix.diagonal (fun i => lam i + t))]
  rw [Matrix.diagonal_mul_diagonal]
  have hdiag :
      (fun i =>
        ((Real.sqrt t)⁻¹ * (lam i + t)⁻¹) *
          (lam i + t)) =
        (fun _ : ι => (Real.sqrt t)⁻¹) := by
    funext i
    have hne : lam i + t ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg (hlam_pos i) ht)
    field_simp
  rw [hdiag]
  have hdiag_const :
      Matrix.diagonal (fun _ : ι => (Real.sqrt t)⁻¹) =
        (Real.sqrt t)⁻¹ • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag_const]
  simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hmul_star]

/-- The finite-dimensional Hermitian functional calculus commutes with the
Balakrishnan integral, with the exact normalization `π`. -/
theorem integral_isHermitianCfc_inverseSqrtResolventSpectralKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (∫ t in Ioi 0,
        hA.isHermitian.cfc
          (inverseSqrtResolventSpectralKernel t)) =
      Real.pi •
        hA.isHermitian.cfc
          (fun lam => (Real.sqrt lam)⁻¹) := by
  classical
  let F : ℝ → Matrix ι ι ℝ :=
    fun t =>
      hA.isHermitian.cfc
        (inverseSqrtResolventSpectralKernel t)
  have hcfc_apply (f : ℝ → ℝ) (i j : ι) :
      hA.isHermitian.cfc f i j =
        ∑ k : ι,
          hA.isHermitian.eigenvectorUnitary i k *
            f (hA.isHermitian.eigenvalues k) *
            star (hA.isHermitian.eigenvectorUnitary j k) := by
    simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.mul_apply, Matrix.diagonal_apply]
  have hentry_int (i j : ι) :
      Integrable (fun t => F t i j) (volume.restrict (Ioi 0)) := by
    simp_rw [F, hcfc_apply]
    exact integrable_finset_sum Finset.univ fun k _ =>
      ((integrableOn_inverseSqrtResolventScalarIntegrand
        (hA.eigenvalues_pos k)).const_mul
          (hA.isHermitian.eigenvectorUnitary i k)).mul_const
            (star (hA.isHermitian.eigenvectorUnitary j k))
  let spectralProjector : ι → Matrix ι ι ℝ :=
    fun k i j =>
      hA.isHermitian.eigenvectorUnitary i k *
        star (hA.isHermitian.eigenvectorUnitary j k)
  have hFsum (t : ℝ) :
      F t =
        ∑ k : ι,
          inverseSqrtResolventScalarIntegrand
              (hA.isHermitian.eigenvalues k) t •
            spectralProjector k := by
    ext i j
    simp only [F]
    rw [hcfc_apply]
    simp only [inverseSqrtResolventSpectralKernel]
    change
      (∑ k : ι,
        hA.isHermitian.eigenvectorUnitary i k *
          inverseSqrtResolventScalarIntegrand
            (hA.isHermitian.eigenvalues k) t *
          star (hA.isHermitian.eigenvectorUnitary j k)) =
        (∑ k : ι,
          inverseSqrtResolventScalarIntegrand
              (hA.isHermitian.eigenvalues k) t •
            spectralProjector k) i j
    let evalAH : Matrix ι ι ℝ →+ ℝ := {
      toFun M := M i j
      map_zero' := rfl
      map_add' _ _ := rfl }
    change
      (∑ k : ι,
        hA.isHermitian.eigenvectorUnitary i k *
          inverseSqrtResolventScalarIntegrand
            (hA.isHermitian.eigenvalues k) t *
          star (hA.isHermitian.eigenvectorUnitary j k)) =
        evalAH
          (∑ k : ι,
            inverseSqrtResolventScalarIntegrand
                (hA.isHermitian.eigenvalues k) t •
              spectralProjector k)
    rw [map_sum]
    change
      (∑ k : ι,
        hA.isHermitian.eigenvectorUnitary i k *
          inverseSqrtResolventScalarIntegrand
            (hA.isHermitian.eigenvalues k) t *
          star (hA.isHermitian.eigenvectorUnitary j k)) =
        ∑ k : ι,
          inverseSqrtResolventScalarIntegrand
              (hA.isHermitian.eigenvalues k) t *
            spectralProjector k i j
    apply Finset.sum_congr rfl
    intro k _
    simp only [spectralProjector]
    ring
  have hsumint :
      Integrable
        (fun t =>
          ∑ k : ι,
            inverseSqrtResolventScalarIntegrand
                (hA.isHermitian.eigenvalues k) t •
              spectralProjector k)
        (volume.restrict (Ioi 0)) := by
    exact integrable_finset_sum Finset.univ fun k _ =>
      (integrableOn_inverseSqrtResolventScalarIntegrand
        (hA.eigenvalues_pos k)).smul_const (spectralProjector k)
  have hFint :
      Integrable F (volume.restrict (Ioi 0)) :=
    hsumint.congr (.of_forall fun t => (hFsum t).symm)
  ext i j
  let evalLM : Matrix ι ι ℝ →ₗ[ℝ] ℝ := {
    toFun M := M i j
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let evalCLM : Matrix ι ι ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap evalLM
  have evalCLM_apply (M : Matrix ι ι ℝ) :
      evalCLM M = M i j := by
    rfl
  calc
    (∫ t in Ioi 0, F t) i j =
        evalCLM (∫ t in Ioi 0, F t) :=
      (evalCLM_apply _).symm
    _ = ∫ t in Ioi 0, evalCLM (F t) :=
      (evalCLM.integral_comp_comm hFint).symm
    _ = ∫ t in Ioi 0, F t i j := by
      apply integral_congr_ae
      exact .of_forall fun t => evalCLM_apply (F t)
    _ = (Real.pi •
        hA.isHermitian.cfc
          (fun lam => (Real.sqrt lam)⁻¹)) i j := by
      simp_rw [F, hcfc_apply]
      rw [integral_finset_sum]
      · simp only [inverseSqrtResolventSpectralKernel]
        change
          (∑ k : ι,
            ∫ t in Ioi 0,
              hA.isHermitian.eigenvectorUnitary i k *
                inverseSqrtResolventScalarIntegrand
                  (hA.isHermitian.eigenvalues k) t *
                star (hA.isHermitian.eigenvectorUnitary j k)) =
            Real.pi *
              hA.isHermitian.cfc
                (fun lam => (Real.sqrt lam)⁻¹) i j
        rw [hcfc_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [integral_mul_const, integral_const_mul]
        rw [integral_inverseSqrtResolventScalarIntegrand
          (hA.eigenvalues_pos k)]
        ring
      · intro k _
        exact
          ((integrableOn_inverseSqrtResolventScalarIntegrand
            (hA.eigenvalues_pos k)).const_mul
              (hA.isHermitian.eigenvectorUnitary i k)).mul_const
                (star (hA.isHermitian.eigenvectorUnitary j k))

/-- Exact normalized matrix Balakrishnan formula. -/
theorem inv_pi_smul_integral_isHermitianCfc_inverseSqrtResolventSpectralKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Real.pi⁻¹ •
        (∫ t in Ioi 0,
          hA.isHermitian.cfc
            (inverseSqrtResolventSpectralKernel t)) =
      spectralInverseSqrtMatrix A hA := by
  rw [integral_isHermitianCfc_inverseSqrtResolventSpectralKernel A hA]
  unfold spectralInverseSqrtMatrix
  rw [smul_smul]
  rw [inv_mul_cancel₀ Real.pi_ne_zero, one_smul]

/-- The matrix-valued Balakrishnan kernel is Bochner integrable on the
positive half-line. -/
theorem integrableOn_isHermitianCfc_inverseSqrtResolventSpectralKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    IntegrableOn
      (fun t =>
        hA.isHermitian.cfc
          (inverseSqrtResolventSpectralKernel t))
      (Ioi 0) := by
  classical
  let spectralProjector : ι → Matrix ι ι ℝ :=
    fun k i j =>
      hA.isHermitian.eigenvectorUnitary i k *
        star (hA.isHermitian.eigenvectorUnitary j k)
  have hcfc_apply (f : ℝ → ℝ) (i j : ι) :
      hA.isHermitian.cfc f i j =
        ∑ k : ι,
          hA.isHermitian.eigenvectorUnitary i k *
            f (hA.isHermitian.eigenvalues k) *
            star (hA.isHermitian.eigenvectorUnitary j k) := by
    simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.mul_apply, Matrix.diagonal_apply]
  have hrepr (t : ℝ) :
      hA.isHermitian.cfc
          (inverseSqrtResolventSpectralKernel t) =
        ∑ k : ι,
          inverseSqrtResolventScalarIntegrand
              (hA.isHermitian.eigenvalues k) t •
            spectralProjector k := by
    ext i j
    rw [hcfc_apply]
    simp only [inverseSqrtResolventSpectralKernel]
    change
      (∑ k : ι,
        hA.isHermitian.eigenvectorUnitary i k *
          inverseSqrtResolventScalarIntegrand
            (hA.isHermitian.eigenvalues k) t *
          star (hA.isHermitian.eigenvectorUnitary j k)) =
        (∑ k : ι,
          inverseSqrtResolventScalarIntegrand
              (hA.isHermitian.eigenvalues k) t •
            spectralProjector k) i j
    let evalAH : Matrix ι ι ℝ →+ ℝ := {
      toFun M := M i j
      map_zero' := rfl
      map_add' _ _ := rfl }
    change
      (∑ k : ι,
        hA.isHermitian.eigenvectorUnitary i k *
          inverseSqrtResolventScalarIntegrand
            (hA.isHermitian.eigenvalues k) t *
          star (hA.isHermitian.eigenvectorUnitary j k)) =
        evalAH
          (∑ k : ι,
            inverseSqrtResolventScalarIntegrand
                (hA.isHermitian.eigenvalues k) t •
              spectralProjector k)
    rw [map_sum]
    change
      (∑ k : ι,
        hA.isHermitian.eigenvectorUnitary i k *
          inverseSqrtResolventScalarIntegrand
            (hA.isHermitian.eigenvalues k) t *
          star (hA.isHermitian.eigenvectorUnitary j k)) =
        ∑ k : ι,
          inverseSqrtResolventScalarIntegrand
              (hA.isHermitian.eigenvalues k) t *
            spectralProjector k i j
    apply Finset.sum_congr rfl
    intro k _
    simp only [spectralProjector]
    ring
  have hsum :
      Integrable
        (fun t =>
          ∑ k : ι,
            inverseSqrtResolventScalarIntegrand
                (hA.isHermitian.eigenvalues k) t •
              spectralProjector k)
        (volume.restrict (Ioi 0)) := by
    exact integrable_finset_sum Finset.univ fun k _ =>
      (integrableOn_inverseSqrtResolventScalarIntegrand
        (hA.eigenvalues_pos k)).smul_const (spectralProjector k)
  exact hsum.congr (.of_forall fun t => (hrepr t).symm)

/-- Exact normalized integral formula for the difference of two positive
inverse square roots.  No commutation between `A₀` and `A₁` is assumed. -/
theorem inv_pi_smul_integral_cfc_sub_eq_spectralInverseSqrtMatrix_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A₀ A₁ : Matrix ι ι ℝ)
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) :
    Real.pi⁻¹ •
        (∫ t in Ioi 0,
          hA₁.isHermitian.cfc
              (inverseSqrtResolventSpectralKernel t) -
            hA₀.isHermitian.cfc
              (inverseSqrtResolventSpectralKernel t)) =
      spectralInverseSqrtMatrix A₁ hA₁ -
        spectralInverseSqrtMatrix A₀ hA₀ := by
  rw [integral_sub
    (integrableOn_isHermitianCfc_inverseSqrtResolventSpectralKernel A₁ hA₁)
    (integrableOn_isHermitianCfc_inverseSqrtResolventSpectralKernel A₀ hA₀)]
  rw [smul_sub]
  rw [inv_pi_smul_integral_isHermitianCfc_inverseSqrtResolventSpectralKernel
    A₁ hA₁]
  rw [inv_pi_smul_integral_isHermitianCfc_inverseSqrtResolventSpectralKernel
    A₀ hA₀]

end

end YangMills.RG
