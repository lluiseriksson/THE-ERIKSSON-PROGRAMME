/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116QuadraticGaussianSpectral
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Group.Pi.Units

/-!
# CMP116 quadratic Gaussian integral: symmetric-matrix closure

This module closes the finite-dimensional analytic identity for a real
symmetric quadratic perturbation of the standard Gaussian.  For a real matrix
`A` such that `1 + A` is positive definite and a complex source `c`, it proves
the exact determinant/inverse formula

`det(1 + A)⁻¹ᐟ² exp((cᵀ (1 + A)⁻¹ c) / 2)`.

The source pairing is complex bilinear: no conjugation, `normSq`, or Hermitian
pairing is introduced.  The proof diagonalizes `1 + A`, uses orthogonal
invariance of the standard Gaussian, consumes the normalized diagonal endpoint,
and reconstructs both the determinant and inverse quadratic form.

This is a finite-dimensional analytic theorem.  It does not yet identify the
Balaban term (2.14), construct the physical activity `H(Z)`, or prove (2.26).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal RealInnerProductSpace

namespace YangMills.RG

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugating the perturbation `A` by the eigenbasis of `1 + A`
produces the shifted diagonal spectrum `λ - 1`. -/
theorem shiftedQuadratic_conjStarAlgAut_eq_diagonal
    (A : Matrix ι ι ℝ) (hpos : (1 + A).PosDef) :
    let hB : (1 + A : Matrix ι ι ℝ).IsHermitian := hpos.isHermitian
    (Unitary.conjStarAlgAut ℝ _
      (star hB.eigenvectorUnitary)) A =
      Matrix.diagonal (fun i => hB.eigenvalues i - 1) := by
  dsimp only
  let hB : (1 + A : Matrix ι ι ℝ).IsHermitian := hpos.isHermitian
  let Q := hB.eigenvectorUnitary
  have hAeq : A = (1 + A) - 1 := by abel
  calc
    (Unitary.conjStarAlgAut ℝ _ (star Q)) A =
        (Unitary.conjStarAlgAut ℝ _ (star Q)) ((1 + A) - 1) :=
      congrArg _ hAeq
    _ = (Unitary.conjStarAlgAut ℝ _ (star Q)) (1 + A) - 1 := by
      rw [map_sub, map_one]
    _ = Matrix.diagonal hB.eigenvalues - 1 := by
      simpa [Function.comp_def] using
        hB.conjStarAlgAut_star_eigenvectorUnitary
    _ = Matrix.diagonal (fun i => hB.eigenvalues i - 1) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]

/-- Reconstruction of `A` from the shifted spectrum of `1 + A`. -/
theorem shiftedQuadratic_eq_spectral_reconstruction
    (A : Matrix ι ι ℝ) (hpos : (1 + A).PosDef) :
    let hB : (1 + A : Matrix ι ι ℝ).IsHermitian := hpos.isHermitian
    A = (hB.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => hB.eigenvalues i - 1) *
        star (hB.eigenvectorUnitary : Matrix ι ι ℝ) := by
  dsimp only
  let hB : (1 + A : Matrix ι ι ℝ).IsHermitian := hpos.isHermitian
  let Q := hB.eigenvectorUnitary
  have hdiag := shiftedQuadratic_conjStarAlgAut_eq_diagonal A hpos
  have h := congrArg (Unitary.conjStarAlgAut ℝ _ Q) hdiag
  change
    (Q : Matrix ι ι ℝ) *
          (star (Q : Matrix ι ι ℝ) * A * (Q : Matrix ι ι ℝ)) *
        star (Q : Matrix ι ι ℝ) =
      (Q : Matrix ι ι ℝ) *
          Matrix.diagonal (fun i => hB.eigenvalues i - 1) *
        star (Q : Matrix ι ι ℝ) at h
  have hleft :
      (Q : Matrix ι ι ℝ) *
            (star (Q : Matrix ι ι ℝ) * A * (Q : Matrix ι ι ℝ)) *
          star (Q : Matrix ι ι ℝ) = A := by
    have hunit :
        (Q : Matrix ι ι ℝ) * star (Q : Matrix ι ι ℝ) = 1 :=
      Unitary.coe_mul_star_self Q
    calc
      _ = ((Q : Matrix ι ι ℝ) * star (Q : Matrix ι ι ℝ)) * A *
          ((Q : Matrix ι ι ℝ) * star (Q : Matrix ι ι ℝ)) := by
            noncomm_ring
      _ = A := by rw [hunit]; simp
  calc
    A = _ := hleft.symm
    _ = _ := h

/-- Spectral inverse formula for a real positive-definite matrix. -/
theorem posDef_inv_eq_spectral
    (B : Matrix ι ι ℝ) (hB : B.PosDef) :
    B⁻¹ =
      (hB.1.eigenvectorUnitary : Matrix ι ι ℝ) *
        Matrix.diagonal (fun i => (hB.1.eigenvalues i)⁻¹) *
          star (hB.1.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let hH : B.IsHermitian := hB.1
  let μ := hH.eigenvalues
  let Q := hH.eigenvectorUnitary
  have hμ : ∀ i, 0 < μ i := by
    intro i
    simpa [μ, hH] using hB.eigenvalues_pos i
  have hu : IsUnit μ :=
    Pi.isUnit_iff.mpr fun i =>
      isUnit_iff_ne_zero.mpr (ne_of_gt (hμ i))
  let u : (ι → ℝ)ˣ := hu.unit
  have hcoe : (u : ι → ℝ) = μ := hu.unit_spec
  have hinvEig :
      Ring.inverse μ = fun i => (μ i)⁻¹ := by
    calc
      Ring.inverse μ = Ring.inverse (u : ι → ℝ) := by rw [hcoe]
      _ = (↑(u⁻¹) : ι → ℝ) := Ring.inverse_unit u
      _ = fun i => (μ i)⁻¹ := by
        funext i
        change (hu.unit⁻¹).1 i = _
        rw [hu.val_inv_apply i, Units.val_inv_eq_inv_val,
          (hu.apply i).unit_spec]
  have hinvQ :
      (Q : Matrix ι ι ℝ)⁻¹ = star (Q : Matrix ι ι ℝ) :=
    Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self Q)
  have hinvStarQ :
      (star (Q : Matrix ι ι ℝ))⁻¹ = (Q : Matrix ι ι ℝ) :=
    Matrix.inv_eq_left_inv (Unitary.coe_mul_star_self Q)
  calc
    B⁻¹ =
        ((Unitary.conjStarAlgAut ℝ _ Q)
          (Matrix.diagonal μ))⁻¹ :=
      congrArg (fun M : Matrix ι ι ℝ => M⁻¹)
        hH.spectral_theorem
    _ = _ := by
      rw [Unitary.conjStarAlgAut_apply,
        Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.inv_diagonal, hinvQ, hinvStarQ, hinvEig]
      simp only [Q, μ, Matrix.mul_assoc]

/-- The inverse quadratic form with a complex source is bilinear, not
Hermitian, and equals the spectral sum of coordinate squares. -/
theorem posDef_complex_bilinear_inverse_eq_spectral_sum
    (B : Matrix ι ι ℝ) (hB : B.PosDef) (c : ι → ℂ) :
    c ⬝ᵥ ((B⁻¹).map Complex.ofRealHom *ᵥ c) =
      ∑ i,
        ((Matrix.map (star (hB.1.eigenvectorUnitary : Matrix ι ι ℝ))
            Complex.ofRealHom *ᵥ c) i) ^ 2 /
          (hB.1.eigenvalues i : ℂ) := by
  let μ := hB.1.eigenvalues
  let Qr : Matrix ι ι ℝ := hB.1.eigenvectorUnitary
  let Qc : Matrix ι ι ℂ := Qr.map Complex.ofRealHom
  let d : ι → ℂ :=
    Matrix.map (star Qr) Complex.ofRealHom *ᵥ c
  have hinvR := posDef_inv_eq_spectral B hB
  have hinvC :
      (B⁻¹).map Complex.ofRealHom =
        ((hB.1.eigenvectorUnitary : Matrix ι ι ℝ) *
          Matrix.diagonal (fun i => (hB.1.eigenvalues i)⁻¹) *
            star (hB.1.eigenvectorUnitary : Matrix ι ι ℝ)).map Complex.ofRealHom := by
    exact congrArg (fun M : Matrix ι ι ℝ => M.map Complex.ofRealHom) hinvR
  rw [hinvC]
  rw [Matrix.map_mul (f := Complex.ofRealHom),
    Matrix.map_mul (f := Complex.ofRealHom)]
  rw [← Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose]
  have htranspose : Qcᵀ = Matrix.map (star Qr) Complex.ofRealHom := by
    ext i j
    simp [Qc, Qr, Matrix.transpose_apply]
  rw [htranspose]
  have hdiag :
      (Matrix.diagonal (fun i => ((μ i)⁻¹ : ℝ))).map Complex.ofRealHom =
        Matrix.diagonal (fun i => ((μ i : ℂ)⁻¹)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiag]
  change d ⬝ᵥ (Matrix.diagonal (fun i => ((μ i : ℂ)⁻¹)) *ᵥ d) =
    ∑ i, d i ^ 2 / (μ i : ℂ)
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  change d i * ((μ i : ℂ)⁻¹ * d i) = d i ^ 2 / (μ i : ℂ)
  field_simp

/-- Coordinates in the eigenvector basis are multiplication by the transposed
orthogonal eigenvector matrix. -/
theorem eigenvectorBasis_repr_eq_star_mulVec
    (B : Matrix ι ι ℝ) (hB : B.PosDef) (x : ι → ℝ) (i : ι) :
    hB.1.eigenvectorBasis.repr (WithLp.toLp 2 x) i =
      (star (hB.1.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x) i := by
  rw [OrthonormalBasis.repr_apply_apply]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The real quadratic form of `A` is the shifted spectral sum of squares. -/
theorem shiftedQuadraticForm_eq_spectral_sum
    (A : Matrix ι ι ℝ) (hpos : (1 + A).PosDef) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) =
      ∑ i, (hpos.1.eigenvalues i - 1) *
        (hpos.1.eigenvectorBasis.repr (WithLp.toLp 2 x) i) ^ 2 := by
  let hB : (1 + A : Matrix ι ι ℝ).IsHermitian := hpos.isHermitian
  let Q : Matrix.unitaryGroup ι ℝ := hB.eigenvectorUnitary
  let y : ι → ℝ := star (Q : Matrix ι ι ℝ) *ᵥ x
  conv_lhs => rw [shiftedQuadratic_eq_spectral_reconstruction A hpos]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose]
  have htranspose :
      (Q : Matrix ι ι ℝ)ᵀ = star (Q : Matrix ι ι ℝ) := by
    ext i j
    simp [Matrix.transpose_apply]
  rw [htranspose]
  change y ⬝ᵥ (Matrix.diagonal (fun i => hB.eigenvalues i - 1) *ᵥ y) = _
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  have hy : y i =
      hB.eigenvectorBasis.repr (WithLp.toLp 2 x) i := by
    symm
    exact_mod_cast (show
      hB.eigenvectorBasis.repr (WithLp.toLp 2 x) i =
        (star (hB.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x) i by
          rw [OrthonormalBasis.repr_apply_apply]
          simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec,
            Matrix.IsHermitian.eigenvectorUnitary_apply]
          apply Finset.sum_congr rfl
          intro j hj
          ring)
  rw [hy]
  ring

/-- Real orthogonal transformations preserve the complex bilinear dot product
after scalar extension from `ℝ` to `ℂ`. -/
theorem complex_orthogonal_bilinear
    (Q : Matrix.unitaryGroup ι ℝ) (c x : ι → ℂ) :
    (Matrix.map (star (Q : Matrix ι ι ℝ)) Complex.ofRealHom *ᵥ c) ⬝ᵥ
        (Matrix.map (star (Q : Matrix ι ι ℝ)) Complex.ofRealHom *ᵥ x) =
      c ⬝ᵥ x := by
  let Qc : Matrix ι ι ℂ :=
    Matrix.map (Q : Matrix ι ι ℝ) Complex.ofRealHom
  let Sc : Matrix ι ι ℂ :=
    Matrix.map (star (Q : Matrix ι ι ℝ)) Complex.ofRealHom
  have htranspose : Qcᵀ = Sc := by
    ext i j
    simp [Qc, Sc, Matrix.transpose_apply]
  have htranspose' : Scᵀ = Qc := by
    ext i j
    simp [Qc, Sc, Matrix.transpose_apply]
  have horth : Qc * Sc = 1 := by
    have hreal :
        (Q : Matrix ι ι ℝ) * star (Q : Matrix ι ι ℝ) = 1 :=
      Unitary.coe_mul_star_self Q
    calc
      Qc * Sc =
          ((Q : Matrix ι ι ℝ) * star (Q : Matrix ι ι ℝ)).map
            Complex.ofRealHom := by
        exact (Matrix.map_mul (L := (Q : Matrix ι ι ℝ))
          (M := star (Q : Matrix ι ι ℝ))
          (f := Complex.ofRealHom)).symm
      _ = (1 : Matrix ι ι ℝ).map Complex.ofRealHom := by
        rw [hreal]
      _ = 1 := by simp
  change (Sc *ᵥ c) ⬝ᵥ (Sc *ᵥ x) = c ⬝ᵥ x
  calc
    (Sc *ᵥ c) ⬝ᵥ (Sc *ᵥ x) =
        (Qc *ᵥ (Sc *ᵥ c)) ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec]
      rw [← Matrix.mulVec_transpose, htranspose']
    _ = c ⬝ᵥ x := by
      rw [Matrix.mulVec_mulVec, horth, Matrix.one_mulVec]

/-- The original complex source pairing equals its spectral-coordinate pairing. -/
theorem complexSource_pairing_eq_spectral
    (A : Matrix ι ι ℝ) (hpos : (1 + A).PosDef)
    (c : ι → ℂ) (x : ι → ℝ) :
    ∑ i,
        (Matrix.map
            (star (hpos.1.eigenvectorUnitary : Matrix ι ι ℝ))
            Complex.ofRealHom *ᵥ c) i *
          ((hpos.1.eigenvectorBasis.repr (WithLp.toLp 2 x) i : ℝ) : ℂ) =
      ∑ i, c i * (x i : ℂ) := by
  let Q : Matrix.unitaryGroup ι ℝ := hpos.1.eigenvectorUnitary
  let xC : ι → ℂ := fun i => (x i : ℂ)
  let d : ι → ℂ :=
    Matrix.map (star (Q : Matrix ι ι ℝ)) Complex.ofRealHom *ᵥ c
  let y : ι → ℂ :=
    Matrix.map (star (Q : Matrix ι ι ℝ)) Complex.ofRealHom *ᵥ xC
  have hy (i : ι) :
      y i = ((hpos.1.eigenvectorBasis.repr (WithLp.toLp 2 x) i : ℝ) : ℂ) := by
    have hr :
        hpos.1.eigenvectorBasis.repr (WithLp.toLp 2 x) i =
          (star (hpos.1.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x) i := by
      rw [OrthonormalBasis.repr_apply_apply]
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec,
        Matrix.IsHermitian.eigenvectorUnitary_apply]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hr]
    simp [y, xC, Q, Matrix.mulVec]
    simp only [dotProduct]
    push_cast
    rfl
  change d ⬝ᵥ (fun i =>
      ((hpos.1.eigenvectorBasis.repr (WithLp.toLp 2 x) i : ℝ) : ℂ)) =
    c ⬝ᵥ xC
  simp_rw [← hy]
  exact complex_orthogonal_bilinear Q c xC

/-- Exact finite-dimensional symmetric quadratic Gaussian identity.

The complex source is paired bilinearly with the real field.  Consequently the
terminal exponent is `cᵀ (1 + A)⁻¹ c / 2`, without complex conjugation. -/
theorem integral_cexp_symmetricQuadratic_standardGaussianPi
    (A : Matrix ι ι ℝ) (hpos : (1 + A).PosDef) (c : ι → ℂ) :
    ∫ x : ι → ℝ,
        Complex.exp
          (-(((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) / 2) +
            ∑ i, c i * (x i : ℂ))
        ∂(standardGaussianPi ι) =
      ((Real.sqrt (Matrix.det (1 + A)))⁻¹ : ℝ) •
        Complex.exp
          ((c ⬝ᵥ (((1 + A)⁻¹).map Complex.ofRealHom *ᵥ c)) / 2) := by
  let hB : (1 + A : Matrix ι ι ℝ).IsHermitian := hpos.isHermitian
  let b := hB.eigenvectorBasis
  let lam := hB.eigenvalues
  let d : ι → ℂ :=
    Matrix.map (star (hB.eigenvectorUnitary : Matrix ι ι ℝ))
      Complex.ofRealHom *ᵥ c
  calc
    (∫ x : ι → ℝ,
        Complex.exp
          (-(((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) / 2) +
            ∑ i, c i * (x i : ℂ))
        ∂(standardGaussianPi ι)) =
      ∫ x : ι → ℝ,
        Complex.exp
          (-∑ i, ((lam i - 1 : ℝ) : ℂ) / 2 *
              ((b.repr (WithLp.toLp 2 x) i : ℝ) : ℂ) ^ 2 +
            ∑ i, d i * ((b.repr (WithLp.toLp 2 x) i : ℝ) : ℂ))
        ∂(standardGaussianPi ι) := by
          apply integral_congr_ae
          filter_upwards [] with x
          congr 1
          have hq := shiftedQuadraticForm_eq_spectral_sum A hpos x
          have hs := complexSource_pairing_eq_spectral A hpos c x
          rw [hq, hs]
          push_cast
          simp only [b, lam]
          rw [Finset.sum_div]
          apply congrArg₂ (· + ·)
          · congr 1
            apply Finset.sum_congr rfl
            intro i hi
            ring
          · rfl
    _ = ((Real.sqrt (∏ i, lam i))⁻¹ : ℝ) •
        Complex.exp (∑ i, (d i) ^ 2 / (2 * lam i)) := by
      exact integral_cexp_orthogonalDiagonal_standardGaussianPi
        b lam d (fun i => by simpa [lam, hB] using hpos.eigenvalues_pos i)
    _ = ((Real.sqrt (Matrix.det (1 + A)))⁻¹ : ℝ) •
        Complex.exp
          ((c ⬝ᵥ (((1 + A)⁻¹).map Complex.ofRealHom *ᵥ c)) / 2) := by
      have hdet : Matrix.det (1 + A) = ∏ i, lam i := by
        simpa [lam, hB] using hB.det_eq_prod_eigenvalues
      have hbil := posDef_complex_bilinear_inverse_eq_spectral_sum
        (1 + A) hpos c
      change c ⬝ᵥ (((1 + A)⁻¹).map Complex.ofRealHom *ᵥ c) =
        ∑ i, d i ^ 2 / (lam i : ℂ) at hbil
      rw [hdet, hbil]
      congr 2
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      have hne : (lam i : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (by simpa [lam, hB] using hpos.eigenvalues_pos i)
      field_simp

end

end YangMills.RG
