/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116QuadraticGaussianMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# CMP116 (2.23)--(2.25): coupled Gaussian and Schur complement

This module evaluates the standardized finite-dimensional two-stage Gaussian
integral that occurs in the analytic passage from (2.23) to (2.25) of
Balaban's cluster-expansion estimate.  Integrating the fluctuation coordinate
first turns the coupling matrix `G` into the Schur-complement correction

`S = A - Gᵀ (1 + B)⁻¹ G`.

The remaining Gaussian integral is then evaluated by the general symmetric
quadratic identity.  The source is complex and the final pairing remains
complex bilinear: no conjugation or Hermitian norm is introduced.

This theorem is deliberately narrower than the full term (2.14).  It does not
construct Balaban's contour and cutoff factors, identify the physical activity
`H(Z)`, justify the whitening transformation from the physical covariance, or
prove the termwise majorant (2.26).

Reference: T. Balaban, *Renormalization Group Approach to Lattice Gauge Field
Theories II. Cluster Expansions*, Commun. Math. Phys. 116 (1988), 1--22,
especially equations (2.23)--(2.26).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal RealInnerProductSpace

namespace YangMills.RG

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A real matrix coupling transported through a complex bilinear source
equals the quadratic form obtained by pulling the middle matrix back along the
coupling. -/
theorem coupledSource_bilinear_eq_schurQuadratic
    (C : Matrix κ κ ℝ) (G : Matrix κ ι ℝ) (x : ι → ℝ) :
    (fun j => ((G *ᵥ x) j : ℂ)) ⬝ᵥ
        (C.map Complex.ofRealHom *ᵥ (fun j => ((G *ᵥ x) j : ℂ))) =
      ((x ⬝ᵥ ((Gᵀ * C * G) *ᵥ x) : ℝ) : ℂ) := by
  let y : κ → ℝ := G *ᵥ x
  have hreal : y ⬝ᵥ (C *ᵥ y) = x ⬝ᵥ ((Gᵀ * C * G) *ᵥ x) := by
    calc
      y ⬝ᵥ (C *ᵥ y) =
          (G *ᵥ x) ⬝ᵥ (C *ᵥ (G *ᵥ x)) := rfl
      _ = x ⬝ᵥ (Gᵀ *ᵥ (C *ᵥ (G *ᵥ x))) := by
        symm
        rw [Matrix.dotProduct_mulVec x Gᵀ (C *ᵥ (G *ᵥ x))]
        rw [← Matrix.mulVec_transpose (Gᵀ) x]
        simp
      _ = x ⬝ᵥ ((Gᵀ * C * G) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← hreal]
  change (fun j => (y j : ℂ)) ⬝ᵥ
      (C.map Complex.ofRealHom *ᵥ (fun j => (y j : ℂ))) =
    ((y ⬝ᵥ (C *ᵥ y) : ℝ) : ℂ)
  simp [dotProduct, Matrix.mulVec]

/-- The two determinant factors produced by successive Gaussian integration
are the Schur-complement factorization of the determinant of the coupled block
quadratic form. -/
theorem det_coupledBlock_eq_det_mul_det_schur
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (G : Matrix κ ι ℝ)
    (hB : (1 + B).PosDef) :
    Matrix.det (Matrix.fromBlocks (1 + A) Gᵀ G (1 + B)) =
      Matrix.det (1 + B) *
        Matrix.det (1 + (A - Gᵀ * (1 + B)⁻¹ * G)) := by
  letI := hB.isUnit.invertible
  rw [Matrix.det_fromBlocks₂₂]
  rw [Matrix.invOf_eq_nonsing_inv]
  congr 2
  abel

/-- Evaluate a coupled, iterated standard Gaussian integral.  Positive
definiteness of `1 + B` evaluates the inner fluctuation integral; positive
definiteness of `1 + S`, where `S` is the Schur complement, evaluates the
remaining background integral. -/
theorem integral_cexp_twoStage_symmetricQuadratic_standardGaussianPi
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (G : Matrix κ ι ℝ)
    (hB : (1 + B).PosDef)
    (hS : (1 + (A - Gᵀ * (1 + B)⁻¹ * G)).PosDef)
    (c : ι → ℂ) :
    let S : Matrix ι ι ℝ := A - Gᵀ * (1 + B)⁻¹ * G
    (∫ x : ι → ℝ,
        Complex.exp
            (-(((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) / 2) +
              ∑ i, c i * (x i : ℂ)) *
          (∫ b : κ → ℝ,
              Complex.exp
                (-(((b ⬝ᵥ (B *ᵥ b) : ℝ) : ℂ) / 2) +
                  ∑ j, ((G *ᵥ x) j : ℂ) * (b j : ℂ))
              ∂(standardGaussianPi κ))
        ∂(standardGaussianPi ι)) =
      (((Real.sqrt (Matrix.det (1 + B)))⁻¹ *
          (Real.sqrt (Matrix.det (1 + S)))⁻¹ : ℝ)) •
        Complex.exp
          ((c ⬝ᵥ (((1 + S)⁻¹).map Complex.ofRealHom *ᵥ c)) / 2) := by
  dsimp only
  let S : Matrix ι ι ℝ := A - Gᵀ * (1 + B)⁻¹ * G
  let rB : ℝ := (Real.sqrt (Matrix.det (1 + B)))⁻¹
  have hinner (x : ι → ℝ) :
      (∫ b : κ → ℝ,
          Complex.exp
            (-(((b ⬝ᵥ (B *ᵥ b) : ℝ) : ℂ) / 2) +
              ∑ j, ((G *ᵥ x) j : ℂ) * (b j : ℂ))
          ∂(standardGaussianPi κ)) =
        rB • Complex.exp
          ((((x ⬝ᵥ ((Gᵀ * (1 + B)⁻¹ * G) *ᵥ x) : ℝ) : ℂ)) / 2) := by
    rw [integral_cexp_symmetricQuadratic_standardGaussianPi B hB
      (fun j => ((G *ᵥ x) j : ℂ))]
    rw [coupledSource_bilinear_eq_schurQuadratic]
  have heff (x : ι → ℝ) :
      Complex.exp
          (-(((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) / 2) +
            ∑ i, c i * (x i : ℂ)) *
        Complex.exp
          ((((x ⬝ᵥ ((Gᵀ * (1 + B)⁻¹ * G) *ᵥ x) : ℝ) : ℂ)) / 2) =
      Complex.exp
        (-(((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) / 2) +
          ∑ i, c i * (x i : ℂ)) := by
    have hquad :
        x ⬝ᵥ (S *ᵥ x) =
          x ⬝ᵥ (A *ᵥ x) -
            x ⬝ᵥ ((Gᵀ * (1 + B)⁻¹ * G) *ᵥ x) := by
      simp only [S, Matrix.sub_mulVec, dotProduct]
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [← Complex.exp_add]
    congr 1
    rw [hquad]
    push_cast
    ring
  calc
    (∫ x : ι → ℝ,
        Complex.exp
            (-(((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) / 2) +
              ∑ i, c i * (x i : ℂ)) *
          (∫ b : κ → ℝ,
              Complex.exp
                (-(((b ⬝ᵥ (B *ᵥ b) : ℝ) : ℂ) / 2) +
                  ∑ j, ((G *ᵥ x) j : ℂ) * (b j : ℂ))
              ∂(standardGaussianPi κ))
        ∂(standardGaussianPi ι)) =
      ∫ x : ι → ℝ,
        rB • Complex.exp
          (-(((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) / 2) +
            ∑ i, c i * (x i : ℂ))
        ∂(standardGaussianPi ι) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [hinner x]
          rw [← heff x]
          simp only [Complex.real_smul]
          ring
    _ = rB •
        (∫ x : ι → ℝ,
          Complex.exp
            (-(((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) / 2) +
              ∑ i, c i * (x i : ℂ))
          ∂(standardGaussianPi ι)) :=
      MeasureTheory.integral_smul rB _
    _ = rB •
        (((Real.sqrt (Matrix.det (1 + S)))⁻¹ : ℝ) •
          Complex.exp
            ((c ⬝ᵥ (((1 + S)⁻¹).map Complex.ofRealHom *ᵥ c)) / 2)) := by
      rw [integral_cexp_symmetricQuadratic_standardGaussianPi S hS c]
    _ = (((Real.sqrt (Matrix.det (1 + B)))⁻¹ *
          (Real.sqrt (Matrix.det (1 + S)))⁻¹ : ℝ)) •
        Complex.exp
          ((c ⬝ᵥ (((1 + S)⁻¹).map Complex.ofRealHom *ᵥ c)) / 2) := by
      exact smul_smul _ _ _

end

end YangMills.RG
