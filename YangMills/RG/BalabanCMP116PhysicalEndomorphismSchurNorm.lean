/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116PhysicalEndomorphismMatrixReconstruction
import YangMills.RG.BalabanCMP116ComplexSourceSchur

/-!
# Bilateral Schur norm for reconstructed physical endomorphisms

The canonical bond--Lie coordinate reconstruction is an exact `L²`
isometry.  Consequently a bilateral row/column Schur estimate for a complex
coordinate matrix controls the genuine Hilbert-space operator norm of the
real physical endomorphism reconstructed from its real part.
-/

namespace YangMills.RG

open scoped Matrix.Norms.Operator

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The canonical flattened bond--Lie coordinates as a Euclidean linear
equivalence. -/
noncomputable def cmp116PhysicalCoordinateEuclideanLinearEquiv
    {d N Nc : ℕ} [NeZero N] :
    EuclideanSpace ℝ (CMP116PhysicalWalkCoordinate d N Nc) ≃ₗ[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  (WithLp.linearEquiv 2 ℝ
      (CMP116PhysicalWalkCoordinate d N Nc → ℝ)).trans
    cmp116PhysicalCoordinateLinearEquiv

/-- Flattening all positive-bond Lie coordinates preserves the physical
`L²` norm exactly. -/
theorem norm_cmp116PhysicalCoordinateEuclideanLinearEquiv
    {d N Nc : ℕ} [NeZero N]
    (x : EuclideanSpace ℝ
      (CMP116PhysicalWalkCoordinate d N Nc)) :
    ‖cmp116PhysicalCoordinateEuclideanLinearEquiv x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, EuclideanSpace.real_norm_sq_eq]
  simp only [cmp116PhysicalCoordinateEuclideanLinearEquiv,
    LinearEquiv.trans_apply, WithLp.linearEquiv_apply,
    cmp116PhysicalCoordinateLinearEquiv,
    EuclideanSpace.real_norm_sq_eq]
  change
    (∑ bond : PhysicalBond d N, ∑ a : Fin (Nc ^ 2 - 1),
      x (bond, a) ^ 2) =
      ∑ qa : CMP116PhysicalWalkCoordinate d N Nc, x qa ^ 2
  exact (Fintype.sum_prod_type
    (fun qa : PhysicalBond d N × Fin (Nc ^ 2 - 1) => x qa ^ 2)).symm

/-- The canonical coordinate dictionary as a real linear isometric
equivalence. -/
noncomputable def cmp116PhysicalCoordinateLinearIsometryEquiv
    {d N Nc : ℕ} [NeZero N] :
    EuclideanSpace ℝ (CMP116PhysicalWalkCoordinate d N Nc) ≃ₗᵢ[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  LinearIsometryEquiv.ofBounds
    cmp116PhysicalCoordinateEuclideanLinearEquiv
    (fun x => (norm_cmp116PhysicalCoordinateEuclideanLinearEquiv x).le)
    (fun A => by
      have h := norm_cmp116PhysicalCoordinateEuclideanLinearEquiv
        (cmp116PhysicalCoordinateEuclideanLinearEquiv.symm A)
      simpa using h.symm.le)

/-- Reconstruction is exactly conjugation of the entrywise-real coordinate
matrix by the canonical physical `L²` isometry. -/
theorem cmp116PhysicalCoordinateLinearIsometryEquiv_symm_reconstruction
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (A : Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ)
    (x : PhysicalGaugeOneCochain d N Nc) :
    cmp116PhysicalCoordinateLinearIsometryEquiv.symm
        (cmp116PhysicalEndomorphismOfComplexMatrixCLM A x) =
      ((Matrix.toEuclideanCLM
        (n := CMP116PhysicalWalkCoordinate d N Nc) (𝕜 := ℝ))
        (cmp116Eq214RealPartMatrix A))
        (cmp116PhysicalCoordinateLinearIsometryEquiv.symm x) := by
  let E :=
    cmp116PhysicalCoordinateLinearIsometryEquiv
      (d := d) (N := N) (Nc := Nc)
  have hE (z : EuclideanSpace ℝ
      (CMP116PhysicalWalkCoordinate d N Nc)) :
      E z = cmp116PhysicalCoordinateEuclideanLinearEquiv z := rfl
  have hcoords :
      ((E.symm x :
          EuclideanSpace ℝ (CMP116PhysicalWalkCoordinate d N Nc)) :
        CMP116PhysicalWalkCoordinate d N Nc → ℝ) =
        cmp116PhysicalCoordinateLinearEquiv.symm x := by
    apply cmp116PhysicalCoordinateLinearEquiv.injective
    rw [cmp116PhysicalCoordinateLinearEquiv.apply_symm_apply]
    have hx : E (E.symm x) = x := E.apply_symm_apply x
    rw [hE] at hx
    simpa [cmp116PhysicalCoordinateEuclideanLinearEquiv] using hx
  apply E.injective
  rw [E.apply_symm_apply]
  change
    cmp116PhysicalCoordinateLinearEquiv
        (Matrix.mulVec (fun i j => (A i j).re)
          (cmp116PhysicalCoordinateLinearEquiv.symm x)) =
      E (((Matrix.toEuclideanCLM
          (n := CMP116PhysicalWalkCoordinate d N Nc) (𝕜 := ℝ))
        (cmp116Eq214RealPartMatrix A)) (E.symm x))
  rw [hE]
  change
    cmp116PhysicalCoordinateLinearEquiv
        (Matrix.mulVec (fun i j => (A i j).re)
          (cmp116PhysicalCoordinateLinearEquiv.symm x)) =
      cmp116PhysicalCoordinateLinearEquiv
        (((Matrix.toEuclideanCLM
          (n := CMP116PhysicalWalkCoordinate d N Nc) (𝕜 := ℝ))
        (cmp116Eq214RealPartMatrix A)) (E.symm x))
  congr 1

/-- A common row/column bound for a complex coordinate kernel controls the
genuine physical `L²` operator norm reconstructed from its real part. -/
theorem norm_cmp116PhysicalEndomorphismOfComplexMatrixCLM_le_of_bilateral
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (A : Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hrow : ‖A‖ ≤ bound) (hcol : ‖A.transpose‖ ≤ bound) :
    ‖cmp116PhysicalEndomorphismOfComplexMatrixCLM A‖ ≤ bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ hbound
  intro x
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hbound (norm_nonneg _))).mp
  rw [mul_pow]
  let y :=
    cmp116PhysicalCoordinateLinearIsometryEquiv.symm x
  have haction :
      cmp116PhysicalCoordinateLinearIsometryEquiv.symm
          (cmp116PhysicalEndomorphismOfComplexMatrixCLM A x) =
        ((Matrix.toEuclideanCLM
          (n := CMP116PhysicalWalkCoordinate d N Nc) (𝕜 := ℝ))
          (cmp116Eq214RealPartMatrix A)) y := by
    exact
      cmp116PhysicalCoordinateLinearIsometryEquiv_symm_reconstruction A x
  have hschur :=
    dotProduct_realPart_mulVec_self_le_linfty_bilateral A y
  have hmatrix :
      ‖((Matrix.toEuclideanCLM
          (n := CMP116PhysicalWalkCoordinate d N Nc) (𝕜 := ℝ))
          (cmp116Eq214RealPartMatrix A)) y‖ ^ 2 ≤
        ‖A‖ * ‖A.transpose‖ * ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    simpa [dotProduct, pow_two] using hschur
  calc
    ‖cmp116PhysicalEndomorphismOfComplexMatrixCLM A x‖ ^ 2 =
        ‖((Matrix.toEuclideanCLM
          (n := CMP116PhysicalWalkCoordinate d N Nc) (𝕜 := ℝ))
          (cmp116Eq214RealPartMatrix A)) y‖ ^ 2 := by
      rw [← cmp116PhysicalCoordinateLinearIsometryEquiv.symm.norm_map,
        haction]
    _ ≤ ‖A‖ * ‖A.transpose‖ * ‖y‖ ^ 2 := hmatrix
    _ ≤ bound ^ 2 * ‖y‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · have hmul :
            ‖A‖ * ‖A.transpose‖ ≤ bound * bound :=
          mul_le_mul hrow hcol (norm_nonneg _) hbound
        simpa [pow_two] using hmul
      · positivity
    _ = bound ^ 2 * ‖x‖ ^ 2 := by
      rw [cmp116PhysicalCoordinateLinearIsometryEquiv.symm.norm_map]

end

end YangMills.RG
