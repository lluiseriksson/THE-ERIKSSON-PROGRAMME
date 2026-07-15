/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223PhysicalCovarianceMatrix
import YangMills.RG.PhysicalGaugeCovarianceLocalization

/-!
# CMP116 equation (2.23): exact physical-root norm bridge

The physical covariance-root certificate controls the operator norm on physical
one-cochains, whereas the exact Gaussian evaluator uses the `L²` operator norm
of a finite scalar matrix.  This module proves that the scalar-coordinate
dictionary is an exact `L²` isometry and therefore transports the root with no
condition-number loss.

For the canonical physical matrix constructed here,

`‖physicalRootMatrix D root‖ = ‖root‖`.

Consequently the `root_norm_bound` field of
`PhysicalLocalizedCovarianceRootCertificate`, together with the scalar source
smallness `alpha * rootNormBound² < 1`, directly proves positivity of the
localized shifted Hessian required by CMP116 (2.23)--(2.24).

Honest scope: the module consumes the source root certificate and scalar
smallness condition.  It does not construct that certificate, identify
`alpha` with the source's `alpha5`, prove domination (2.20)--(2.22), or bound
the final majorant in (2.26).
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

namespace PhysicalGaugeCMP116Dictionary

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- Pulling flattened CMP116 scalar coordinates through the physical
dictionary preserves the `L²` norm exactly. -/
theorem norm_pullFluctuationCochain_flat
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (x : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim)) :
    ‖D.pullFluctuationCochain (fun q a => x (q, a))‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, EuclideanSpace.real_norm_sq_eq]
  simp only [pullFluctuationCochain, PiLp.toLp_apply,
    sunLieCoordOfScalars, EuclideanSpace.real_norm_sq_eq]
  change
    (∑ b : PhysicalBond dPhys N, ∑ a : Fin (Nc ^ 2 - 1),
      x (D.coordEquiv.symm (b, a)) ^ 2) =
      ∑ qa, x qa ^ 2
  simpa only [Fintype.sum_prod_type] using
    Equiv.sum_comp D.coordEquiv.symm (fun qa => x qa ^ 2)

/-- The linear coordinate equivalence from flattened CMP116 Euclidean
coordinates to physical one-cochains. -/
noncomputable def flatPhysicalLinearEquiv
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim) :
    EuclideanSpace ℝ (CMP116CoordIndex d L lieDim) ≃ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc where
  toFun x := D.pullFluctuationCochain (fun q a => x (q, a))
  invFun A := WithLp.toLp 2 (fun qa => D.pushFluctuation A qa.1 qa.2)
  left_inv x := by
    apply PiLp.ext
    intro qa
    simp
  right_inv A := D.pullFluctuationCochain_pushFluctuation A
  map_add' x y := by
    exact D.pullFluctuationCochain_add
      (fun q a => x (q, a)) (fun q a => y (q, a))
  map_smul' c x := by
    exact D.pullFluctuationCochain_smul c (fun q a => x (q, a))

/-- Norm form of the exact dictionary isometry. -/
theorem norm_flatPhysicalLinearEquiv
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (x : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim)) :
    ‖D.flatPhysicalLinearEquiv x‖ = ‖x‖ := by
  exact D.norm_pullFluctuationCochain_flat x

/-- The physical scalar-coordinate dictionary as an exact real linear
isometric equivalence. -/
noncomputable def flatPhysicalLinearIsometryEquiv
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim) :
    EuclideanSpace ℝ (CMP116CoordIndex d L lieDim) ≃ₗᵢ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc :=
  LinearIsometryEquiv.ofBounds D.flatPhysicalLinearEquiv
    (fun x => (D.norm_flatPhysicalLinearEquiv x).le)
    (fun A => by
      have h := D.norm_flatPhysicalLinearEquiv
        (D.flatPhysicalLinearEquiv.symm A)
      simpa using h.symm.le)

/-- Conjugate the physical covariance root by the exact `L²` coordinate
isometry. -/
noncomputable def flatPhysicalRootCLM
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc) :
    EuclideanSpace ℝ (CMP116CoordIndex d L lieDim) →L[ℝ]
      EuclideanSpace ℝ (CMP116CoordIndex d L lieDim) :=
  D.flatPhysicalLinearIsometryEquiv.symm.toContinuousLinearMap.comp
    (root.comp D.flatPhysicalLinearIsometryEquiv.toContinuousLinearMap)

/-- Isometric conjugation preserves the physical covariance-root operator
norm exactly. -/
theorem norm_flatPhysicalRootCLM
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc) :
    ‖D.flatPhysicalRootCLM root‖ = ‖root‖ := by
  apply le_antisymm
  · refine (D.flatPhysicalRootCLM root).opNorm_le_bound (norm_nonneg _) ?_
    intro x
    calc
      ‖D.flatPhysicalRootCLM root x‖ =
          ‖root (D.flatPhysicalLinearIsometryEquiv x)‖ := by
            simp [flatPhysicalRootCLM]
      _ ≤ ‖root‖ * ‖D.flatPhysicalLinearIsometryEquiv x‖ :=
        root.le_opNorm _
      _ = ‖root‖ * ‖x‖ := by
        rw [D.flatPhysicalLinearIsometryEquiv.norm_map]
  · refine root.opNorm_le_bound (norm_nonneg _) ?_
    intro y
    calc
      ‖root y‖ = ‖D.flatPhysicalLinearIsometryEquiv
          (D.flatPhysicalRootCLM root
            (D.flatPhysicalLinearIsometryEquiv.symm y))‖ := by
              simp [flatPhysicalRootCLM]
      _ = ‖D.flatPhysicalRootCLM root
            (D.flatPhysicalLinearIsometryEquiv.symm y)‖ :=
        D.flatPhysicalLinearIsometryEquiv.norm_map _
      _ ≤ ‖D.flatPhysicalRootCLM root‖ *
            ‖D.flatPhysicalLinearIsometryEquiv.symm y‖ :=
        (D.flatPhysicalRootCLM root).le_opNorm _
      _ = ‖D.flatPhysicalRootCLM root‖ * ‖y‖ := by
        rw [D.flatPhysicalLinearIsometryEquiv.symm.norm_map]

/-- The canonical finite `L²` matrix of the certified physical covariance
root in the dictionary coordinates. -/
noncomputable def physicalRootMatrix
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc) :
    Matrix (CMP116CoordIndex d L lieDim) (CMP116CoordIndex d L lieDim) ℝ :=
  (Matrix.toEuclideanCLM
    (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ)).symm
      (D.flatPhysicalRootCLM root)

/-- The finite matrix norm equals the original physical root norm, with no
dictionary condition-number loss. -/
theorem norm_physicalRootMatrix
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc) :
    ‖D.physicalRootMatrix root‖ = ‖root‖ := by
  calc
    ‖D.physicalRootMatrix root‖ =
        ‖(Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
            (D.physicalRootMatrix root)‖ :=
      (Matrix.l2_opNorm_toEuclideanCLM _).symm
    _ = ‖D.flatPhysicalRootCLM root‖ := by
      congr 1
      exact (Matrix.toEuclideanCLM
        (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ)).apply_symm_apply
          (D.flatPhysicalRootCLM root)
    _ = ‖root‖ := D.norm_flatPhysicalRootCLM root

/-- The canonical finite matrix acts exactly as the physical root after the
isometric coordinate identification. -/
theorem physicalRootMatrix_action
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    (x : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim)) :
    D.flatPhysicalLinearIsometryEquiv
        ((Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
            (D.physicalRootMatrix root) x) =
      root (D.flatPhysicalLinearIsometryEquiv x) := by
  have hmatrix :
      (Matrix.toEuclideanCLM
        (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
          (D.physicalRootMatrix root) =
        D.flatPhysicalRootCLM root := by
    exact (Matrix.toEuclideanCLM
      (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ)).apply_symm_apply _
  rw [hmatrix]
  simp [flatPhysicalRootCLM]

/-- The source certificate's physical root-norm field bounds the canonical
finite Gaussian matrix verbatim. -/
theorem norm_physicalRootMatrix_le_of_covarianceRootCertificate
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight) :
    ‖D.physicalRootMatrix root‖ ≤ rootNormBound := by
  rw [D.norm_physicalRootMatrix root]
  exact hcert.root_norm_bound

/-- For a certified self-adjoint square root, the squared root norm is exactly
the covariance norm.  This is the operator C-star identity specialized to the
source identity `root.comp root = covariance`. -/
theorem norm_root_sq_eq_covariance_of_certificate
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight) :
    ‖root‖ ^ 2 = ‖covariance‖ := by
  have hsymm : root.IsSymmetric := by
    intro x y
    exact (hcert.root_selfAdjoint_form x y).symm
  have hadjoint : ContinuousLinearMap.adjoint root = root :=
    hsymm.clm_adjoint_eq
  calc
    ‖root‖ ^ 2 = ‖(ContinuousLinearMap.adjoint root).comp root‖ := by
      rw [pow_two, ContinuousLinearMap.norm_adjoint_comp_self]
    _ = ‖root.comp root‖ := by rw [hadjoint]
    _ = ‖covariance‖ := by rw [hcert.root_square]

/-- The canonical finite Gaussian matrix satisfies the same exact C-star
identity as the certified physical covariance root. -/
theorem norm_physicalRootMatrix_sq_eq_covariance
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight) :
    ‖D.physicalRootMatrix root‖ ^ 2 = ‖covariance‖ := by
  rw [D.norm_physicalRootMatrix root]
  exact norm_root_sq_eq_covariance_of_certificate hcert

/-- The covariance-norm certificate, rather than a separately chosen root
bound, is sufficient for the localized positive-definite Hessian. -/
theorem posDef_physicalRootMatrix_of_covarianceNorm_small
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (S : Finset (CMP116CoordIndex d L lieDim))
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hsmall : alpha * covNormBound < 1) :
    (1 - (D.physicalRootMatrix root)ᵀ *
      (alpha • cmp116Eq223CoordinateProjection S) *
      D.physicalRootMatrix root).PosDef := by
  have hmatrixSq : ‖D.physicalRootMatrix root‖ ^ 2 ≤ covNormBound := by
    rw [D.norm_physicalRootMatrix_sq_eq_covariance hcert]
    exact hcert.covariance_certificate.covariance_norm_bound
  exact posDef_one_sub_localized_covariance_of_l2_opNorm_small
    S (D.physicalRootMatrix root) alpha halpha
    ((mul_le_mul_of_nonneg_left hmatrixSq halpha).trans_lt hsmall)

/-- Literal source-facing half-smallness form used before CMP116 (2.24):
`alpha5 * covNormBound < 1/2` is stronger than the positivity threshold. -/
theorem posDef_physicalRootMatrix_of_alpha5_covariance_half_small
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (S : Finset (CMP116CoordIndex d L lieDim))
    (alpha5 : ℝ) (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2) :
    (1 - (D.physicalRootMatrix root)ᵀ *
      (alpha5 • cmp116Eq223CoordinateProjection S) *
      D.physicalRootMatrix root).PosDef := by
  apply D.posDef_physicalRootMatrix_of_covarianceNorm_small
    hcert S alpha5 halpha5
  exact hsmall.trans (by norm_num)

/-- The physical root certificate and source scalar smallness directly prove
the positive-definite shifted Hessian used in (2.23)--(2.24). -/
theorem posDef_physicalRootMatrix_of_covarianceRootCertificate_small
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (S : Finset (CMP116CoordIndex d L lieDim))
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hsmall : alpha * rootNormBound ^ 2 < 1) :
    (1 - (D.physicalRootMatrix root)ᵀ *
      (alpha • cmp116Eq223CoordinateProjection S) *
      D.physicalRootMatrix root).PosDef := by
  have hnorm := D.norm_physicalRootMatrix_le_of_covarianceRootCertificate hcert
  have hsquare : ‖D.physicalRootMatrix root‖ ^ 2 ≤
      rootNormBound ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  exact posDef_one_sub_localized_covariance_of_l2_opNorm_small
    S (D.physicalRootMatrix root) alpha halpha
    ((mul_le_mul_of_nonneg_left hsquare halpha).trans_lt hsmall)

end PhysicalGaugeCMP116Dictionary
end YangMills.RG
