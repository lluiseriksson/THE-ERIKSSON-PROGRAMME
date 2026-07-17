/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214FlatDeltaBound
import YangMills.RG.BalabanCMP96ConstraintNorm

/-!
# CMP116 equation (2.14): the physical constraint-elimination matrix

CMP96/CMP99 write the constrained field as `B = C Btilde`.  The physical
operator constructed in `BalabanCMP96ConstraintElimination` is the padded
projection `C = I - E Q`; its restriction to fields vanishing at the pivot
bonds is the rectangular reduced-coordinate map.

This file conjugates that concrete operator by the exact CMP116/physical
coordinate isometry.  It proves the volume-independent matrix bound

`||C_cmp116|| <= 1 + M^(d-1)`

and consumes the matrix in the strongest flat-background Gamma reduction.
Consequently that endpoint no longer accepts an arbitrary `C`, a scalar
`CNorm`, or a proof bounding it.

Honest scope: the padded realization does not by itself prove the reduced
Gaussian measure/Jacobian formula.  The remaining physical domination and
the full ledger (2.26) are not proved here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc L lieDim : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc] [NeZero L] [NeZero lieDim]

/-- Explicit volume-independent norm budget for the CMP96 elimination map. -/
def cmp116Eq214PhysicalConstraintNormBound (d M : ℕ) : ℝ :=
  1 + (M : ℝ) ^ (d - 1)

/-- The concrete CMP96 constraint-elimination operator in the scalar
coordinates used by CMP116. -/
def PhysicalGaugeCMP116Dictionary.cmp116Eq214PhysicalConstraintMatrix
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim) :
    Matrix (CMP116CoordIndex d L lieDim) (CMP116CoordIndex d L lieDim) ℝ :=
  Dict.physicalRootMatrix
    (cmp96ConstraintEliminationCLM
      (d := d) (L := M) (N' := N') (Nc := Nc))

omit [NeZero lieDim] in
/-- Isometric coordinate transport introduces no norm loss. -/
theorem PhysicalGaugeCMP116Dictionary.norm_cmp116Eq214PhysicalConstraintMatrix
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim) :
    ‖Dict.cmp116Eq214PhysicalConstraintMatrix‖ =
      ‖cmp96ConstraintEliminationCLM
        (d := d) (L := M) (N' := N') (Nc := Nc)‖ := by
  exact Dict.norm_physicalRootMatrix _

omit [NeZero lieDim] in
/-- The concrete CMP116 matrix has a norm bound independent of `N'`. -/
theorem PhysicalGaugeCMP116Dictionary.norm_cmp116Eq214PhysicalConstraintMatrix_le
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (hd : 3 ≤ d) :
    ‖Dict.cmp116Eq214PhysicalConstraintMatrix‖ ≤
      cmp116Eq214PhysicalConstraintNormBound d M := by
  rw [Dict.norm_cmp116Eq214PhysicalConstraintMatrix]
  exact norm_cmp96ConstraintEliminationCLM_le hd

omit [NeZero lieDim] in
/-- The matrix acts exactly as physical constraint elimination after applying
the coordinate dictionary. -/
theorem PhysicalGaugeCMP116Dictionary.cmp116Eq214PhysicalConstraintMatrix_action
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (x : EuclideanSpace ℝ (CMP116CoordIndex d L lieDim)) :
    Dict.flatPhysicalLinearIsometryEquiv
        ((Matrix.toEuclideanCLM
          (n := CMP116CoordIndex d L lieDim) (𝕜 := ℝ))
            Dict.cmp116Eq214PhysicalConstraintMatrix x) =
      cmp96ConstraintEliminationCLM
        (d := d) (L := M) (N' := N') (Nc := Nc)
          (Dict.flatPhysicalLinearIsometryEquiv x) := by
  exact Dict.physicalRootMatrix_action _ x

omit [NeZero lieDim] in
/-- The flat-background Gamma source with both the Hessian and the physical
constraint coordinates fixed definitionally. -/
theorem norm_cmp116Eq214Gamma_physicalConstraint_flatDeltaMatrix_sq_le
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (hd : 3 ≤ d) (rho : SUNAdjointModel Nc) (a : ℝ)
    (root : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ)
    (localizedCoordinates : Finset (CMP116CoordIndex d L lieDim))
    (rootNorm : ℝ)
    (hroot : ‖root‖ ≤ rootNorm) :
    ‖cmp116Eq214GammaMatrix Dict.cmp116Eq214PhysicalConstraintMatrix
        (Dict.cmp116Eq214FlatDeltaMatrix rho a)
        (cmp116Eq214ComplementLocalizedC
          Dict.cmp116Eq214PhysicalConstraintMatrix localizedCoordinates)
        root‖ ^ 2 ≤
      cmp116Eq214GammaComplementSourceRate
        (cmp116Eq214PhysicalConstraintNormBound d M)
        (cmp116Eq214FlatDeltaNormBound d M a) rootNorm := by
  exact norm_cmp116Eq214GammaComplement_flatDeltaMatrix_sq_le
    Dict rho a Dict.cmp116Eq214PhysicalConstraintMatrix root
    localizedCoordinates (cmp116Eq214PhysicalConstraintNormBound d M)
    rootNorm (Dict.norm_cmp116Eq214PhysicalConstraintMatrix_le hd) hroot

variable {nDelta nY : ℕ}
  {Psi Phi E : Type*} [Norm E]

namespace CMP116Eq214FiniteGaussianData

set_option maxHeartbeats 800000 in
/-- Strong flat-background reduction with the physical CMP96 constraint map
inserted internally.  No arbitrary `C`, `CNorm`, or `hC` remains. -/
theorem norm_term_le_cauchyRate_of_physicalConstraintGamma_flatDelta_expCard
    (G : CMP116Eq214FiniteGaussianData nDelta nY
      (Cube d L) Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
        PhysicalGaugeOneCochain d (M * N') Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond d (M * N') → PhysicalBond d (M * N') → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (hd : 3 ≤ d) (rho : SUNAdjointModel Nc) (a : ℝ)
    (Y0 P : Finset (Cube d L))
    (Z0 : Finset (FinBox d N'))
    (psi : Psi) (phi : Phi)
    (alpha5 outerBound : ℝ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hbeta : 2 *
      (cmp116Eq225SourceCoefficient (Dict.physicalRootMatrix root) alpha5 *
        cmp116Eq214GammaComplementSourceRate
          (cmp116Eq214PhysicalConstraintNormBound d M)
          (cmp116Eq214FlatDeltaNormBound d M a) rootNormBound) < 1)
    (houter_nonneg : 0 ≤ outerBound)
    (houter : ∀ sigma tau x,
      ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hdom : ∀ sigma tau x,
      ∀ᵐ b ∂matrixGaussianPi (Dict.physicalRootMatrix root),
        ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.innerIntegrand
          Y0 P sigma tau psi phi x b‖ ≤
            cmp116Eq223RealGaussian
              (-(alpha5 • cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)))
              (cmp116Eq214GammaMatrix
                Dict.cmp116Eq214PhysicalConstraintMatrix
                (Dict.cmp116Eq214FlatDeltaMatrix rho a)
                (Dict.cmp116Eq214PhysicalComplementLocalizedC Z0
                  Dict.cmp116Eq214PhysicalConstraintMatrix)
                (Dict.physicalRootMatrix root) *ᵥ
                  (cmp116Eq223CoordinateProjection
                    (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x)) b) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta G.deltaRadius
        (cmp116Eq214CauchyRate nY G.yRadius
          (outerBound *
            Real.exp
              (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
                M d Nc (Dict.physicalRootMatrix root) alpha5
                (cmp116Eq225SourceCoefficient
                  (Dict.physicalRootMatrix root) alpha5 *
                    cmp116Eq214GammaComplementSourceRate
                      (cmp116Eq214PhysicalConstraintNormBound d M)
                      (cmp116Eq214FlatDeltaNormBound d M a) rootNormBound) *
                (Z0.card : ℝ)))) := by
  apply G.norm_term_le_cauchyRate_of_physicalGammaComplement_flatDelta_expCard
    Dict hcert rho a Y0 P Z0 psi phi alpha5 outerBound
      (cmp116Eq214PhysicalConstraintNormBound d M)
      (fun _sigma _tau => Dict.cmp116Eq214PhysicalConstraintMatrix)
      hDelta hY halpha5 hsmall hbeta houter_nonneg houter
  · simpa using hdom
  · intro sigma tau
    exact Dict.norm_cmp116Eq214PhysicalConstraintMatrix_le hd

end CMP116Eq214FiniteGaussianData

end
end YangMills.RG
