/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214GammaComplement
import YangMills.RG.PhysicalShellLocalityQ
import YangMills.RG.PhysicalCoerciveCombesThomas

/-!
# CMP116 equation (2.14): a concrete flat-background bound for Delta_k

The strongest equation-(2.14) reduction still receives a uniform operator-norm
bound for the physical Hessian `Delta_k`.  This module discharges that input in
the exactly identified trivial-background sector.

At `U = 1` the source operator is the finite physical precision

`Delta_flat = K_0 + a Q^* Q`.

The existing physical shell proves range `3M` and entrywise block bound

`(4d)^2 + 4 + |a| M^2`.

The block Schur estimate and the explicit bond-ball count therefore give the
volume-independent operator bound

`||Delta_flat|| <= ((4d)^2 + 4 + |a| M^2) (2(3M+1))^d d`.

The physical/CMP116 coordinate dictionary is an exact `L2` isometry, so the
same constant bounds the canonical finite matrix with no condition-number
loss.  The final theorem consumes that concrete matrix in the printed source
composition

`Gamma_k = C^* Delta_k (C Z0^c) (C^(k))^(1/2)`.

**Source boundary.**  Bałaban, CMP 99 (1985), (3.26), identifies the
trivial-background operator with the flat gauge-fixed precision; CMP 96
(1984), (2.152)--(2.157), supplies the constrained Gaussian setting; CMP 116
(1987), (2.14), supplies the Gamma composition.  This file does not extend the
bound to complex contour backgrounds, construct the constraint-elimination
operator `C`, prove the remaining domination estimates, or close (2.26).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Explicit, volume-independent Schur bound for the flat CMP116 Hessian. -/
def cmp116Eq214FlatDeltaNormBound (d M : ℕ) (a : ℝ) : ℝ :=
  ((((4 * d : ℕ) : ℝ) ^ 2 + (2 : ℝ) ^ 2) + |a| * (M : ℝ) ^ 2) *
    ((((2 * (3 * M + 1)) ^ d * d : ℕ) : ℝ))

/-- The concrete flat precision `K_0 + a Q^*Q` has an operator norm bounded
independently of the periodic volume `N'`. -/
theorem norm_flatCMP116DeltaCLM_le
    {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (rho : SUNAdjointModel Nc) (a : ℝ) :
    ‖gaugeFixedBasePrecisionCLM
        (flatGaugeHodgeK0CLM d (M * N') Nc rho)
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) M N') a‖ ≤
      cmp116Eq214FlatDeltaNormBound d M a := by
  unfold cmp116Eq214FlatDeltaNormBound
  exact physicalOpNorm_le_of_kernelBound_finiteRange
    physicalBondDist physicalBondDist_comm
    (R := 3 * M) (NR := (2 * (3 * M + 1)) ^ d * d)
    (β := (((4 * d : ℕ) : ℝ) ^ 2 + (2 : ℝ) ^ 2) + |a| * (M : ℝ) ^ 2)
    (by positivity)
    (fun x => physicalBondDist_ball_card_le x (3 * M))
    (flatBasePrecision_finiteRange rho a)
    (flatBasePrecision_kernelBound rho a)

variable
  {d M N' Nc L lieDim : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc] [NeZero L] [NeZero lieDim]

/-- The canonical CMP116 matrix of the concrete flat physical Hessian. -/
def PhysicalGaugeCMP116Dictionary.cmp116Eq214FlatDeltaMatrix
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (rho : SUNAdjointModel Nc) (a : ℝ) :
    Matrix (CMP116CoordIndex d L lieDim) (CMP116CoordIndex d L lieDim) ℝ :=
  Dict.physicalRootMatrix
    (gaugeFixedBasePrecisionCLM
      (flatGaugeHodgeK0CLM d (M * N') Nc rho)
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) M N') a)

omit [NeZero lieDim] in
/-- Isometric coordinate transport preserves the concrete flat Hessian bound
verbatim at the finite matrix level. -/
theorem PhysicalGaugeCMP116Dictionary.norm_cmp116Eq214FlatDeltaMatrix_le
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (rho : SUNAdjointModel Nc) (a : ℝ) :
    ‖Dict.cmp116Eq214FlatDeltaMatrix rho a‖ ≤
      cmp116Eq214FlatDeltaNormBound d M a := by
  rw [PhysicalGaugeCMP116Dictionary.cmp116Eq214FlatDeltaMatrix,
    Dict.norm_physicalRootMatrix]
  exact norm_flatCMP116DeltaCLM_le rho a

omit [NeZero lieDim] in
/-- The literal Gamma source with the concrete flat Hessian needs no abstract
`deltaNorm` premise. -/
theorem norm_cmp116Eq214GammaComplement_flatDeltaMatrix_sq_le
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (rho : SUNAdjointModel Nc) (a : ℝ)
    (C root : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ)
    (localizedCoordinates : Finset (CMP116CoordIndex d L lieDim))
    (CNorm rootNorm : ℝ)
    (hC : ‖C‖ ≤ CNorm)
    (hroot : ‖root‖ ≤ rootNorm) :
    ‖cmp116Eq214GammaMatrix C
        (Dict.cmp116Eq214FlatDeltaMatrix rho a)
        (cmp116Eq214ComplementLocalizedC C localizedCoordinates) root‖ ^ 2 ≤
      cmp116Eq214GammaComplementSourceRate CNorm
        (cmp116Eq214FlatDeltaNormBound d M a) rootNorm := by
  exact norm_cmp116Eq214GammaComplementMatrix_sq_le
    C (Dict.cmp116Eq214FlatDeltaMatrix rho a) root localizedCoordinates
    CNorm (cmp116Eq214FlatDeltaNormBound d M a) rootNorm
    hC (Dict.norm_cmp116Eq214FlatDeltaMatrix_le rho a) hroot

variable
  {nDelta nY : ℕ}
  {Psi Phi E : Type*} [Norm E]

namespace CMP116Eq214FiniteGaussianData

set_option maxHeartbeats 800000 in
/-- Full equation-(2.14) reduction in the concrete trivial-background Hessian
sector.  The public interface contains neither a Hessian matrix family nor an
abstract Hessian norm premise: both are produced by the flat physical shell. -/
theorem norm_term_le_cauchyRate_of_physicalGammaComplement_flatDelta_expCard
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
    (rho : SUNAdjointModel Nc) (a : ℝ)
    (Y0 P : Finset (Cube d L))
    (Z0 : Finset (FinBox d N'))
    (psi : Psi) (phi : Phi)
    (alpha5 outerBound CNorm : ℝ)
    (C : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hbeta : 2 *
      (cmp116Eq225SourceCoefficient (Dict.physicalRootMatrix root) alpha5 *
        cmp116Eq214GammaComplementSourceRate CNorm
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
              (cmp116Eq214GammaMatrix (C sigma tau)
                (Dict.cmp116Eq214FlatDeltaMatrix rho a)
                (Dict.cmp116Eq214PhysicalComplementLocalizedC Z0 (C sigma tau))
                (Dict.physicalRootMatrix root) *ᵥ
                  (cmp116Eq223CoordinateProjection
                    (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x)) b)
    (hC : ∀ sigma tau, ‖C sigma tau‖ ≤ CNorm) :
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
                    cmp116Eq214GammaComplementSourceRate CNorm
                      (cmp116Eq214FlatDeltaNormBound d M a) rootNormBound) *
                (Z0.card : ℝ)))) := by
  apply G.norm_term_le_cauchyRate_of_physicalGammaComplement_expCard
    Dict hcert Y0 P Z0 psi phi alpha5 outerBound CNorm
      (cmp116Eq214FlatDeltaNormBound d M a) C
      (fun _sigma _tau => Dict.cmp116Eq214FlatDeltaMatrix rho a)
      hDelta hY halpha5 hsmall hbeta houter_nonneg houter hdom hC
  intro sigma tau
  exact Dict.norm_cmp116Eq214FlatDeltaMatrix_le rho a

end CMP116Eq214FiniteGaussianData

end
end YangMills.RG
