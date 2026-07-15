/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214MainReduction

/-!
# CMP116 equation (2.14): the physical Gamma source

The linear source in Bałaban's equation (2.14) is

`Gamma_k (Z0, sigma) = C* Delta_k(sigma) C_Z0 (C^(k))^(1/2)(sigma)`.

Over real finite coordinates, `C*` is the transpose.  This module records the
literal four-factor matrix, proves its operator-norm estimate, and consumes it
in the strongest polymer-volume Gaussian reduction.  Consequently the public
endpoint no longer receives an abstract source matrix `J` or a separate `hJ`.

Honest scope: the concrete construction and uniform estimates for `C`,
`Delta_k`, and `C_Z0` remain source-specific inputs.  This module does not
prove the Wilson and `R1/R2/R3` kernel estimates or the full ledger (2.26).
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Literal finite-coordinate realization of the source operator in (2.14). -/
def cmp116Eq214GammaMatrix
    {ι : Type*} [Fintype ι]
    (C delta localizedC root : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Cᵀ * delta * localizedC * root

/-- The source matrix acts by the four operators in the printed order. -/
theorem cmp116Eq214GammaMatrix_mulVec
    {ι : Type*} [Fintype ι]
    (C delta localizedC root : Matrix ι ι ℝ) (x : ι → ℝ) :
    cmp116Eq214GammaMatrix C delta localizedC root *ᵥ x =
      Cᵀ *ᵥ (delta *ᵥ (localizedC *ᵥ (root *ᵥ x))) := by
  unfold cmp116Eq214GammaMatrix
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- Submultiplicative `L²` bound for the literal CMP116 source. -/
theorem norm_cmp116Eq214GammaMatrix_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C delta localizedC root : Matrix ι ι ℝ) :
    ‖cmp116Eq214GammaMatrix C delta localizedC root‖ ≤
      ‖C‖ * ‖delta‖ * ‖localizedC‖ * ‖root‖ := by
  unfold cmp116Eq214GammaMatrix
  have hCt : ‖Cᵀ‖ = ‖C‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose C
  calc
    ‖Cᵀ * delta * localizedC * root‖ ≤
        ‖Cᵀ * delta * localizedC‖ * ‖root‖ := norm_mul_le _ _
    _ ≤ (‖Cᵀ * delta‖ * ‖localizedC‖) * ‖root‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ((‖Cᵀ‖ * ‖delta‖) * ‖localizedC‖) * ‖root‖ := by
      gcongr
      exact norm_mul_le _ _
    _ = ‖C‖ * ‖delta‖ * ‖localizedC‖ * ‖root‖ := by rw [hCt]

/-- Uniform bounds for the four physical factors produce the squared source
rate consumed by equation (2.25). -/
theorem norm_cmp116Eq214GammaMatrix_sq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C delta localizedC root : Matrix ι ι ℝ)
    (CNorm deltaNorm localizedNorm rootNorm : ℝ)
    (hC : ‖C‖ ≤ CNorm)
    (hdelta : ‖delta‖ ≤ deltaNorm)
    (hlocalized : ‖localizedC‖ ≤ localizedNorm)
    (hroot : ‖root‖ ≤ rootNorm) :
    ‖cmp116Eq214GammaMatrix C delta localizedC root‖ ^ 2 ≤
      (CNorm * deltaNorm * localizedNorm * rootNorm) ^ 2 := by
  have hC0 : 0 ≤ CNorm := (norm_nonneg C).trans hC
  have hdelta0 : 0 ≤ deltaNorm := (norm_nonneg delta).trans hdelta
  have hlocalized0 : 0 ≤ localizedNorm :=
    (norm_nonneg localizedC).trans hlocalized
  have hroot0 : 0 ≤ rootNorm := (norm_nonneg root).trans hroot
  have hproduct :
      ‖C‖ * ‖delta‖ * ‖localizedC‖ * ‖root‖ ≤
        CNorm * deltaNorm * localizedNorm * rootNorm := by
    gcongr
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((norm_cmp116Eq214GammaMatrix_le C delta localizedC root).trans hproduct) 2

/-- Explicit uniform source rate obtained from the four physical factors. -/
def cmp116Eq214GammaSourceRate
    (CNorm deltaNorm localizedNorm rootNorm : ℝ) : ℝ :=
  (CNorm * deltaNorm * localizedNorm * rootNorm) ^ 2

variable
  {nDelta nY d M N' Nc L lieDim : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
  [NeZero Nc] [NeZero L] [NeZero lieDim]
  {Ψ Φ E : Type*} [Norm E]

namespace CMP116Eq214FiniteGaussianData

set_option maxHeartbeats 800000 in
/-- Strongest equation-(2.14) reduction with the source fixed definitionally
to `Gamma_k = C* Delta_k C_Z0 root`.  The abstract `J` and `hJ` inputs of the
generic linear-source endpoint have disappeared. -/
theorem norm_term_le_cauchyRate_of_physicalGammaSource_expCard
    (G : CMP116Eq214FiniteGaussianData nDelta nY
      (Cube d L) Ψ Φ E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
        PhysicalGaugeOneCochain d (M * N') Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond d (M * N') → PhysicalBond d (M * N') → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (Y0 P : Finset (Cube d L))
    (Z0 : Finset (FinBox d N'))
    (psi : Ψ) (phi : Φ)
    (alpha5 outerBound CNorm deltaNorm localizedNorm : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (C delta localizedC : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hbeta : 2 *
      (cmp116Eq225SourceCoefficient (Dict.physicalRootMatrix root) alpha5 *
        cmp116Eq214GammaSourceRate
          CNorm deltaNorm localizedNorm rootNormBound) < 1)
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
              (r sigma tau x) b)
    (hshape : ∀ sigma tau x,
      r sigma tau x =
        cmp116Eq214GammaMatrix (C sigma tau) (delta sigma tau)
            (localizedC sigma tau) (Dict.physicalRootMatrix root) *ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x))
    (hC : ∀ sigma tau, ‖C sigma tau‖ ≤ CNorm)
    (hdelta : ∀ sigma tau, ‖delta sigma tau‖ ≤ deltaNorm)
    (hlocalized : ∀ sigma tau, ‖localizedC sigma tau‖ ≤ localizedNorm) :
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
                    cmp116Eq214GammaSourceRate
                      CNorm deltaNorm localizedNorm rootNormBound) *
                (Z0.card : ℝ)))) := by
  let sourceRate := cmp116Eq214GammaSourceRate
    CNorm deltaNorm localizedNorm rootNormBound
  have hroot := Dict.norm_physicalRootMatrix_le_of_covarianceRootCertificate hcert
  have hsourceRate : 0 ≤ sourceRate := by
    unfold sourceRate cmp116Eq214GammaSourceRate
    positivity
  apply G.norm_term_le_cauchyRate_of_physicalGaussianReduction_linearSource_expCard
    Dict hcert Y0 P Z0 psi phi alpha5 outerBound sourceRate r
      (fun sigma tau => cmp116Eq214GammaMatrix
        (C sigma tau) (delta sigma tau) (localizedC sigma tau)
        (Dict.physicalRootMatrix root))
      hDelta hY halpha5 hsmall hsourceRate
      (by simpa [sourceRate] using hbeta) houter_nonneg houter hdom hshape
  intro sigma tau
  simpa [sourceRate, cmp116Eq214GammaSourceRate] using
    norm_cmp116Eq214GammaMatrix_sq_le
      (C sigma tau) (delta sigma tau) (localizedC sigma tau)
      (Dict.physicalRootMatrix root)
      CNorm deltaNorm localizedNorm rootNormBound
      (hC sigma tau) (hdelta sigma tau) (hlocalized sigma tau) hroot

end CMP116Eq214FiniteGaussianData

end
end YangMills.RG
