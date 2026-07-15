/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214GammaSource

/-!
# CMP116 equation (2.14): the complement-localized Gamma factor

The printed source operator contains the factor `C Z0^c`, not the conditioned
covariance `C^(k)(Z0)`.  In finite coordinates this module realizes that factor
as `C * P_(Z0^c)`, where `P_(Z0^c)` is the diagonal projection onto the explicit
complement carrier.  It proves that this restriction cannot increase the
`L²` operator norm and consumes the result in the strongest Gaussian reduction.

The terminal endpoint no longer receives an arbitrary `localizedC`, its norm
bound, an arbitrary source `r`, or a shape equality.  The source is literally

`Cᵀ * Delta_k * (C * P_(Z0^c)) * root * P_Z0 * X`.

Honest scope: identifying the explicit finite carrier with the precise CMP116
fine-lattice complement is a dictionary obligation.  The module does not prove
uniform bounds for `C`, `Delta_k`, or the remaining physical kernels, and it
does not close the full ledger (2.26).
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Finite-coordinate realization of the printed factor `C Z0^c`. -/
def cmp116Eq214ComplementLocalizedC
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (localizedCoordinates : Finset ι) : Matrix ι ι ℝ :=
  C * cmp116Eq223CoordinateProjection (Finset.univ \ localizedCoordinates)

/-- The complement-localized factor first restricts the input and then applies
`C`. -/
theorem cmp116Eq214ComplementLocalizedC_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (localizedCoordinates : Finset ι) (x : ι → ℝ) :
    cmp116Eq214ComplementLocalizedC C localizedCoordinates *ᵥ x =
      C *ᵥ (cmp116Eq223CoordinateProjection
        (Finset.univ \ localizedCoordinates) *ᵥ x) := by
  unfold cmp116Eq214ComplementLocalizedC
  rw [Matrix.mulVec_mulVec]

/-- A diagonal projection onto a complement carrier has `L²` operator norm at
most one. -/
theorem norm_cmp116Eq223ComplementProjection_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (localizedCoordinates : Finset ι) :
    ‖cmp116Eq223CoordinateProjection
        (Finset.univ \ localizedCoordinates)‖ ≤ (1 : ℝ) := by
  rw [cmp116Eq223CoordinateProjection, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 ?_
  intro i
  by_cases hi : i ∈ Finset.univ \ localizedCoordinates <;> simp [hi]

/-- Restricting `C` to the complement cannot increase its `L²` operator norm. -/
theorem norm_cmp116Eq214ComplementLocalizedC_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (localizedCoordinates : Finset ι) :
    ‖cmp116Eq214ComplementLocalizedC C localizedCoordinates‖ ≤ ‖C‖ := by
  calc
    ‖cmp116Eq214ComplementLocalizedC C localizedCoordinates‖ ≤
        ‖C‖ * ‖cmp116Eq223CoordinateProjection
          (Finset.univ \ localizedCoordinates)‖ := by
      exact norm_mul_le _ _
    _ ≤ ‖C‖ * 1 := by
      gcongr
      exact norm_cmp116Eq223ComplementProjection_le_one localizedCoordinates
    _ = ‖C‖ := mul_one _

/-- Uniform source rate after the printed complement-localized factor is
bounded by the same operator norm as `C`. -/
def cmp116Eq214GammaComplementSourceRate
    (CNorm deltaNorm rootNorm : ℝ) : ℝ :=
  (CNorm * deltaNorm * CNorm * rootNorm) ^ 2

/-- The literal complement-localized Gamma source obeys the uniform squared
operator-norm rate. -/
theorem norm_cmp116Eq214GammaComplementMatrix_sq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C delta root : Matrix ι ι ℝ) (localizedCoordinates : Finset ι)
    (CNorm deltaNorm rootNorm : ℝ)
    (hC : ‖C‖ ≤ CNorm)
    (hdelta : ‖delta‖ ≤ deltaNorm)
    (hroot : ‖root‖ ≤ rootNorm) :
    ‖cmp116Eq214GammaMatrix C delta
        (cmp116Eq214ComplementLocalizedC C localizedCoordinates) root‖ ^ 2 ≤
      cmp116Eq214GammaComplementSourceRate CNorm deltaNorm rootNorm := by
  unfold cmp116Eq214GammaComplementSourceRate
  exact norm_cmp116Eq214GammaMatrix_sq_le C delta
    (cmp116Eq214ComplementLocalizedC C localizedCoordinates) root
    CNorm deltaNorm CNorm rootNorm hC hdelta
    ((norm_cmp116Eq214ComplementLocalizedC_le C localizedCoordinates).trans hC)
    hroot

variable
  {nDelta nY d M N' Nc L lieDim : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
  [NeZero Nc] [NeZero L] [NeZero lieDim]
  {Ψ Φ E : Type*} [Norm E]

namespace CMP116Eq214FiniteGaussianData

set_option maxHeartbeats 800000 in
/-- Strongest equation-(2.14) reduction with the printed complement-localized
source built internally.  Neither an abstract source matrix nor an independent
localized-operator norm remains in the public interface. -/
theorem norm_term_le_cauchyRate_of_physicalGammaComplement_expCard
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
    (alpha5 outerBound CNorm deltaNorm : ℝ)
    (C delta : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hbeta : 2 *
      (cmp116Eq225SourceCoefficient (Dict.physicalRootMatrix root) alpha5 *
        cmp116Eq214GammaComplementSourceRate
          CNorm deltaNorm rootNormBound) < 1)
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
              (cmp116Eq214GammaMatrix (C sigma tau) (delta sigma tau)
                (cmp116Eq214ComplementLocalizedC (C sigma tau)
                  (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))
                (Dict.physicalRootMatrix root) *ᵥ
                  (cmp116Eq223CoordinateProjection
                    (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x)) b)
    (hC : ∀ sigma tau, ‖C sigma tau‖ ≤ CNorm)
    (hdelta : ∀ sigma tau, ‖delta sigma tau‖ ≤ deltaNorm) :
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
                      CNorm deltaNorm rootNormBound) *
                (Z0.card : ℝ)))) := by
  let S := Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0
  let r := fun sigma tau x =>
    cmp116Eq214GammaMatrix (C sigma tau) (delta sigma tau)
      (cmp116Eq214ComplementLocalizedC (C sigma tau) S)
      (Dict.physicalRootMatrix root) *ᵥ
        (cmp116Eq223CoordinateProjection S *ᵥ x)
  apply G.norm_term_le_cauchyRate_of_physicalGammaSource_expCard
    Dict hcert Y0 P Z0 psi phi alpha5 outerBound CNorm deltaNorm CNorm
      r C delta
      (fun sigma tau => cmp116Eq214ComplementLocalizedC (C sigma tau) S)
      hDelta hY halpha5 hsmall
      (by simpa [cmp116Eq214GammaComplementSourceRate] using hbeta)
      houter_nonneg houter
      (by simpa [S, r] using hdom)
      (by intro sigma tau x; rfl)
      hC hdelta
  intro sigma tau
  exact (norm_cmp116Eq214ComplementLocalizedC_le (C sigma tau) S).trans
    (hC sigma tau)

end CMP116Eq214FiniteGaussianData

end
end YangMills.RG
