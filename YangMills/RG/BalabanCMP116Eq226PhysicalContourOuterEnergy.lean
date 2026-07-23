/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4ReindexedContourDensity
import YangMills.RG.BalabanCMP116Eq225OuterInteractionEnergy
import YangMills.RG.BalabanCMP116Eq214CauchyPolydisc

/-!
# Cauchy boundary from the literal contour density with outer energy

The `R1` correction belongs to the outer Gaussian weight.  A uniform
pointwise bound in the outer field is therefore the wrong interface.  This
module applies the equation-(2.25) outer-energy theorem directly to a
`CMP116Eq214PhysicalContourDensity` and upgrades the fixed-contour estimate to
the nested Cauchy boundary required by equation (2.26).

The reference Gaussian is fixed by construction, so the resulting majorant
contains one literal `referenceRoot` and is uniform over both contour
families.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

/-- The physically correct nested Cauchy bound: the outer `R1` energy and the
completed-square `R3` source energy are integrated in one localized Gaussian
moment. -/
theorem nestedCauchyBoundaryBound_of_outerInteractionEnergy
    {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
    {Psi Phi : Site → Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (Y0 P : Finset Bond)
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (S : Finset (Bond × Fin lieDim))
    (alpha sourceRate sourceResidual outerBound outerRate : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate Bond lieDim →
        Bond × Fin lieDim → ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall :
      alpha * ‖C.referenceRoot‖ ^ 2 < 1)
    (hbeta :
      2 * (outerRate +
        cmp116Eq225SourceCoefficient C.referenceRoot alpha *
          sourceRate) < 1)
    (houter_nonneg : 0 ≤ outerBound)
    (houter : ∀ sigma tau x,
      ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.outerWeight
          sigma tau psi phi x‖ ≤
        outerBound *
          Real.exp (outerRate * ∑ i ∈ S, x i ^ 2))
    (hdom : ∀ sigma tau x,
      ∀ᵐ b ∂matrixGaussianPi C.referenceRoot,
        ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.innerIntegrand
            Y0 P sigma tau psi phi x b‖ ≤
          cmp116Eq223RealGaussian
            (-(alpha • cmp116Eq223CoordinateProjection S))
            (r sigma tau x) b)
    (hsource : ∀ sigma tau x,
      (r sigma tau x) ⬝ᵥ (r sigma tau x) ≤
        sourceRate * (∑ i ∈ S, x i ^ 2) + sourceResidual) :
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      C.deltaRadius C.yRadius
      (fun sigma tau =>
        C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.analyticIntegrand
          Y0 P sigma tau psi phi)
      (outerBound *
        (cmp116Eq225LocalizedSourceEnergyPrefactor S
          C.referenceRoot alpha sourceResidual *
        (Real.sqrt
          ((1 - 2 * (outerRate +
            cmp116Eq225SourceCoefficient C.referenceRoot alpha *
              sourceRate)) ^ S.card))⁻¹)) := by
  apply cmp116Eq214NestedCauchyBoundaryBound_of_forall_norm_le
  intro sigma tau
  let G := C.toLocalFiniteGaussianData.toFiniteGaussianData
  have hfixed :
      G.covarianceRoot sigma tau = C.referenceRoot := rfl
  have hbound :=
    G.norm_analyticIntegrand_le_of_outerInteractionEnergy
      Y0 P sigma tau psi phi S alpha sourceRate sourceResidual
      outerBound outerRate (r sigma tau)
      halpha
      (by simpa [hfixed] using hsmall)
      (by simpa [hfixed] using hbeta)
      houter_nonneg
      (houter sigma tau)
      (by simpa [G, hfixed] using hdom sigma tau)
      (hsource sigma tau)
  simpa [G, hfixed] using hbound

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
