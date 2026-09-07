/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LocalAnalyticData
import YangMills.RG.BalabanCMP116Eq214FiniteGaussianData

/-!
# CMP116 equation (2.14): one object for locality and Gaussian estimates

The quantitative reduction consumes `CMP116Eq214FiniteGaussianData`, whereas
the source-faithful activity construction consumes analytic weights defined on
restricted fields.  This module supplies their common refinement.

Both forgetful maps are literal.  In particular, the term estimated by the
finite-Gaussian theorems is definitionally the global evaluation of the local
term.  A physical producer therefore cannot use one integrand to prove the
bound and another to claim locality.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Finite Gaussian equation-(2.14) data with external field locality enforced
by the types of all three physical weights. -/
structure CMP116Eq214LocalFiniteGaussianData
    (nDelta nY : ℕ) (Bond Site : Type*) (Psi Phi : Site → Type*)
    (E : Type*) [Fintype Bond] [Norm E] (lieDim : ℕ) where
  spectatorSupport : Finset Site
  fluctuationSupport : Finset Site
  deltaRadius : Fin nDelta → ℝ
  yRadius : Fin nY → ℝ
  covarianceRoot :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ
  outerWeight :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
      CMP116Eq214GaussianCoordinate Bond lieDim → ℂ
  innerWeight :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
      CMP116Eq214GaussianCoordinate Bond lieDim →
      CMP116Eq214GaussianCoordinate Bond lieDim → ℂ
  bondField : CMP116Eq214GaussianCoordinate Bond lieDim → Bond → E
  threshold : ℝ
  interactionExponent :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
      CMP116Eq214GaussianCoordinate Bond lieDim → ℂ

namespace CMP116Eq214LocalFiniteGaussianData

variable {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
  {Psi Phi : Site → Type*} [Fintype Bond] [Norm E]

/-- Forget only the restricted-field typing, retaining the concrete Gaussian
laws used by the quantitative campaign. -/
def toFiniteGaussianData
    (G : CMP116Eq214LocalFiniteGaussianData nDelta nY
      Bond Site Psi Phi E lieDim) :
    CMP116Eq214FiniteGaussianData nDelta nY Bond
      (∀ s, Psi s) (∀ s, Phi s) E lieDim where
  deltaRadius := G.deltaRadius
  yRadius := G.yRadius
  covarianceRoot := G.covarianceRoot
  outerWeight := fun sigma tau psi phi x =>
    G.outerWeight sigma tau
      (restrictGlobal G.spectatorSupport psi)
      (restrictGlobal G.fluctuationSupport phi) x
  innerWeight := fun sigma tau psi phi x b =>
    G.innerWeight sigma tau
      (restrictGlobal G.spectatorSupport psi)
      (restrictGlobal G.fluctuationSupport phi) x b
  bondField := G.bondField
  threshold := G.threshold
  interactionExponent := fun sigma tau psi phi b =>
    G.interactionExponent sigma tau
      (restrictGlobal G.spectatorSupport psi)
      (restrictGlobal G.fluctuationSupport phi) b

/-- Forget only the concrete finite-Gaussian specialization, retaining the
restricted-field interface. -/
def toLocalAnalyticData
    (G : CMP116Eq214LocalFiniteGaussianData nDelta nY
      Bond Site Psi Phi E lieDim) :
    CMP116Eq214LocalAnalyticData nDelta nY Bond
      (CMP116Eq214GaussianCoordinate Bond lieDim)
      (CMP116Eq214GaussianCoordinate Bond lieDim) Site Psi Phi E where
  spectatorSupport := G.spectatorSupport
  fluctuationSupport := G.fluctuationSupport
  deltaRadius := G.deltaRadius
  yRadius := G.yRadius
  mu0 := balabanCMP116Dmu0Flat Bond lieDim
  conditionedMeasure := fun sigma tau => matrixGaussianPi (G.covarianceRoot sigma tau)
  outerWeight := G.outerWeight
  innerWeight := G.innerWeight
  bondField := G.bondField
  threshold := G.threshold
  interactionExponent := G.interactionExponent

/-- The two forgetful paths produce exactly the same global analytic data. -/
theorem toLocalAnalyticData_toAnalyticData_eq
    (G : CMP116Eq214LocalFiniteGaussianData nDelta nY
      Bond Site Psi Phi E lieDim) :
    G.toLocalAnalyticData.toAnalyticData =
      G.toFiniteGaussianData.toAnalyticData := by
  rfl

/-- Consequently the finite-Gaussian term being estimated is exactly the term
obtained by forgetting the restricted physical weights. -/
theorem toLocalAnalyticData_term_eq_toFiniteGaussianData_term
    (G : CMP116Eq214LocalFiniteGaussianData nDelta nY
      Bond Site Psi Phi E lieDim)
    (Y0 P : Finset Bond) (psi : ∀ s, Psi s) (phi : ∀ s, Phi s) :
    G.toLocalAnalyticData.toAnalyticData.term Y0 P psi phi =
      G.toFiniteGaussianData.toAnalyticData.term Y0 P psi phi := by
  rfl

/-- The physical local term and the quantitatively estimated finite-Gaussian
term are the same object after evaluation on global fields. -/
@[simp] theorem globalEval_localTerm_eq_toFiniteGaussianData_term
    (G : CMP116Eq214LocalFiniteGaussianData nDelta nY
      Bond Site Psi Phi E lieDim)
    (Y0 P : Finset Bond) (psi : ∀ s, Psi s) (phi : ∀ s, Phi s) :
    (G.toLocalAnalyticData.localTerm Y0 P).globalEval psi phi =
      G.toFiniteGaussianData.toAnalyticData.term Y0 P psi phi := by
  rfl

end CMP116Eq214LocalFiniteGaussianData

end


end YangMills.RG
