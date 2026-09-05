/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCommonDomainTower
import YangMills.RG.BalabanCMP99SourceMassWeights
import YangMills.RG.BalabanCMP99SourceCoarseCovariance

/-!
# Feed one common CMP99 average tower into the stratified mass

The stratified mass must not receive unrelated operators at its different
scales.  This file takes one common-domain tower and transports each retained
prefix to the literal scale-field type of `Lambda_j`.  The only dictionary
data left visible are level-by-level linear isometries, so this transport
cannot hide a condition-number loss.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u v w

/-- Exact isometric identification of the retained tower levels with the
field types on the source lattices of the global strata. -/
structure CMP99SourceCommonTowerScaleIdentification
    {FineSite : Type u} [DecidableEq FineSite]
    {n : ℕ} {ScaleSite : Fin n → Type v}
    [∀ r, DecidableEq (ScaleSite r)] [∀ r, Fintype (ScaleSite r)]
    {Start : CMP99SourceWeightedTowerHilbertSpace}
    (T : CMP99SourceCommonDomainTower Start n)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (g : Type w) [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] where
  levelEquiv : ∀ r : Fin n,
    (T.levelSpace r.castSucc).carrier ≃ₗᵢ[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r

namespace CMP99SourceCommonTowerScaleIdentification

variable {FineSite : Type u} [DecidableEq FineSite]
variable {n : ℕ} {ScaleSite : Fin n → Type v}
variable [∀ r, DecidableEq (ScaleSite r)] [∀ r, Fintype (ScaleSite r)]
variable {Start : CMP99SourceWeightedTowerHilbertSpace}
variable {T : CMP99SourceCommonDomainTower Start n}
variable {S : CMP99SourceScaledStratification FineSite n ScaleSite}
variable {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]

/-- The `j`-th source average, derived from the `j`-th prefix of one tower. -/
def Qprime
    (I : CMP99SourceCommonTowerScaleIdentification T S g) (r : Fin n) :
    Start.carrier →L[ℝ]
      CMP99SourceScaledStratification.ScaleField
        (ScaleSite := ScaleSite) g r :=
  (I.levelEquiv r).toContinuousLinearMap.comp (T.Qprime r.castSucc)

/-- The source precision built from one retained common-domain tower. -/
def gaugePrecision
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) (a L eta : ℝ) : Start.carrier →L[ℝ] Start.carrier :=
  cmp99SourceScaledGaugePrecision S covariantLaplacian I.Qprime d a L eta

/-- Exact (3.23)--(3.24) quadratic form with all `Q'_j` derived from the
same tower. -/
theorem spacingPairing_gaugePrecision
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) (a L eta : ℝ) (heta : eta ≠ 0) (phi : Start.carrier) :
    cmp99SourceSpacingPairing d eta phi
        (I.gaugePrecision covariantLaplacian d a L eta phi) =
      cmp99SourceSpacingPairing d eta phi (covariantLaplacian phi) +
        ∑ r : Fin n,
          cmp99SourceMassParameter a L r.val *
            (L ^ r.val * eta) ^ (d - 2) *
              ∑ y ∈ S.strata r, ‖I.Qprime r phi y‖ ^ 2 := by
  exact spacingPairing_cmp99SourceScaledGaugePrecision S covariantLaplacian
    I.Qprime d a L eta heta phi

/-- The full common-tower precision retains the ambient coercivity constant.
All source weights are generated from the positive printed parameters. -/
theorem gaugePrecision_isCoercive
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) {a L eta c : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta)
    (hDelta : IsCoerciveCLM covariantLaplacian c) :
    IsCoerciveCLM (I.gaugePrecision covariantLaplacian d a L eta) c := by
  exact isCoerciveCLM_cmp99SourceStratifiedGaugePrecision
    (fun r => CMP99SourceScaledStratification.ScaleField
      (ScaleSite := ScaleSite) g r)
    (fun r => S.StratumField g r)
    covariantLaplacian I.Qprime (fun r => S.restrictStratumCLM r)
    (fun r => le_of_lt
      (cmp99SourceCountingStratumWeight_pos d ha hL heta r)) hDelta

/-- The full common-tower precision is symmetric when the covariant
Laplacian is symmetric. -/
theorem gaugePrecision_isSymmetric
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) (a L eta : ℝ) (hDelta : covariantLaplacian.IsSymmetric) :
    (I.gaugePrecision covariantLaplacian d a L eta).IsSymmetric := by
  exact cmp99SourceStratifiedGaugePrecision_isSymmetric
    (fun r => CMP99SourceScaledStratification.ScaleField
      (ScaleSite := ScaleSite) g r)
    (fun r => S.StratumField g r)
    covariantLaplacian I.Qprime (fun r => S.restrictStratumCLM r)
    (cmp99SourceCountingStratumWeight d a L eta) hDelta

/-- Green operator for the complete stratified precision (3.23)--(3.24),
constructed from coercivity rather than supplied as an inverse. -/
def green
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) {a L eta c : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c) :
    Start.carrier →L[ℝ] Start.carrier :=
  covarianceOfIsCoerciveCLM
    (I.gaugePrecision covariantLaplacian d a L eta) hc
    (I.gaugePrecision_isCoercive covariantLaplacian d ha hL heta hDelta)

/-- Exact right inverse equation for the complete source precision. -/
theorem gaugePrecision_comp_green
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) {a L eta c : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c) :
    (I.gaugePrecision covariantLaplacian d a L eta).comp
        (I.green covariantLaplacian d ha hL heta hc hDelta) =
      ContinuousLinearMap.id ℝ Start.carrier := by
  exact precision_comp_covarianceOfIsCoerciveCLM _ hc _

/-- Exact left inverse equation for the complete source precision. -/
theorem green_comp_gaugePrecision
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) {a L eta c : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c) :
    (I.green covariantLaplacian d ha hL heta hc hDelta).comp
        (I.gaugePrecision covariantLaplacian d a L eta) =
      ContinuousLinearMap.id ℝ Start.carrier := by
  exact covarianceOfIsCoerciveCLM_comp_precision _ hc _

/-- Symmetry of the generated full source Green. -/
theorem green_isSymmetric
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) {a L eta c : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c)
    (hDeltaSymm : covariantLaplacian.IsSymmetric) :
    (I.green covariantLaplacian d ha hL heta hc hDelta).IsSymmetric := by
  exact covarianceOfIsCoerciveCLM_isSymmetric _ hc
    (I.gaugePrecision_isCoercive covariantLaplacian d ha hL heta hDelta)
    (I.gaugePrecision_isSymmetric covariantLaplacian d a L eta hDeltaSymm)

/-- The actual average seen by the `r`-th source stratum. -/
def stratumAverage
    (I : CMP99SourceCommonTowerScaleIdentification T S g) (r : Fin n) :
    Start.carrier →L[ℝ] S.StratumField g r :=
  (S.restrictStratumCLM r).comp (I.Qprime r)

/-- Corrected coarse covariance on `Lambda_r`, formed with the Green of the
complete stratified precision rather than a one-scale surrogate. -/
def stratumCoarseCovariance
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) {a L eta c : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c) (r : Fin n) :
    S.StratumField g r →L[ℝ] S.StratumField g r :=
  cmp99SourceCoarseCovarianceMiddle (I.stratumAverage r)
    (I.green covariantLaplacian d ha hL heta hc hDelta)

/-- Exact square identity for the corrected stratum covariance. -/
theorem inner_stratumCoarseCovariance
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) {a L eta c : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c)
    (hDeltaSymm : covariantLaplacian.IsSymmetric)
    (r : Fin n) (xi : S.StratumField g r) :
    inner ℝ xi
        (I.stratumCoarseCovariance covariantLaplacian d
          ha hL heta hc hDelta r xi) =
      ‖I.green covariantLaplacian d ha hL heta hc hDelta
        ((I.stratumAverage r).adjoint xi)‖ ^ 2 := by
  exact inner_cmp99SourceCoarseCovarianceMiddle _ _
    (I.green_isSymmetric covariantLaplacian d
      ha hL heta hc hDelta hDeltaSymm) xi

/-- Positivity of every corrected stratum covariance. -/
theorem inner_stratumCoarseCovariance_nonneg
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (covariantLaplacian : Start.carrier →L[ℝ] Start.carrier)
    (d : ℕ) {a L eta c : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c)
    (hDeltaSymm : covariantLaplacian.IsSymmetric)
    (r : Fin n) (xi : S.StratumField g r) :
    0 ≤ inner ℝ xi
      (I.stratumCoarseCovariance covariantLaplacian d
        ha hL heta hc hDelta r xi) := by
  rw [I.inner_stratumCoarseCovariance covariantLaplacian d
    ha hL heta hc hDelta hDeltaSymm r xi]
  exact sq_nonneg _

/-- No independently chosen scale operator survives: unfolding the adapter
shows the retained prefix followed by the exact level equivalence. -/
@[simp] theorem Qprime_apply
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (r : Fin n) (phi : Start.carrier) :
    I.Qprime r phi = I.levelEquiv r (T.Qprime r.castSucc phi) := rfl

end CMP99SourceCommonTowerScaleIdentification

end

end YangMills.RG
