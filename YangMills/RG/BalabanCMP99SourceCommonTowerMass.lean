/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCommonDomainTower
import YangMills.RG.BalabanCMP99SourceMassWeights

/-!
# Feed one common CMP99 average tower into the stratified mass

The stratified mass must not receive unrelated operators at its different
scales.  This file takes one common-domain tower and transports each retained
prefix to the literal scale-field type of `Lambda_j`.  The only dictionary
data left visible are the level-by-level continuous linear equivalences.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u v w

/-- Exact identification of the retained tower levels with the field types
on the source lattices of the global strata. -/
structure CMP99SourceCommonTowerScaleIdentification
    {FineSite : Type u} [DecidableEq FineSite]
    {n : ℕ} {ScaleSite : Fin n → Type v}
    [∀ r, DecidableEq (ScaleSite r)]
    {Start : CMP99SourceWeightedTowerHilbertSpace}
    (T : CMP99SourceCommonDomainTower Start n)
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (g : Type w) [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] where
  levelEquiv : ∀ r : Fin n,
    (T.levelSpace r.castSucc).carrier ≃L[ℝ]
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

/-- No independently chosen scale operator survives: unfolding the adapter
shows the retained prefix followed by the exact level equivalence. -/
@[simp] theorem Qprime_apply
    (I : CMP99SourceCommonTowerScaleIdentification T S g)
    (r : Fin n) (phi : Start.carrier) :
    I.Qprime r phi = I.levelEquiv r (T.Qprime r.castSucc phi) := rfl

end CMP99SourceCommonTowerScaleIdentification

end

end YangMills.RG
