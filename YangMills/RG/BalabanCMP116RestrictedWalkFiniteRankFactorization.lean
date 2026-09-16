/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedWalkContourActiveCore
import YangMills.RG.BalabanCMP116Eq214FiniteCarrierFactorization

/-!
# Finite-rank factorization of one contour-active physical walk

The first-hit physical factorization is transported to the exact complex
bond--Lie matrix convention used by the CMP116 determinant.  Each active walk
then factors through the scalar coordinates over one common contour-active
physical core.
-/

namespace YangMills.RG

noncomputable section

universe u w

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Matrix form of the exact first-hit factorization of one physical patched
walk through the common contour-active core. -/
theorem cmp116PhysicalPatchWalk_matrix_eq_firstHit_finiteCarrierFactors
    {ι : Type u} [DecidableEq ι]
    {Cube : Type w} [DecidableEq Cube]
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (domainActive : ↥charts → Finset Cube)
    (carrier : Finset Cube)
    (walk : CMP99GeneralizedWalk Unit ↥charts)
    (cube : Cube) (hactive : cube ∈ walk.active domainActive)
    (hcarrier : cube ∈ carrier) :
    let R0 :=
      cmp99PhysicalPatchHead charts K enlarged core hc hmass hK
    let R := fun (_ : Unit) => cmp99PhysicalPatchContinuation
      charts K enlarged core hc hmass hK
    let index := walk.firstActiveDomainIndex domainActive cube hactive
    let leftPart := ((walk.factors R0 R).take index).prod
    let pivot := walk.firstActiveFactor
      domainActive R0 R cube hactive
    let rightPart := ((walk.factors R0 R).drop (index + 1)).prod
    let activeCore := CMP99GeneralizedWalk.contourActiveCore
      (fun i : ↥charts => core i) domainActive carrier
    let activeCoordinates :=
      cmp116PhysicalCoreCoordinates (Nc := Nc) activeCore
    cmp116PhysicalEndomorphismComplexMatrix (walk.term R0 R) =
      (cmp116PhysicalEndomorphismComplexMatrix (leftPart.comp pivot) *
        cmp116FinsetColumnInclusion (α := ℂ) activeCoordinates) *
      (cmp116FinsetCoordinateRestriction (α := ℂ) activeCoordinates *
        cmp116PhysicalEndomorphismComplexMatrix rightPart) := by
  dsimp only
  let R0 :=
    cmp99PhysicalPatchHead charts K enlarged core hc hmass hK
  let R := fun (_ : Unit) => cmp99PhysicalPatchContinuation
    charts K enlarged core hc hmass hK
  let index := walk.firstActiveDomainIndex domainActive cube hactive
  let leftPart := ((walk.factors R0 R).take index).prod
  let pivot := walk.firstActiveFactor
    domainActive R0 R cube hactive
  let rightPart := ((walk.factors R0 R).drop (index + 1)).prod
  let activeCore := CMP99GeneralizedWalk.contourActiveCore
    (fun i : ↥charts => core i) domainActive carrier
  let activeCoordinates :=
    cmp116PhysicalCoreCoordinates (Nc := Nc) activeCore
  have hterm :=
    cmp99PhysicalPatchWalk_term_eq_firstHit_contourActiveCore
      charts K enlarged core hc hmass hK domainActive carrier walk
      cube hactive hcarrier
  have hterm' :
      walk.term R0 R =
        (leftPart.comp pivot).comp
          ((physicalBondProjection activeCore).comp rightPart) := by
    simpa only [R0, R, index, leftPart, pivot, rightPart, activeCore,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hterm
  calc
    cmp116PhysicalEndomorphismComplexMatrix (walk.term R0 R) =
        cmp116PhysicalEndomorphismComplexMatrix
          ((leftPart.comp pivot).comp
            ((physicalBondProjection activeCore).comp rightPart)) := by
      rw [hterm']
    _ = cmp116PhysicalEndomorphismComplexMatrix (leftPart.comp pivot) *
        (cmp116PhysicalEndomorphismComplexMatrix
            (physicalBondProjection activeCore) *
          cmp116PhysicalEndomorphismComplexMatrix rightPart) := by
      simp only [cmp116PhysicalEndomorphismComplexMatrix_comp,
        Matrix.mul_assoc]
    _ = cmp116PhysicalEndomorphismComplexMatrix (leftPart.comp pivot) *
        cmp116FinsetCoordinateProjection (α := ℂ) activeCoordinates *
          cmp116PhysicalEndomorphismComplexMatrix rightPart := by
      rw [cmp116PhysicalEndomorphismComplexMatrix_projection]
      simp only [activeCoordinates, Matrix.mul_assoc]
    _ = (cmp116PhysicalEndomorphismComplexMatrix (leftPart.comp pivot) *
          cmp116FinsetColumnInclusion (α := ℂ) activeCoordinates) *
        (cmp116FinsetCoordinateRestriction (α := ℂ) activeCoordinates *
          cmp116PhysicalEndomorphismComplexMatrix rightPart) := by
      exact mul_cmp116FinsetCoordinateProjection_mul_eq_factorized
        activeCoordinates
        (cmp116PhysicalEndomorphismComplexMatrix (leftPart.comp pivot))
        (cmp116PhysicalEndomorphismComplexMatrix rightPart)

end

end YangMills.RG
