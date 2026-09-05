/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedTransferPowers
import YangMills.RG.BalabanCMP116RestrictedVisitedTransferResolvent
import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedCovariance

/-!
# Source `Pi^4` restricted contours as finite transfer powers

The generic visited-state transfer construction is specialized here to the
literal source `Pi^4` charts, their physical successor family, and the
canonical complex matrices of the patched-parametrix head and continuation
operators.

Every theorem in this file concerns one finite walk-length layer.  No
interchange or factorization of infinite sums is used.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The literal weakening carrier attached to one source quotient chart and
one distinguished `sigma_0` anchor. -/
def cmp116SourcePi4RestrictedDomainActive
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp99SourceDomainLargeBlocks chart.1.domain ∩
    cmp116SourceSigmaZero anchor

/-- Canonical complex matrix of one literal source patched-parametrix head. -/
noncomputable def cmp116SourcePi4RestrictedHeadMatrix
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (head : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix
    (cmp99PhysicalPatchHead
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK head)

/-- Canonical complex matrix of one literal source continuation factor. -/
noncomputable def cmp116SourcePi4RestrictedContinuationMatrix
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (_label : Unit)
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix
    (cmp99PhysicalPatchContinuation
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK chart)

/-- The canonical complex matrix transports the ordered product of any
finite physical endomorphism list without reversing its order. -/
theorem cmp116PhysicalEndomorphismComplexMatrix_list_prod
    {d N Nc : ℕ} [NeZero N] [NeZero (Nc ^ 2 - 1)] :
    ∀ factors : List
        (PhysicalGaugeOneCochain d N Nc →L[ℝ]
          PhysicalGaugeOneCochain d N Nc),
      cmp116PhysicalEndomorphismComplexMatrix factors.prod =
        (factors.map cmp116PhysicalEndomorphismComplexMatrix).prod := by
  intro factors
  induction factors with
  | nil =>
      change
        cmp116PhysicalEndomorphismComplexMatrix
            (ContinuousLinearMap.id ℝ
              (PhysicalGaugeOneCochain d N Nc)) = 1
      exact cmp116PhysicalEndomorphismComplexMatrix_id
  | cons factor rest ih =>
      simp only [List.prod_cons, List.map_cons]
      rw [ContinuousLinearMap.mul_def,
        cmp116PhysicalEndomorphismComplexMatrix_comp, ih]

/-- Transporting one source walk term to canonical complex matrices commutes
exactly with its noncommutative ordered product. -/
theorem cmp116PhysicalEndomorphismComplexMatrix_walk_term
    {Label Domain : Type*}
    {d N Nc : ℕ} [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (R0 : Domain →
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (R : Label → Domain →
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (walk : CMP99GeneralizedWalk Label Domain) :
    cmp116PhysicalEndomorphismComplexMatrix (walk.term R0 R) =
      walk.term
        (fun head => cmp116PhysicalEndomorphismComplexMatrix (R0 head))
        (fun label domain =>
          cmp116PhysicalEndomorphismComplexMatrix (R label domain)) := by
  unfold CMP99GeneralizedWalk.term
  rw [cmp116PhysicalEndomorphismComplexMatrix_list_prod]
  simp only [List.map_cons, List.prod_cons]
  congr 1
  apply congrArg List.prod
  rw [List.map_map]
  exact List.map_congr_left (fun step _ => rfl)

/-- One literal physical source covariance layer on a restricted contour is
the corresponding generic finite generated-walk layer in canonical complex
coordinates. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_eq_generated
    {nContour M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nContour ≃ ↥carrier)
    (z : Fin nContour → ℂ)
    (n : ℕ) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z) n =
      cmp116RestrictedGeneratedWalkLayer
        carrier e z
        (cmp116SourcePi4RestrictedDomainActive anchor)
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
        (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
        n := by
  classical
  funext row col
  unfold cmp116SourcePi4FullComplexWeakenedCovarianceLayer
  unfold cmp116RestrictedGeneratedWalkLayer
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Fintype.sum_congr
  intro head
  conv_rhs => rw [← Finset.sum_attach]
  rw [Finset.attach_eq_univ]
  apply Fintype.sum_congr
  intro tail
  let anchored :
      CMP99AnchoredWalk
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        head :=
    ⟨n, tail⟩
  let walk : CMP99GeneralizedWalk Unit
      ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) :=
    ⟨head, tail.1⟩
  change
    cmp116ComplexWeakeningMonomial
        (cmp116SourcePi4QuotientWalkActive
          (M := M) anchor head anchored)
        (cmp116SourceRestrictedShiftedCoupling carrier e z) *
      cmp116ComplexPhysicalOperatorCoefficient
        (anchored.term
          (cmp99PhysicalPatchHead
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            K cmp99SourcePi4ChartEnlarged
            (cmp99SourcePi4ChartCore (M := M))
            hc hmass hK)
          (fun _ =>
            cmp99PhysicalPatchContinuation
              (cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q))
              K cmp99SourcePi4ChartEnlarged
              (cmp99SourcePi4ChartCore (M := M))
              hc hmass hK))
        col.1 row.1 col.2 row.2 =
      cmp116ComplexWeakeningMonomial
          (walk.active
            (cmp116SourcePi4RestrictedDomainActive anchor))
          (cmp116SourceRestrictedShiftedCoupling carrier e z) *
        (walk.term
          (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK))
          row col
  rw [← cmp116PhysicalEndomorphismComplexMatrix_apply]
  change
    cmp116ComplexWeakeningMonomial
        (walk.active (cmp116SourcePi4RestrictedDomainActive anchor))
        (cmp116SourceRestrictedShiftedCoupling carrier e z) *
      cmp116PhysicalEndomorphismComplexMatrix
        (walk.term
          (fun chart =>
            cmp99PhysicalPatchHead
              (cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q))
              K cmp99SourcePi4ChartEnlarged
              (cmp99SourcePi4ChartCore (M := M))
              hc hmass hK chart)
          (fun (_label : Unit) chart =>
            cmp99PhysicalPatchContinuation
              (cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q))
              K cmp99SourcePi4ChartEnlarged
              (cmp99SourcePi4ChartCore (M := M))
              hc hmass hK chart))
        row col =
      cmp116ComplexWeakeningMonomial
          (walk.active
            (cmp116SourcePi4RestrictedDomainActive anchor))
          (cmp116SourceRestrictedShiftedCoupling carrier e z) *
        (walk.term
          (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK))
          row col
  rw [cmp116PhysicalEndomorphismComplexMatrix_walk_term]
  rfl

/-- The literal physical restricted-contour layer is therefore exactly a
head-weighted row sum of the matching finite visited-state transfer power. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_eq_transferPower
    {nContour M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nContour ≃ ↥carrier)
    (z : Fin nContour → ℂ)
    (n : ℕ) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z) n =
      cmp116RestrictedVisitedTransferPowerLayer
        carrier
        (cmp116SourcePi4RestrictedDomainActive anchor)
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
        (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
        (cmp116SourceRestrictedShiftedCoupling carrier e z) n := by
  rw [
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_eq_generated,
    cmp116RestrictedGeneratedWalkLayer_eq_transferPowerLayer]

/-- The complete literal source covariance on a restricted contour is the
finite head readout of the visited-state transfer resolvent.  The only
analytic input is summability of the physical transfer powers; no double
series is reordered. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_restricted_eq_headReadout_resolvent
    {nContour M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nContour ≃ ↥carrier)
    (z : Fin nContour → ℂ)
    (hsum :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (cmp116SourceRestrictedShiftedCoupling carrier e z) ^ n) :
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z) =
      cmp116RestrictedVisitedTransferHeadReadout
        carrier
        (cmp116SourcePi4RestrictedDomainActive anchor)
        (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
        (cmp116SourceRestrictedShiftedCoupling carrier e z)
        (cmp116RestrictedVisitedTransferResolvent
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (cmp116SourceRestrictedShiftedCoupling carrier e z)) := by
  have hpowerSum :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferPowerLayer
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (cmp116SourceRestrictedShiftedCoupling carrier e z) n := by
    let L := cmp116RestrictedVisitedTransferHeadReadoutCLM
      (Label := Unit)
      carrier
      (cmp116SourcePi4RestrictedDomainActive anchor)
      (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
      (cmp116SourceRestrictedShiftedCoupling carrier e z)
    have himage := hsum.map L L.continuous
    exact himage.congr fun n =>
      (cmp116RestrictedVisitedTransferPowerLayer_eq_headReadout
        carrier
        (cmp116SourcePi4RestrictedDomainActive anchor)
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
        (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
        (cmp116SourceRestrictedShiftedCoupling carrier e z) n).symm
  have hsourceSum :
      Summable fun n : ℕ =>
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z) n :=
    hpowerSum.congr fun n =>
      (cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_eq_transferPower
        (R := R) anchor K hc hmass hK carrier e z n).symm
  calc
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z) =
      ∑' n : ℕ,
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z) n := by
      funext row col
      rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix]
      symm
      calc
        (∑' n : ℕ,
            cmp116SourcePi4FullComplexWeakenedCovarianceLayer
              (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling carrier e z) n) row col =
            (∑' n : ℕ,
              cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK
                (cmp116SourceRestrictedShiftedCoupling carrier e z) n row) col := by
          exact congrFun (tsum_apply (x := row) hsourceSum) col
        _ = ∑' n : ℕ,
            cmp116SourcePi4FullComplexWeakenedCovarianceLayer
              (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling carrier e z) n row col :=
          tsum_apply ((Pi.summable.mp hsourceSum) row)
    _ = ∑' n : ℕ,
        cmp116RestrictedVisitedTransferPowerLayer
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (cmp116SourceRestrictedShiftedCoupling carrier e z) n := by
      apply tsum_congr
      intro n
      exact
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_eq_transferPower
          (R := R) anchor K hc hmass hK carrier e z n
    _ = _ :=
      tsum_cmp116RestrictedVisitedTransferPowerLayer_eq_headReadout_resolvent
        carrier
        (cmp116SourcePi4RestrictedDomainActive anchor)
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
        (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
        (cmp116SourceRestrictedShiftedCoupling carrier e z)
        hsum

end

end YangMills.RG
