/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceCoordinatePivotWeightedTrace
import YangMills.RG.BalabanCMP116SourceCoordinatePivotGeneratedWalkCount
import YangMills.RG.BalabanCMP116SourceGeneratedWalkSumReindex
import YangMills.RG.BalabanCMP116RestrictedPivotWeightBound
import YangMills.RG.BalabanCMP116SourceRestrictedCoordinatePivotMatrixLayer

/-!
# Uniform active-walk trace bound for one source coordinate

The weighted first-hit trace estimate is converted to a walk-independent
bound.  The reverse and forward continuation powers recombine into the
single exact power `rho ^ layer`; the ordered contour weight is bounded by
one radius and the physical weakening cap.  The uniform first-hit count then
sums the complete marked layer without an ambient chart factor.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- One generated-walk contribution to the ordered physical
coordinate-pivot trace. -/
noncomputable def cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm
    {q M Q Nc R layer : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃ ↥carrier) (z : Fin q → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (walk : CMP99GeneratedWalkAtLength
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R) layer)
    (i : Fin q)
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) : ℂ :=
  let rawPair : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) :=
    (walk.1, walk.2.1)
  cmp116RestrictedOrderedPivotWeight
      (cmp116SourcePi4ForwardWalkActive anchor rawPair)
      carrier e z i *
    Matrix.trace
      ((P *
        cmp116PhysicalEndomorphismComplexMatrix
          (cmp116SourcePi4ForwardWalkOperator K hc hmass hK rawPair)) *
        D ^ m)

set_option maxHeartbeats 3000000 in

/-- Every generated walk has the same volume-uniform marked trace bound.
The bound is valid also when the ordered pivot weight vanishes. -/
theorem norm_cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm_le
    {q M Q Nc R layer : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃ ↥carrier) (z : Fin q → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hrange : R + 1 ≤ 4 * M)
    (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (walk : CMP99GeneratedWalkAtLength
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R) layer)
    (i : Fin q)
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) :
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    ‖cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm
        anchor carrier e z K hc hmass hK walk i P D m‖ ≤
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        ((radius * Rweak ^ (10000 * (layer + 1))) *
          (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
            (‖P‖ * (Ahead * geometricRow)))) := by
  dsimp only
  let rawPair : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) :=
    (walk.1, walk.2.1)
  let rawWalk : CMP99GeneralizedWalk Unit
      ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) :=
    ⟨rawPair.1, rawPair.2⟩
  let active := cmp116SourcePi4ForwardWalkActive anchor rawPair
  let w := cmp116RestrictedOrderedPivotWeight active carrier e z i
  let geometricRow :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  have hAhead : 0 ≤ Ahead := (Cert.head walk.1).1
  have hrho : 0 ≤ rho := (Cert.continuation walk.1).1
  have hgeometricRow : 0 ≤ geometricRow := by
    dsimp [geometricRow]
    exact mul_nonneg (Nat.cast_nonneg _)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  have hcommon :
      0 ≤ (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
        (‖P‖ * (Ahead * geometricRow))) := by
    positivity
  change
    ‖cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm
        anchor carrier e z K hc hmass hK walk i P D m‖ ≤
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        ((radius * Rweak ^ (10000 * (layer + 1))) *
          (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
            (‖P‖ * (Ahead * geometricRow))))
  by_cases hw : w = 0
  · have hterm :
        cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm
          anchor carrier e z K hc hmass hK walk i P D m = 0 := by
        simp [cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm,
          rawPair, active, w, hw]
    rw [hterm, norm_zero]
    have hweightNonneg :
        0 ≤ radius * Rweak ^ (10000 * (layer + 1)) :=
      mul_nonneg hradius
        (pow_nonneg (zero_le_one.trans hRweak) _)
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hweightNonneg hcommon)
  · have hbase :=
      norm_cmp116SourcePi4ForwardWalk_coordinatePivot_weight_mul_trace_le_weighted
        anchor carrier e z K hc hmass hK Cert hrate hgeom
        rawPair i hw P D m
    dsimp only at hbase
    let domainActive :=
      fun chart :
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)) =>
        cmp99SourceDomainLargeBlocks chart.1.domain ∩
          cmp116SourceSigmaZero anchor
    have hactive : (e i : FinBox 4 (2 * Q)) ∈
        rawWalk.active domainActive :=
      mem_active_of_cmp116RestrictedOrderedPivotWeight_ne_zero
        active carrier e z i hw
    let index :=
      rawWalk.firstActiveDomainIndex domainActive (e i) hactive
    have hlen : rawWalk.tail.length = layer := by
      exact length_eq_of_mem_cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        walk.2.2
    have hpow :
        rho ^ (rawWalk.tail.length - index.val) * rho ^ index.val =
          rho ^ layer := by
      rw [rawWalk.rho_pow_suffix_mul_prefix_eq rho index, hlen]
    have hsplit :
        (((rho ^ (rawWalk.tail.length - index.val) * geometricRow) *
              ‖D ^ m‖) *
          (‖P‖ * ((Ahead * rho ^ index.val) * geometricRow))) =
        (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
          (‖P‖ * (Ahead * geometricRow))) := by
      calc
        _ = (rho ^ (rawWalk.tail.length - index.val) * rho ^ index.val) *
            (geometricRow * ‖D ^ m‖ * ‖P‖ * Ahead * geometricRow) := by
              ring
        _ = rho ^ layer *
            (geometricRow * ‖D ^ m‖ * ‖P‖ * Ahead * geometricRow) := by
              rw [hpow]
        _ = _ := by ring
    have hchartActive :
        ∀ chart : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
          (domainActive chart).card ≤ 10000 := by
      intro chart
      have hcard :=
        (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
          (Label := Unit) anchor hrange).active_card_le chart
      simpa [domainActive] using hcard
    have hactiveCard :
        active.card ≤ 10000 * (layer + 1) := by
      have hcard :=
        rawWalk.card_active_le_mul_length_add_one
          domainActive 10000 hchartActive
      simpa [active, cmp116SourcePi4ForwardWalkActive,
        rawWalk, CMP99GeneralizedWalk.length, hlen] using hcard
    have hwboundActive :
        ‖w‖ ≤ radius * Rweak ^ active.card := by
      exact norm_cmp116RestrictedOrderedPivotWeight_le
        active carrier e z radius Rweak hradius hRweak hz hcap i
    have hwbound :
        ‖w‖ ≤ radius * Rweak ^ (10000 * (layer + 1)) := by
      exact hwboundActive.trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hRweak hactiveCard) hradius)
    calc
      ‖cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm
          anchor carrier e z K hc hmass hK walk i P D m‖ =
          ‖w * Matrix.trace
            ((P *
              cmp116PhysicalEndomorphismComplexMatrix
                (cmp116SourcePi4ForwardWalkOperator
                  K hc hmass hK rawPair)) * D ^ m)‖ := by
            rfl
      _ ≤ (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
          (‖w‖ *
            (((rho ^ (rawWalk.tail.length - index.val) * geometricRow) *
                ‖D ^ m‖) *
              (‖P‖ * ((Ahead * rho ^ index.val) * geometricRow)))) := by
            simpa [rawPair, rawWalk, active, w, domainActive, index,
              geometricRow] using hbase
      _ = (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
          (‖w‖ *
            (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
              (‖P‖ * (Ahead * geometricRow)))) := by
            rw [hsplit]
      _ ≤ (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
          ((radius * Rweak ^ (10000 * (layer + 1))) *
            (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
              (‖P‖ * (Ahead * geometricRow)))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hwbound hcommon)
              (Nat.cast_nonneg _)

set_option maxHeartbeats 3000000 in

/-- The complete family of length-`layer` physical walks activating one
coordinate has a uniform volume-independent trace bound. -/
theorem sum_norm_cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm_le
    {q M Q Nc R Delta layer : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃ ↥carrier) (z : Fin q → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (i : Fin q)
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) :
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    ∑ walk ∈ cmp99GeneratedWalksActivating
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        (cmp116SourcePi4CoordinateActive anchor) (e i) layer,
      ‖cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm
        anchor carrier e z K hc hmass hK walk i P D m‖ ≤
      (((layer + 1) * 625 *
          cmp116SourcePi4TerminalBranching Delta ^ layer : ℕ) : ℝ) *
        ((((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
          ((radius * Rweak ^ (10000 * (layer + 1))) *
            (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
              (‖P‖ * (Ahead * geometricRow))))) := by
  dsimp only
  let geometricRow :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  let walks :=
    cmp99GeneratedWalksActivating
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      (cmp116SourcePi4CoordinateActive anchor) (e i) layer
  let termBound :=
    (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
      ((radius * Rweak ^ (10000 * (layer + 1))) *
        (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
          (‖P‖ * (Ahead * geometricRow))))
  let cell : FinBox 4 Q := default
  let domain : CMP99SourcePi4Domain Q :=
    cmp99SourcePi4CollarDomain cell
  let chart : CMP99SourcePi4Chart Unit Q := ⟨(), domain⟩
  have hchart :
      chart ∈ (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) := by
    rw [mem_cmp99SourcePi4Charts_iff]
    exact (mem_cmp99SourcePi4Domains_iff domain).2 ⟨cell, rfl⟩
  let chartSub :
      ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) := ⟨chart, hchart⟩
  have hAhead : 0 ≤ Ahead := (Cert.head chartSub).1
  have hrho : 0 ≤ rho := (Cert.continuation chartSub).1
  have hgeometricRow : 0 ≤ geometricRow := by
    dsimp [geometricRow]
    exact mul_nonneg (Nat.cast_nonneg _)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  have htermBound : 0 ≤ termBound := by
    dsimp [termBound]
    positivity
  have hpoint : ∀ walk ∈ walks,
      ‖cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm
        anchor carrier e z K hc hmass hK walk i P D m‖ ≤ termBound := by
    intro walk _hwalk
    simpa [termBound, geometricRow] using
      norm_cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm_le
        anchor carrier e z K hc hmass hK Cert hrate hgeom
        hrange radius Rweak hradius hRweak hz hcap walk i P D m
  have hsum :
      ∑ walk ∈ walks,
          ‖cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm
            anchor carrier e z K hc hmass hK walk i P D m‖ ≤
        (walks.card : ℝ) * termBound := by
    calc
      _ ≤ ∑ _walk ∈ walks, termBound :=
        Finset.sum_le_sum hpoint
      _ = (walks.card : ℝ) * termBound := by simp
  have hcard :
      walks.card ≤
        (layer + 1) * 625 *
          cmp116SourcePi4TerminalBranching Delta ^ layer := by
    simpa [walks] using
      card_cmp116SourcePi4GeneratedWalksActivating_le
        anchor (e i) hrange hDelta hDelta1 layer
  calc
    ∑ walk ∈ walks,
        ‖cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm
          anchor carrier e z K hc hmass hK walk i P D m‖ ≤
      (walks.card : ℝ) * termBound := hsum
    _ ≤ (((layer + 1) * 625 *
        cmp116SourcePi4TerminalBranching Delta ^ layer : ℕ) : ℝ) *
          termBound := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) htermBound

set_option maxHeartbeats 3000000 in

/-- The complete terminal sum for one ordered physical coordinate pivot is
exactly restricted to marked walks and therefore obeys the same uniform
first-hit layer bound. -/
theorem norm_sum_sourceTerminalWalks_coordinatePivotTrace_le
    {q M Q Nc R Delta layer : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃ ↥carrier) (z : Fin q → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (i : Fin q)
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) :
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    ‖∑ terminal : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R layer terminal,
          cmp116RestrictedOrderedPivotWeight
              (cmp116SourcePi4ForwardWalkActive anchor walk)
              carrier e z i *
            Matrix.trace
              ((P *
                cmp116PhysicalEndomorphismComplexMatrix
                  (cmp116SourcePi4ForwardWalkOperator
                    K hc hmass hK walk)) * D ^ m)‖ ≤
      (((layer + 1) * 625 *
          cmp116SourcePi4TerminalBranching Delta ^ layer : ℕ) : ℝ) *
        ((((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
          ((radius * Rweak ^ (10000 * (layer + 1))) *
            (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
              (‖P‖ * (Ahead * geometricRow))))) := by
  dsimp only
  let domainActive :=
    cmp116SourcePi4CoordinateActive anchor
  let F := fun walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) =>
    cmp116RestrictedOrderedPivotWeight
        (cmp116SourcePi4ForwardWalkActive anchor walk)
        carrier e z i *
      Matrix.trace
        ((P *
          cmp116PhysicalEndomorphismComplexMatrix
            (cmp116SourcePi4ForwardWalkOperator
              K hc hmass hK walk)) * D ^ m)
  have hzero : ∀ walk :
      CMP99GeneratedWalkAtLength
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R) layer,
      (e i : FinBox 4 (2 * Q)) ∉
          walk.toGeneralizedWalk.active domainActive →
        F (walk.1, walk.2.1) = 0 := by
    intro walk hnot
    have hnot' :
        (e i : FinBox 4 (2 * Q)) ∉
          cmp116SourcePi4ForwardWalkActive
            anchor (walk.1, walk.2.1) := by
      simpa [domainActive, cmp116SourcePi4CoordinateActive,
        cmp116SourcePi4ForwardWalkActive,
        CMP99GeneratedWalkAtLength.toGeneralizedWalk] using hnot
    simp [F, cmp116RestrictedOrderedPivotWeight, hnot']
  have hreindex :=
    sum_sourceTerminalWalks_eq_sum_generatedWalksActivating
      (M := M) (R := R) (n := layer)
      domainActive (e i) F hzero
  rw [hreindex]
  calc
    ‖∑ walk ∈ cmp99GeneratedWalksActivating
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        domainActive (e i) layer,
        F (walk.1, walk.2.1)‖ ≤
      ∑ walk ∈ cmp99GeneratedWalksActivating
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        domainActive (e i) layer,
        ‖F (walk.1, walk.2.1)‖ := by
          exact norm_sum_le _ _
    _ ≤ (((layer + 1) * 625 *
          cmp116SourcePi4TerminalBranching Delta ^ layer : ℕ) : ℝ) *
        ((((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
          ((radius * Rweak ^ (10000 * (layer + 1))) *
            (((rho ^ layer *
                (((Nc ^ 2 - 1 : ℕ) : ℝ) *
                  cmp99PhysicalBondGeometricRowSum 4 rate)) *
                ‖D ^ m‖) *
              (‖P‖ * (Ahead *
                (((Nc ^ 2 - 1 : ℕ) : ℝ) *
                  cmp99PhysicalBondGeometricRowSum 4 rate)))))) := by
      simpa [domainActive, F,
        cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm] using
        sum_norm_cmp116SourcePi4GeneratedWalkCoordinatePivotTraceTerm_le
          anchor carrier e z K hc hmass hK Cert hrate hgeom
          hrange hDelta hDelta1 radius Rweak hradius hRweak hz hcap
          i P D m

set_option maxHeartbeats 3000000 in
theorem norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_trace_le
    {q M Q Nc R Delta layer : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃ ↥carrier) (z : Fin q → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) :
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    ‖Matrix.trace
        ((P *
          (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
              (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling carrier e z) layer -
            cmp116SourcePi4FullComplexWeakenedCovarianceLayer
              (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
          D ^ m)‖ ≤
      (q : ℝ) *
        ((((layer + 1) * 625 *
            cmp116SourcePi4TerminalBranching Delta ^ layer : ℕ) : ℝ) *
          ((((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
            ((radius * Rweak ^ (10000 * (layer + 1))) *
              (((rho ^ layer * geometricRow) * ‖D ^ m‖) *
                (‖P‖ * (Ahead * geometricRow)))))) := by
  dsimp only
  let B : ℝ :=
    (((layer + 1) * 625 *
        cmp116SourcePi4TerminalBranching Delta ^ layer : ℕ) : ℝ) *
      ((((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        ((radius * Rweak ^ (10000 * (layer + 1))) *
          (((rho ^ layer *
              (((Nc ^ 2 - 1 : ℕ) : ℝ) *
                cmp99PhysicalBondGeometricRowSum 4 rate)) *
              ‖D ^ m‖) *
            (‖P‖ * (Ahead *
              (((Nc ^ 2 - 1 : ℕ) : ℝ) *
                cmp99PhysicalBondGeometricRowSum 4 rate))))))
  change
    ‖Matrix.trace
        ((P *
          (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
              (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling carrier e z) layer -
            cmp116SourcePi4FullComplexWeakenedCovarianceLayer
              (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
          D ^ m)‖ ≤ (q : ℝ) * B
  rw [
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer_restricted_trace_mul_pow_eq_sum_coordinatePivots
      (R := R) anchor carrier e z K hc hmass hK layer P D m]
  rw [Finset.sum_comm]
  calc
    ‖∑ i : Fin q, ∑ terminal, ∑ walk ∈
        cmp99PhysicalPatchForwardTerminalWalks
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R layer terminal,
        cmp116RestrictedOrderedPivotWeight
            (cmp116SourcePi4ForwardWalkActive anchor walk)
            carrier e z i *
          Matrix.trace
            ((P *
              cmp116PhysicalEndomorphismComplexMatrix
                (cmp116SourcePi4ForwardWalkOperator
                  K hc hmass hK walk)) * D ^ m)‖ ≤
      ∑ i : Fin q, ‖∑ terminal, ∑ walk ∈
        cmp99PhysicalPatchForwardTerminalWalks
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R layer terminal,
        cmp116RestrictedOrderedPivotWeight
            (cmp116SourcePi4ForwardWalkActive anchor walk)
            carrier e z i *
          Matrix.trace
            ((P *
              cmp116PhysicalEndomorphismComplexMatrix
                (cmp116SourcePi4ForwardWalkOperator
                  K hc hmass hK walk)) * D ^ m)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin q, B := by
      exact Finset.sum_le_sum fun i _ =>
        (by
          simpa [B] using
            (norm_sum_sourceTerminalWalks_coordinatePivotTrace_le
              (R := R) (Delta := Delta) (layer := layer)
              anchor carrier e z K hc hmass hK Cert hrate hgeom
              hrange hDelta hDelta1 radius Rweak hradius hRweak hz hcap
              i P D m))
    _ = (q : ℝ) * B := by simp [B]

end

end YangMills.RG
