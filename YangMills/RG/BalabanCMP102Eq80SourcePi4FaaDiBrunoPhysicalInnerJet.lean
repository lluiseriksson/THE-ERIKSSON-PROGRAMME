/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FaaDiBruno
import YangMills.RG.BalabanCMP116SourcePi4RealMixedCovarianceVertexInterpolation
import YangMills.RG.BalabanCMP116FiniteMultiaffineInterpolationJet

/-!
# Physical inner jet for the equation-(80) Faà di Bruno formula

The arbitrary-depth composition formula contains derivatives of the smooth
finite vertex interpolant.  This file identifies its first Taylor
coefficient in a canonical weakening-coordinate direction with the literal
next source-produced mixed covariance.

The equality is obtained from the physical contour derivative theorem and
uniqueness of the derivative of the same one-dimensional coordinate curve.
It is not a formal finite-difference definition of the jet.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Real physical weakening region used by the source covariance contour
estimates. -/
def CMP116RealPhysicalContourRegion
    {D : Type*} (Rweak : ℝ) (s : D → ℝ) : Prop :=
  (∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ)) ∧
    ∀ x, ‖(s x : ℂ)‖ ≤ Rweak

/-- The physical weakening region is stable under every `0/1` vertex update
when the contour cap is at least one. -/
theorem cmp116RealPhysicalContourRegion_update_zero_one
    {D : Type*} [DecidableEq D]
    (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
    (s : D → ℝ) (d : D)
    (hs : CMP116RealPhysicalContourRegion Rweak s) :
    CMP116RealPhysicalContourRegion Rweak (Function.update s d 0) ∧
      CMP116RealPhysicalContourRegion Rweak (Function.update s d 1) := by
  constructor
  · exact ⟨
      cmp116UpdateRealWeakening_unitShifted' s d 0 (by norm_num) hs.1,
      cmp116UpdateRealWeakening_cap' s d 0 Rweak
        (by
          have hzero : (0 : ℝ) ≤ Rweak := le_trans (by norm_num) hRweak
          simpa using hzero)
        hs.2⟩
  · exact ⟨
      cmp116UpdateRealWeakening_unitShifted' s d 1 (by norm_num) hs.1,
      cmp116UpdateRealWeakening_cap' s d 1 Rweak
        (by simpa using hRweak) hs.2⟩

set_option maxHeartbeats 4000000 in
/-- The literal unit finite difference of a physical mixed covariance in a
fresh coordinate is the next mixed covariance.  This is the source-facing
recursion consumed by the arbitrary coordinate-jet theorem. -/
theorem
    cmp116CoordinateFiniteDifference_sourcePi4FullRealMixedCovariance_eq_insert
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) (hdS : d ∉ S)
    (hRweak : 1 ≤ Rweak)
    (hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    cmp116CoordinateFiniteDifference
        (fun sigma =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK sigma S)
        d s =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s (insert d S) := by
  have h :=
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_eq_affine
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
      hrange hΔ hΔ1 s S d hdS hRweak hsShift hsCap hsmall 1
  unfold cmp116CoordinateFiniteDifference
  change
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK (Function.update s d 1) S -
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK (Function.update s d 0) S =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s (insert d S)
  rw [h]
  module

set_option maxHeartbeats 8000000 in
/-- Every arbitrary-depth iterated unit finite difference of the physical
source covariance is the literal mixed covariance whose carrier is obtained
by recursively inserting the selected coordinates.  The proof only uses
the physical `0/1` cube; no convergence claim is extended outside the
certified real contour region. -/
theorem
    cmp116IteratedCoordinateFiniteDifference_sourcePi4FullRealMixedCovariance_eq_carrier
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (n : ℕ) (coordinates : Fin n → FinBox 4 (2 * Q))
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (hfresh : CMP116IteratedCoordinatesFresh n coordinates S)
    (hRweak : 1 ≤ Rweak)
    (hs : CMP116RealPhysicalContourRegion Rweak s)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    cmp116IteratedCoordinateFiniteDifference n
        (fun sigma =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK sigma S)
        coordinates s =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s
        (cmp116IteratedCoordinateCarrier n coordinates S) := by
  induction n generalizing S with
  | zero =>
      simp [cmp116IteratedCoordinateFiniteDifference,
        cmp116IteratedCoordinateCarrier]
  | succ n ih =>
      let dlast := coordinates (Fin.last n)
      let initCoordinates : Fin n → FinBox 4 (2 * Q) :=
        fun i => coordinates i.castSucc
      have hfreshLast : dlast ∉ S := by
        exact hfresh.1
      have hfreshInit :
          CMP116IteratedCoordinatesFresh n initCoordinates
            (insert dlast S) := by
        exact hfresh.2
      let F :
          (FinBox 4 (2 * Q) → ℝ) → PhysicalEndomorphism M Q Nc :=
        cmp116CoordinateFiniteDifference
          (fun sigma =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK sigma S)
          dlast
      let G :
          (FinBox 4 (2 * Q) → ℝ) → PhysicalEndomorphism M Q Nc :=
        fun sigma =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK sigma (insert dlast S)
      have hAgree :
          CMP116AgreeOnCoordinateCube n initCoordinates s F G := by
        intro bits
        let u :=
          cmp116CoordinateCubePoint n initCoordinates s bits
        have hu :
            CMP116RealPhysicalContourRegion Rweak u :=
          cmp116CoordinateCubePoint_property
            (CMP116RealPhysicalContourRegion Rweak)
            (fun v d hv =>
              cmp116RealPhysicalContourRegion_update_zero_one
                Rweak hRweak v d hv)
            n initCoordinates s hs bits
        exact
          cmp116CoordinateFiniteDifference_sourcePi4FullRealMixedCovariance_eq_insert
            anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
            hrange hΔ hΔ1 u S dlast hfreshLast hRweak hu.1 hu.2 hsmall
      have hcongr :=
        cmp116IteratedCoordinateFiniteDifference_congr_on_cube
          n initCoordinates s F G hAgree
      have hnext :=
        ih initCoordinates (insert dlast S) hfreshInit
      simpa [cmp116IteratedCoordinateFiniteDifference,
        cmp116IteratedCoordinateCarrier, initCoordinates, dlast, F, G]
        using hcongr.trans hnext

set_option maxHeartbeats 5000000 in
/-- The Fréchet derivative of the mixed-covariance vertex polynomial in one
fresh canonical coordinate is the next physical mixed covariance. -/
theorem
    fderiv_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealMixedCovariance_apply_single
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hfresh : ∀ e ∈ L, e ∉ S)
    (d : FinBox 4 (2 * Q)) (hdL : d ∈ L)
    (hRweak : 1 ≤ Rweak)
    (hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    fderiv ℝ
        (cmp116FiniteMultiaffineInterpolation
          (fun sigma =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK sigma S)
          s L)
        s (Pi.single d 1) =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s (insert d S) := by
  let P :=
    cmp116FiniteMultiaffineInterpolation
      (fun sigma =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK sigma S)
      s L
  have hP :
      DifferentiableAt ℝ P (Function.update s d (s d)) :=
    (contDiff_cmp116FiniteMultiaffineInterpolation
      1
      (fun sigma =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK sigma S)
      s L).differentiable one_ne_zero _
  have hcurve :=
    hasDerivAt_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealMixedCovariance
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
      hrange hΔ hΔ1 s S L hL hfresh d hdL hRweak hsShift hsCap
      hsmall (s d)
  have hchain :
      HasDerivAt
        (fun u => P (Function.update s d u))
        (fderiv ℝ P s (Pi.single d 1)) (s d) := by
    have h :=
      hP.hasFDerivAt.comp_hasDerivAt (s d)
        (hasDerivAt_update s d (s d))
    simpa [Function.comp_def] using h
  exact hchain.unique hcurve

set_option maxHeartbeats 5000000 in
/-- The order-one Taylor coefficient used by Faà di Bruno is therefore the
literal next physical mixed covariance. -/
theorem
    ftaylorSeries_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealMixedCovariance_one_apply_single
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hfresh : ∀ e ∈ L, e ∉ S)
    (d : FinBox 4 (2 * Q)) (hdL : d ∈ L)
    (hRweak : 1 ≤ Rweak)
    (hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ftaylorSeries ℝ
        (cmp116FiniteMultiaffineInterpolation
          (fun sigma =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK sigma S)
          s L)
        s 1 (fun _ => Pi.single d 1) =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s (insert d S) := by
  simpa [ftaylorSeries] using
    fderiv_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealMixedCovariance_apply_single
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
      hrange hΔ hΔ1 s S L hL hfresh d hdL hRweak hsShift hsCap hsmall

set_option maxHeartbeats 10000000 in
/-- Arbitrary physical inner Taylor coefficient used by Faà di Bruno.
For a fresh indexed block of weakening coordinates, the smooth vertex
polynomial's complete coordinate jet is literally the source-produced mixed
covariance with precisely that recursively inserted carrier. -/
theorem
    ftaylorSeries_cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_apply_coordinateBlock
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (base : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hcover : ∀ d : FinBox 4 (2 * Q), d ∈ L)
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (hfresh : CMP116IteratedCoordinatesFresh n coordinates ∅)
    (hRweak : 1 ≤ Rweak)
    (hbase : CMP116RealPhysicalContourRegion Rweak base)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ftaylorSeries ℝ
        (cmp116FiniteMultiaffineInterpolation
          (fun sigma =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK sigma ∅)
          base L)
        base n (fun i => Pi.single (coordinates i) 1) =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK base
        (cmp116IteratedCoordinateCarrier n coordinates ∅) := by
  let P :
      (FinBox 4 (2 * Q) → ℝ) → PhysicalEndomorphism M Q Nc :=
    cmp116FiniteMultiaffineInterpolation
      (fun sigma =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK sigma ∅)
      base L
  let G :
      (FinBox 4 (2 * Q) → ℝ) → PhysicalEndomorphism M Q Nc :=
    fun sigma =>
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK sigma ∅
  have hjet :
      iteratedFDeriv ℝ n P base
          (fun i => Pi.single (coordinates i) 1) =
        cmp116IteratedCoordinateFiniteDifference n P coordinates base := by
    exact
      iteratedFDeriv_cmp116FiniteMultiaffineInterpolation_apply_single_eq_iteratedFiniteDifference
        n
        (fun sigma =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK sigma ∅)
        base L hL coordinates base
  have hAgree :
      CMP116AgreeOnCoordinateCube n coordinates base P G := by
    intro bits
    let u := cmp116CoordinateCubePoint n coordinates base bits
    have hu : CMP116RealPhysicalContourRegion Rweak u :=
      cmp116CoordinateCubePoint_property
        (CMP116RealPhysicalContourRegion Rweak)
        (fun v d hv =>
          cmp116RealPhysicalContourRegion_update_zero_one
            Rweak hRweak v d hv)
        n coordinates base hbase bits
    exact
      cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_eq_self
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
        hrange hΔ hΔ1 base u L hL hcover hRweak hbase.1 hbase.2
        hu.1 hu.2 hsmall
  have hcongr :
      cmp116IteratedCoordinateFiniteDifference n P coordinates base =
        cmp116IteratedCoordinateFiniteDifference n G coordinates base :=
    cmp116IteratedCoordinateFiniteDifference_congr_on_cube
      n coordinates base P G hAgree
  have hphysical :
      cmp116IteratedCoordinateFiniteDifference n G coordinates base =
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK base
          (cmp116IteratedCoordinateCarrier n coordinates ∅) := by
    exact
      cmp116IteratedCoordinateFiniteDifference_sourcePi4FullRealMixedCovariance_eq_carrier
        anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
        hrange hΔ hΔ1 n coordinates base ∅ hfresh hRweak hbase hsmall
  change
    iteratedFDeriv ℝ n P base
        (fun i => Pi.single (coordinates i) 1) =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK base
        (cmp116IteratedCoordinateCarrier n coordinates ∅)
  exact hjet.trans (hcongr.trans hphysical)

end

end YangMills.RG
