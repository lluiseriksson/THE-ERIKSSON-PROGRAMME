/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116FiniteMultiaffineInterpolation
import YangMills.RG.BalabanCMP116SourcePi4RealMixedCovarianceAffine

/-!
# Finite vertex interpolation of the physical real covariance

On the physical real weakening region, the complete random-walk covariance
is exactly the finite vertex polynomial supplied by separate coordinate
affinity.  The convergence hypotheses remain visible and are used only for
the source operator; the interpolating polynomial itself is globally smooth.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Pointwise physical unit-shift control is preserved when coordinates are
selected from two controlled weakening fields. -/
theorem cmp116AssignWeakeningList_unitShifted
    {D : Type*} [DecidableEq D]
    (base u : D → ℝ) (L : List D)
    (hbase : ∀ x, ‖(base x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hu : ∀ x, ‖(u x : ℂ) - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖(cmp116AssignWeakeningList base u L x : ℂ) - 1‖ ≤
      (1 : ℝ) := by
  intro x
  by_cases hx : x ∈ L
  · simpa [cmp116AssignWeakeningList, hx] using hu x
  · simpa [cmp116AssignWeakeningList, hx] using hbase x

/-- Pointwise physical cap control is preserved by the same assignment. -/
theorem cmp116AssignWeakeningList_cap
    {D : Type*} [DecidableEq D]
    (base u : D → ℝ) (L : List D) (Rweak : ℝ)
    (hbase : ∀ x, ‖(base x : ℂ)‖ ≤ Rweak)
    (hu : ∀ x, ‖(u x : ℂ)‖ ≤ Rweak) :
    ∀ x, ‖(cmp116AssignWeakeningList base u L x : ℂ)‖ ≤ Rweak := by
  intro x
  by_cases hx : x ∈ L
  · simpa [cmp116AssignWeakeningList, hx] using hu x
  · simpa [cmp116AssignWeakeningList, hx] using hbase x

/-- Updating one real coordinate preserves the physical unit-shift bound when
the inserted scalar itself satisfies that bound. -/
theorem cmp116UpdateRealWeakening_unitShifted'
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (d : D) (z : ℝ)
    (hz : ‖(z : ℂ) - 1‖ ≤ (1 : ℝ))
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖((Function.update s d z) x : ℂ) - 1‖ ≤ (1 : ℝ) := by
  intro x
  by_cases hxd : x = d
  · subst x
    simpa using hz
  · simpa [Function.update, hxd] using hs x

/-- Updating one coordinate also preserves the physical cap. -/
theorem cmp116UpdateRealWeakening_cap'
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (d : D) (z Rweak : ℝ)
    (hz : ‖(z : ℂ)‖ ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak) :
    ∀ x, ‖((Function.update s d z) x : ℂ)‖ ≤ Rweak := by
  intro x
  by_cases hxd : x = d
  · subst x
    simpa using hz
  · simpa [Function.update, hxd] using hs x

set_option maxHeartbeats 3000000 in
/-- On every finite list of distinct physical coordinates, the complete real
covariance is exactly its finite vertex interpolation. -/
theorem
    cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_eq
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
    (base u : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hRweak : 1 ≤ Rweak)
    (hbaseShift : ∀ x, ‖(base x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hbaseCap : ∀ x, ‖(base x : ℂ)‖ ≤ Rweak)
    (huShift : ∀ x, ‖(u x : ℂ) - 1‖ ≤ (1 : ℝ))
    (huCap : ∀ x, ‖(u x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    cmp116FiniteMultiaffineInterpolation
        (fun sigma =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK sigma ∅)
        base L u =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK
        (cmp116AssignWeakeningList base u L) ∅ := by
  induction L generalizing base with
  | nil =>
      simp [cmp116FiniteMultiaffineInterpolation]
  | cons d L ih =>
      have hdL : d ∉ L := (List.nodup_cons.mp hL).1
      have hLNodup : L.Nodup := (List.nodup_cons.mp hL).2
      have hbase0Shift :
          ∀ x, ‖((Function.update base d 0) x : ℂ) - 1‖ ≤
            (1 : ℝ) :=
        cmp116UpdateRealWeakening_unitShifted' base d 0 (by norm_num)
          hbaseShift
      have hbase1Shift :
          ∀ x, ‖((Function.update base d 1) x : ℂ) - 1‖ ≤
            (1 : ℝ) :=
        cmp116UpdateRealWeakening_unitShifted' base d 1 (by norm_num)
          hbaseShift
      have hbase0Cap :
          ∀ x, ‖((Function.update base d 0) x : ℂ)‖ ≤ Rweak :=
        cmp116UpdateRealWeakening_cap' base d 0 Rweak
          (by simpa using (le_trans (by norm_num : (0 : ℝ) ≤ 1) hRweak))
          hbaseCap
      have hbase1Cap :
          ∀ x, ‖((Function.update base d 1) x : ℂ)‖ ≤ Rweak :=
        cmp116UpdateRealWeakening_cap' base d 1 Rweak (by simpa using hRweak)
          hbaseCap
      change
        (1 - u d) •
            cmp116FiniteMultiaffineInterpolation
              (fun sigma =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK sigma ∅)
              (Function.update base d 0) L u +
          u d •
            cmp116FiniteMultiaffineInterpolation
              (fun sigma =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK sigma ∅)
              (Function.update base d 1) L u =
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK
          (cmp116AssignWeakeningList base u (d :: L)) ∅
      rw [ih (Function.update base d 0) hLNodup hbase0Shift hbase0Cap,
        ih (Function.update base d 1) hLNodup hbase1Shift hbase1Cap]
      rw [cmp116AssignWeakeningList_update_base_of_not_mem
          base u d L 0 hdL,
        cmp116AssignWeakeningList_update_base_of_not_mem
          base u d L 1 hdL,
        cmp116AssignWeakeningList_cons_of_not_mem base u d L]
      let x := cmp116AssignWeakeningList base u L
      have hxShift : ∀ y, ‖(x y : ℂ) - 1‖ ≤ (1 : ℝ) :=
        cmp116AssignWeakeningList_unitShifted
          base u L hbaseShift huShift
      have hxCap : ∀ y, ‖(x y : ℂ)‖ ≤ Rweak :=
        cmp116AssignWeakeningList_cap base u L Rweak hbaseCap huCap
      have ht :=
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_eq_affine
          anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
          hrange hΔ hΔ1 x ∅ d (by simp) hRweak hxShift hxCap hsmall
          (u d)
      have h1 :=
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_eq_affine
          anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
          hrange hΔ hΔ1 x ∅ d (by simp) hRweak hxShift hxCap hsmall 1
      rw [ht, h1]
      module

/-- If the distinct coordinate list covers the complete finite weakening
space, the globally smooth vertex polynomial agrees with the physical
random-walk covariance at every admissible real weakening field. -/
theorem
    cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_eq_self
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
    (base u : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hcover : ∀ d : FinBox 4 (2 * Q), d ∈ L)
    (hRweak : 1 ≤ Rweak)
    (hbaseShift : ∀ x, ‖(base x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hbaseCap : ∀ x, ‖(base x : ℂ)‖ ≤ Rweak)
    (huShift : ∀ x, ‖(u x : ℂ) - 1‖ ≤ (1 : ℝ))
    (huCap : ∀ x, ‖(u x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    cmp116FiniteMultiaffineInterpolation
        (fun sigma =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK sigma ∅)
        base L u =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK u ∅ := by
  rw [cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealCovariance_eq
    anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
    hΔ hΔ1 base u L hL hRweak hbaseShift hbaseCap huShift huCap hsmall]
  rw [cmp116AssignWeakeningList_eq_of_forall_mem base u L hcover]

end

end YangMills.RG
