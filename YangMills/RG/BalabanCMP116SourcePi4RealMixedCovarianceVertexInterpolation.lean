/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4RealCovarianceVertexInterpolation

/-!
# Vertex interpolation of every physical mixed covariance

The finite interpolation theorem extends from the complete covariance to any
already differentiated carrier `S`, provided the newly interpolated
coordinates are fresh.  This is the source-facing jet statement needed for
the arbitrary-depth equation-(80) FTC expansion.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 4000000 in
/-- A finite list of fresh coordinates interpolates the physical covariance
with existing mixed-derivative carrier `S` exactly. -/
theorem
    cmp116FiniteMultiaffineInterpolation_sourcePi4FullRealMixedCovariance_eq
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
    (S : Finset (FinBox 4 (2 * Q)))
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hfresh : ∀ d ∈ L, d ∉ S)
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
            (R := R) anchor K hc hmass hK sigma S)
        base L u =
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK
        (cmp116AssignWeakeningList base u L) S := by
  induction L generalizing base with
  | nil =>
      simp [cmp116FiniteMultiaffineInterpolation]
  | cons d L ih =>
      have hdL : d ∉ L := (List.nodup_cons.mp hL).1
      have hLNodup : L.Nodup := (List.nodup_cons.mp hL).2
      have hdS : d ∉ S := hfresh d (by simp)
      have htailFresh : ∀ e ∈ L, e ∉ S := by
        intro e he
        exact hfresh e (by simp [he])
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
        cmp116UpdateRealWeakening_cap' base d 1 Rweak
          (by simpa using hRweak) hbaseCap
      change
        (1 - u d) •
            cmp116FiniteMultiaffineInterpolation
              (fun sigma =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK sigma S)
              (Function.update base d 0) L u +
          u d •
            cmp116FiniteMultiaffineInterpolation
              (fun sigma =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK sigma S)
              (Function.update base d 1) L u =
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK
          (cmp116AssignWeakeningList base u (d :: L)) S
      rw [ih (Function.update base d 0) hLNodup htailFresh
          hbase0Shift hbase0Cap,
        ih (Function.update base d 1) hLNodup htailFresh
          hbase1Shift hbase1Cap]
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
          hrange hΔ hΔ1 x S d hdS hRweak hxShift hxCap hsmall (u d)
      have h1 :=
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_update_eq_affine
          anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
          hrange hΔ hΔ1 x S d hdS hRweak hxShift hxCap hsmall 1
      rw [ht, h1]
      module

end

end YangMills.RG
