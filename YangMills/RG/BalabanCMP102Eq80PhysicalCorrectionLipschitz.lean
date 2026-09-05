/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionLinearBound

/-!
# Lipschitz stability of the selected CMP102 correction

The scalar certificates may vary with the fine field, but the two source
charts are compared at common physical contour radii.  The literal
two-field correction estimate and the linear bound for `H` then give

`|D(A) - D(B)|∞ ≤ L / (1 - L |H|∞) * |A - B|∞`.

No continuity or differentiability of the certificate family is assumed.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

set_option maxHeartbeats 10000000 in
/-- **Volume-uniform Lipschitz stability of the source-defined physical
correction.**  All chart data are generated internally from the two selected
fixed points. -/
theorem cmp102Eq80PhysicalBackgroundCorrection_supNorm_sub_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (A B : FinePhysicalOneCochain d L N' Nc) :
    cmp102PhysicalCorrectionSupNorm
        (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r) (fun _ => s) S hcontract A -
          cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r) (fun _ => s) S hcontract B) ≤
      (cmp102PhysicalCorrectionContractionRate Nc d L r s /
          (1 - ((S A).toBallData).contractionRate)) *
        cmp98SourceFieldSupNorm (A - B) := by
  let DA :=
    cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract A
  let DB :=
    cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract B
  let DAsup : PhysicalGaugeOneCochainSup d N' Nc :=
    physicalGaugeOneCochainSupEquiv DA
  let DBsup : PhysicalGaugeOneCochainSup d N' Nc :=
    physicalGaugeOneCochainSupEquiv DB
  have hDAmem : ‖DAsup‖ ≤ ρ A := by
    simpa [DAsup, DA, norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
      using cmp102Eq80PhysicalBackgroundCorrection_mem_ball
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract A
  have hDBmem : ‖DBsup‖ ≤ ρ B := by
    simpa [DBsup, DB, norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
      using cmp102Eq80PhysicalBackgroundCorrection_mem_ball
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract B
  let XA :=
    A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget DA
  let XB :=
    B - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget DB
  let BA : CMP102PhysicalNonlinearChartBudget U XA :=
    (S A).toBallData.chartBudget DAsup hDAmem
  let BB : CMP102PhysicalNonlinearChartBudget U XB :=
    (S B).toBallData.chartBudget DBsup hDBmem
  have hfixedA :
      cmp102PhysicalNonlinearCorrectionOfBudget U XA BA = DA := by
    have h := cmp102Eq80PhysicalBackgroundCorrection_eq
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract A
    simpa [DA, DAsup, XA, BA,
      cmp102Eq80PhysicalBackgroundCorrection] using h
  have hfixedB :
      cmp102PhysicalNonlinearCorrectionOfBudget U XB BB = DB := by
    have h := cmp102Eq80PhysicalBackgroundCorrection_eq
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract B
    simpa [DB, DBsup, XB, BB,
      cmp102Eq80PhysicalBackgroundCorrection] using h
  have honeA : |(1 : ℝ)| < BA.radius := by
    simpa using BA.one_lt_radius
  have honeB : |(1 : ℝ)| < BB.radius := by
    simpa using BB.one_lt_radius
  have hcorr :=
    cmp102PhysicalCorrectionSupNorm_sub_le
      U XA XB BA.toFieldChart BB.toFieldChart r s
      BA.base
      (by simpa [XA] using BA.small 1 honeA)
      (by simpa [XB] using BB.small 1 honeB)
      (by simpa [XA, BA] using BA.localRadius 1 honeA)
      (by simpa [XB, BB] using BB.localRadius 1 honeB)
      (S A).r_lt_one
      (by simpa [XA, BA] using BA.relativeRadius 1 honeA)
      (by simpa [XB, BB] using BB.relativeRadius 1 honeB)
      (S A).s_lt_one
  have hcorrBudget :
      cmp102PhysicalCorrectionSupNorm (DA - DB) ≤
        cmp102PhysicalCorrectionContractionRate Nc d L r s *
          cmp98SourceFieldSupNorm (XA - XB) := by
    rw [← hfixedA, ← hfixedB]
    simpa [cmp102PhysicalNonlinearCorrectionOfBudget] using hcorr
  have hX :
      XA - XB =
        (A - B) -
          cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
            (DA - DB) := by
    simp only [XA, XB, map_sub]
    abel
  have hH :=
    cmp98SourceFieldSupNorm_cmp99SourceEq3126PhysicalH_le
      U ha hP hε hsmall hbudget (DA - DB)
  have hsource :
      cmp98SourceFieldSupNorm (XA - XB) ≤
        cmp98SourceFieldSupNorm (A - B) +
          cmp99SourceEq3126PhysicalHSourceSupNorm
              U ha hP hε hsmall hbudget *
            cmp102PhysicalCorrectionSupNorm (DA - DB) := by
    rw [hX]
    exact
      (cmp98SourceFieldSupNorm_sub_le (A - B)
        (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
          (DA - DB))).trans
        (add_le_add (le_refl _) hH)
  let Lrate := cmp102PhysicalCorrectionContractionRate Nc d L r s
  let Hrate := cmp99SourceEq3126PhysicalHSourceSupNorm
    U ha hP hε hsmall hbudget
  have hL : 0 ≤ Lrate :=
    cmp102PhysicalCorrectionContractionRate_nonneg
      r s (S A).r_nonneg (S A).s_nonneg
  have hcombined :
      cmp102PhysicalCorrectionSupNorm (DA - DB) ≤
        Lrate * (cmp98SourceFieldSupNorm (A - B) +
          Hrate * cmp102PhysicalCorrectionSupNorm (DA - DB)) := by
    exact hcorrBudget.trans (mul_le_mul_of_nonneg_left
      (by simpa [Hrate] using hsource) hL)
  have hrate :
      ((S A).toBallData).contractionRate = Lrate * Hrate := by
    rfl
  have hsmallRate : Lrate * Hrate < 1 := by
    simpa [hrate] using hcontract A
  have hdenom : 0 < 1 - Lrate * Hrate := sub_pos.mpr hsmallRate
  have hlinear :
      (1 - Lrate * Hrate) *
          cmp102PhysicalCorrectionSupNorm (DA - DB) ≤
        Lrate * cmp98SourceFieldSupNorm (A - B) := by
    nlinarith
  have hbound :
      cmp102PhysicalCorrectionSupNorm (DA - DB) ≤
        (Lrate / (1 - Lrate * Hrate)) *
          cmp98SourceFieldSupNorm (A - B) := by
    calc
      cmp102PhysicalCorrectionSupNorm (DA - DB) ≤
          (Lrate * cmp98SourceFieldSupNorm (A - B)) /
            (1 - Lrate * Hrate) :=
        (le_div_iff₀ hdenom).2 (by simpa [mul_comm] using hlinear)
      _ = (Lrate / (1 - Lrate * Hrate)) *
          cmp98SourceFieldSupNorm (A - B) := by ring
  simpa [DA, DB, Lrate, Hrate, hrate] using hbound

/-- The selected correction, transported to its source sup-norm Banach
space, is globally Lipschitz when the physical contour radii are fixed.
The certificate family itself need not have any regularity. -/
theorem lipschitzWith_cmp102Eq80PhysicalBackgroundCorrection_sup
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1) :
    let Lrate := cmp102PhysicalCorrectionContractionRate Nc d L r s
    let q := ((S 0).toBallData).contractionRate
    let c := Lrate / (1 - q)
    let K : NNReal :=
      ⟨c * ‖(physicalGaugeOneCochainSupEquiv :
          FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
            PhysicalGaugeOneCochainSup d (L * N') Nc).toContinuousLinearMap‖,
        mul_nonneg
          (div_nonneg
            (cmp102PhysicalCorrectionContractionRate_nonneg
              r s (S 0).r_nonneg (S 0).s_nonneg)
            (le_of_lt (sub_pos.mpr (hcontract 0))))
          (norm_nonneg _)⟩
    LipschitzWith K
      (fun A =>
        physicalGaugeOneCochainSupEquiv
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r) (fun _ => s) S hcontract A)) := by
  dsimp only
  let Lrate := cmp102PhysicalCorrectionContractionRate Nc d L r s
  let q := ((S 0).toBallData).contractionRate
  let c := Lrate / (1 - q)
  have hc : 0 ≤ c := by
    exact div_nonneg
      (cmp102PhysicalCorrectionContractionRate_nonneg
        r s (S 0).r_nonneg (S 0).s_nonneg)
      (le_of_lt (sub_pos.mpr (hcontract 0)))
  let K : NNReal :=
    ⟨c * ‖(physicalGaugeOneCochainSupEquiv :
        FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
          PhysicalGaugeOneCochainSup d (L * N') Nc).toContinuousLinearMap‖,
      mul_nonneg hc (norm_nonneg _)⟩
  refine LipschitzWith.of_dist_le_mul fun A B => ?_
  let DA :=
    cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract A
  let DB :=
    cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract B
  have hmain :=
    cmp102Eq80PhysicalBackgroundCorrection_supNorm_sub_le
      U ha hP hε hsmall hbudget ρ radius r s S hcontract A B
  have hrate :
      ((S A).toBallData).contractionRate = q := by
    rfl
  have hsource :
      cmp98SourceFieldSupNorm (A - B) ≤
        ‖(physicalGaugeOneCochainSupEquiv :
            FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
              PhysicalGaugeOneCochainSup d (L * N') Nc).toContinuousLinearMap‖ *
          ‖A - B‖ := by
    rw [← norm_physicalGaugeOneCochainSupEquiv_eq_sourceSupNorm]
    exact
      (physicalGaugeOneCochainSupEquiv :
        FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
          PhysicalGaugeOneCochainSup d (L * N') Nc
      ).toContinuousLinearMap.le_opNorm (A - B)
  calc
    dist (physicalGaugeOneCochainSupEquiv DA)
        (physicalGaugeOneCochainSupEquiv DB) =
        cmp102PhysicalCorrectionSupNorm (DA - DB) := by
      rw [dist_eq_norm, ← map_sub,
        norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
    _ ≤ c * cmp98SourceFieldSupNorm (A - B) := by
      simpa [DA, DB, c, Lrate, hrate] using hmain
    _ ≤ c *
        (‖(physicalGaugeOneCochainSupEquiv :
            FinePhysicalOneCochain d L N' Nc ≃L[ℝ]
              PhysicalGaugeOneCochainSup d (L * N') Nc).toContinuousLinearMap‖ *
          ‖A - B‖) :=
      mul_le_mul_of_nonneg_left hsource hc
    _ = (K : ℝ) * dist A B := by
      simp only [K, NNReal.coe_mk, dist_eq_norm]
      ring

/-- In particular, the selected physical correction is continuous as a map
to the sup-norm correction space. -/
theorem continuous_cmp102Eq80PhysicalBackgroundCorrection_sup
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1) :
    Continuous
      (fun A =>
        physicalGaugeOneCochainSupEquiv
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r) (fun _ => s) S hcontract A)) :=
  (lipschitzWith_cmp102Eq80PhysicalBackgroundCorrection_sup
    U ha hP hε hsmall hbudget ρ radius r s S hcontract).continuous

end

end YangMills.RG
