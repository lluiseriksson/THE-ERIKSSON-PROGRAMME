/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinPeriodicTranslation

/-!
# The fully translation-invariant Dobrushin site-cylinder state

The compatible centred family of D-7 descends to the algebraic direct limit
of integer site cylinders.  Periodic finite-volume translation invariance is
then combined with the already-proved free--periodic limit equality.  The
result is a positive normalized real-linear state invariant under every
element of the genuine additive group `Z^2`, including inverse translations.

The only analytic hypothesis is the visible Dobrushin window
`2*tanh|beta| + 2*tanh|gamma| <= alpha < 1`.  No KP regime, thermodynamic
limit premise, or translation-invariance premise is an argument of the
terminal construction.
-/

namespace YangMills.OS
namespace Dobrushin

open Classical Filter Topology

namespace SiteCylinderPresentation

/-- Value selected by the D-7 centred state for one integer presentation. -/
noncomputable def infiniteValue
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (O : SiteCylinderPresentation) : ℝ :=
  infiniteCenteredLocalGibbsExpectation beta gamma alpha halpha0 halpha1 hwin
    O.radius (O.toCenteredKernelAt O.radius le_rfl)

/-- The raw value is independent of the chosen finite presentation. -/
theorem infiniteValue_eq_of_equivalent
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (O P : SiteCylinderPresentation) (hOP : O.Equivalent P) :
    O.infiniteValue beta gamma alpha halpha0 halpha1 hwin =
      P.infiniteValue beta gamma alpha halpha0 halpha1 hwin := by
  let R := max O.radius P.radius
  have hO : O.radius ≤ R := Nat.le_max_left _ _
  have hP : P.radius ≤ R := Nat.le_max_right _ _
  have hOlift := infiniteCenteredLocalGibbsExpectation_lift
    beta gamma alpha halpha0 halpha1 hwin hO
      (O.toCenteredKernelAt O.radius le_rfl)
  have hPlift := infiniteCenteredLocalGibbsExpectation_lift
    beta gamma alpha halpha0 halpha1 hwin hP
      (P.toCenteredKernelAt P.radius le_rfl)
  rw [O.liftCenteredObservable_toCenteredKernelAt le_rfl hO] at hOlift
  rw [P.liftCenteredObservable_toCenteredKernelAt le_rfl hP] at hPlift
  unfold infiniteValue
  rw [← hOlift, ← hPlift]
  rw [O.toCenteredKernelAt_eq_of_equivalent P hOP R hO hP]

/-! ## A common-radius periodic chart -/

/-- The site of a presentation in the outer periodic square attached to a
common centred radius. -/
noncomputable def outerSite (O : SiteCylinderPresentation) (R : ℕ)
    (hR : O.radius ≤ R) (n : ℕ) (q : O.support) : CenteredRect (R + n) :=
  (centeredRectEquiv (Nat.le_add_right R n) (O.siteAt R hR q)).1

/-- Periodic expectation of an integer presentation through a common centred
chart. -/
noncomputable def periodicExpectationAt
    (beta gamma : ℝ) (O : SiteCylinderPresentation) (R : ℕ)
    (hR : O.radius ≤ R) (n : ℕ) : ℝ :=
  expect (gibbsMu (isingWeight
      (periodicRectJ (L := 2 * (R + n) + 1) (T := 2 * (R + n) + 1)
        beta gamma)))
    (fun eta => O.kernel (fun q => eta (O.outerSite R hR n q)))

theorem periodicExpectationAt_eq_centeredPeriodic
    (beta gamma : ℝ) (O : SiteCylinderPresentation) (R : ℕ)
    (hR : O.radius ≤ R) (n : ℕ) :
    O.periodicExpectationAt beta gamma R hR n =
      centeredPeriodicGibbsExpectation beta gamma R
        (O.toCenteredKernelAt R hR) n := by
  rfl

/-- Every common-radius periodic sequence converges to the intrinsic value of
the presentation. -/
theorem tendsto_periodicExpectationAt
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (O : SiteCylinderPresentation) (R : ℕ) (hR : O.radius ≤ R) :
    Tendsto (O.periodicExpectationAt beta gamma R hR) atTop
      (𝓝 (O.infiniteValue beta gamma alpha halpha0 halpha1 hwin)) := by
  have hper := tendsto_centeredPeriodicGibbsExpectation
    beta gamma alpha halpha0 halpha1 hwin R (O.toCenteredKernelAt R hR)
  have hlift := infiniteCenteredLocalGibbsExpectation_lift
    beta gamma alpha halpha0 halpha1 hwin hR
      (O.toCenteredKernelAt O.radius le_rfl)
  rw [O.liftCenteredObservable_toCenteredKernelAt le_rfl hR] at hlift
  unfold infiniteValue
  rw [hlift] at hper
  simpa only [periodicExpectationAt_eq_centeredPeriodic] using hper

/-- Positive unit vector in an integer lattice direction. -/
def unitVector (i : Fin 2) : IsingSite := Pi.single i 1

@[simp] theorem outerSite_fst_val
    (O : SiteCylinderPresentation) (R : ℕ) (hR : O.radius ≤ R)
    (n : ℕ) (q : O.support) :
    (O.outerSite R hR n q).1.val = Int.toNat (q.1 0 + (R : ℤ)) + n := by
  unfold outerSite
  change Int.toNat (q.1 0 + (R : ℤ)) + ((R + n) - R) = _
  omega

@[simp] theorem outerSite_snd_val
    (O : SiteCylinderPresentation) (R : ℕ) (hR : O.radius ≤ R)
    (n : ℕ) (q : O.support) :
    (O.outerSite R hR n q).2.val = Int.toNat (q.1 1 + (R : ℤ)) + n := by
  unfold outerSite
  change Int.toNat (q.1 1 + (R : ℤ)) + ((R + n) - R) = _
  omega

theorem outerSite_translate_unit_zero
    (O : SiteCylinderPresentation) (R n : ℕ)
    (hO : O.radius ≤ R)
    (hT : (O.translate (unitVector 0)).radius ≤ R)
    (q : O.support) :
    (O.translate (unitVector 0)).outerSite R hT n
        ⟨q.1 + unitVector 0, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩ =
      torusShiftX (2 * (R + n) + 1) (O.outerSite R hO n q) := by
  apply Prod.ext
  · apply Fin.ext
    rw [outerSite_fst_val, torusShiftX_fst_val, outerSite_fst_val]
    simp only [unitVector, Pi.add_apply, Pi.single_eq_same]
    have hlo := O.neg_radius_le_coord q.1 q.2 0
    have hTmem : q.1 + unitVector 0 ∈ (O.translate (unitVector 0)).support :=
      Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩
    have hhi := (O.translate (unitVector 0)).coord_le_radius
      (q.1 + unitVector 0) hTmem 0
    have hcoord : (q.1 + unitVector 0) 0 = q.1 0 + 1 := by
      simp [unitVector]
    rw [hcoord] at hhi
    have hrad : (((O.translate (unitVector 0)).radius : ℕ) : ℤ) ≤ (R : ℤ) := by
      exact_mod_cast hT
    have hn0 : 0 ≤ q.1 0 + (R : ℤ) := by omega
    have hn1 : 0 ≤ q.1 0 + 1 + (R : ℤ) := by omega
    have hcast0 := Int.toNat_of_nonneg hn0
    have hcast1 := Int.toNat_of_nonneg hn1
    rw [Nat.mod_eq_of_lt (by omega :
      Int.toNat (q.1 0 + (R : ℤ)) + n + 1 < 2 * (R + n) + 1)]
    omega
  · apply Fin.ext
    rw [outerSite_snd_val, torusShiftX_snd, outerSite_snd_val]
    simp [unitVector]

theorem outerSite_translate_unit_one
    (O : SiteCylinderPresentation) (R n : ℕ)
    (hO : O.radius ≤ R)
    (hT : (O.translate (unitVector 1)).radius ≤ R)
    (q : O.support) :
    (O.translate (unitVector 1)).outerSite R hT n
        ⟨q.1 + unitVector 1, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩ =
      torusShiftY (2 * (R + n) + 1) (O.outerSite R hO n q) := by
  apply Prod.ext
  · apply Fin.ext
    rw [outerSite_fst_val, torusShiftY_fst, outerSite_fst_val]
    simp [unitVector]
  · apply Fin.ext
    rw [outerSite_snd_val, torusShiftY_snd_val, outerSite_snd_val]
    simp only [unitVector, Pi.add_apply, Pi.single_eq_same]
    have hlo := O.neg_radius_le_coord q.1 q.2 1
    have hTmem : q.1 + unitVector 1 ∈ (O.translate (unitVector 1)).support :=
      Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩
    have hhi := (O.translate (unitVector 1)).coord_le_radius
      (q.1 + unitVector 1) hTmem 1
    have hcoord : (q.1 + unitVector 1) 1 = q.1 1 + 1 := by
      simp [unitVector]
    rw [hcoord] at hhi
    have hrad : (((O.translate (unitVector 1)).radius : ℕ) : ℤ) ≤ (R : ℤ) := by
      exact_mod_cast hT
    have hn0 : 0 ≤ q.1 1 + (R : ℤ) := by omega
    have hn1 : 0 ≤ q.1 1 + 1 + (R : ℤ) := by omega
    have hcast0 := Int.toNat_of_nonneg hn0
    have hcast1 := Int.toNat_of_nonneg hn1
    rw [Nat.mod_eq_of_lt (by omega :
      Int.toNat (q.1 1 + (R : ℤ)) + n + 1 < 2 * (R + n) + 1)]
    omega

theorem periodicExpectationAt_translate_unit_zero
    (beta gamma : ℝ) (O : SiteCylinderPresentation) (R : ℕ)
    (hO : O.radius ≤ R)
    (hT : (O.translate (unitVector 0)).radius ≤ R) (n : ℕ) :
    (O.translate (unitVector 0)).periodicExpectationAt beta gamma R hT n =
      O.periodicExpectationAt beta gamma R hO n := by
  unfold periodicExpectationAt SiteCylinderPresentation.translate
  let f : ((CenteredRect (R + n)) → Fin 2) → ℝ :=
    fun eta => O.kernel (fun q => eta (O.outerSite R hO n q))
  have hshift := expect_periodic_torusShiftX
    (2 * (R + n) + 1) beta gamma f
  change
    expect (gibbsMu (isingWeight
      (periodicRectJ (L := 2 * (R + n) + 1) (T := 2 * (R + n) + 1)
        beta gamma)))
      (fun eta => O.kernel (fun q =>
        eta ((O.translate (unitVector 0)).outerSite R hT n
          ⟨q.1 + unitVector 0, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩))) = _
  calc
    _ = expect (gibbsMu (isingWeight
        (periodicRectJ (L := 2 * (R + n) + 1) (T := 2 * (R + n) + 1)
          beta gamma)))
        (fun eta => f (fun p => eta (torusShiftX (2 * (R + n) + 1) p))) := by
      apply congrArg (expect (gibbsMu (isingWeight
        (periodicRectJ (L := 2 * (R + n) + 1) (T := 2 * (R + n) + 1)
          beta gamma))))
      funext eta
      apply congrArg O.kernel
      funext q
      exact congrArg eta (O.outerSite_translate_unit_zero R n hO hT q)
    _ = _ := hshift

theorem periodicExpectationAt_translate_unit_one
    (beta gamma : ℝ) (O : SiteCylinderPresentation) (R : ℕ)
    (hO : O.radius ≤ R)
    (hT : (O.translate (unitVector 1)).radius ≤ R) (n : ℕ) :
    (O.translate (unitVector 1)).periodicExpectationAt beta gamma R hT n =
      O.periodicExpectationAt beta gamma R hO n := by
  unfold periodicExpectationAt SiteCylinderPresentation.translate
  let f : ((CenteredRect (R + n)) → Fin 2) → ℝ :=
    fun eta => O.kernel (fun q => eta (O.outerSite R hO n q))
  have hshift := expect_periodic_torusShiftY
    (2 * (R + n) + 1) beta gamma f
  change
    expect (gibbsMu (isingWeight
      (periodicRectJ (L := 2 * (R + n) + 1) (T := 2 * (R + n) + 1)
        beta gamma)))
      (fun eta => O.kernel (fun q =>
        eta ((O.translate (unitVector 1)).outerSite R hT n
          ⟨q.1 + unitVector 1, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩))) = _
  calc
    _ = expect (gibbsMu (isingWeight
        (periodicRectJ (L := 2 * (R + n) + 1) (T := 2 * (R + n) + 1)
          beta gamma)))
        (fun eta => f (fun p => eta (torusShiftY (2 * (R + n) + 1) p))) := by
      apply congrArg (expect (gibbsMu (isingWeight
        (periodicRectJ (L := 2 * (R + n) + 1) (T := 2 * (R + n) + 1)
          beta gamma))))
      funext eta
      apply congrArg O.kernel
      funext q
      exact congrArg eta (O.outerSite_translate_unit_one R n hO hT q)
    _ = _ := hshift

/-- Invariance of the infinite value under either positive generator. -/
theorem infiniteValue_translate_unit
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (O : SiteCylinderPresentation) (i : Fin 2) :
    (O.translate (unitVector i)).infiniteValue
        beta gamma alpha halpha0 halpha1 hwin =
      O.infiniteValue beta gamma alpha halpha0 halpha1 hwin := by
  let T := O.translate (unitVector i)
  let R := max O.radius T.radius
  have hO : O.radius ≤ R := Nat.le_max_left _ _
  have hT : T.radius ≤ R := Nat.le_max_right _ _
  have hlimO := O.tendsto_periodicExpectationAt
    beta gamma alpha halpha0 halpha1 hwin R hO
  have hlimT := T.tendsto_periodicExpectationAt
    beta gamma alpha halpha0 halpha1 hwin R hT
  have heq : T.periodicExpectationAt beta gamma R hT =
      O.periodicExpectationAt beta gamma R hO := by
    funext n
    fin_cases i
    · exact O.periodicExpectationAt_translate_unit_zero beta gamma R hO hT n
    · exact O.periodicExpectationAt_translate_unit_one beta gamma R hO hT n
  rw [heq] at hlimT
  exact tendsto_nhds_unique hlimT hlimO

end SiteCylinderPresentation

/-! ## Descent to the quotient and the terminal state -/

namespace LocalCylinderAlgebra

/-- The infinite-volume value on the algebraic direct limit. -/
noncomputable def infiniteStateValue
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha) :
    LocalCylinderAlgebra → ℝ :=
  Quotient.lift
    (SiteCylinderPresentation.infiniteValue
      beta gamma alpha halpha0 halpha1 hwin)
    (SiteCylinderPresentation.infiniteValue_eq_of_equivalent
      beta gamma alpha halpha0 halpha1 hwin)

theorem infiniteStateValue_add
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (O P : LocalCylinderAlgebra) :
    infiniteStateValue beta gamma alpha halpha0 halpha1 hwin (O + P) =
      infiniteStateValue beta gamma alpha halpha0 halpha1 hwin O +
        infiniteStateValue beta gamma alpha halpha0 halpha1 hwin P := by
  induction O using Quotient.inductionOn with
  | _ O =>
      induction P using Quotient.inductionOn with
      | _ P =>
          change (SiteCylinderPresentation.add O P).infiniteValue
              beta gamma alpha halpha0 halpha1 hwin =
            O.infiniteValue beta gamma alpha halpha0 halpha1 hwin +
              P.infiniteValue beta gamma alpha halpha0 halpha1 hwin
          let R := max O.radius P.radius
          have hO : O.radius ≤ R := Nat.le_max_left _ _
          have hP : P.radius ≤ R := Nat.le_max_right _ _
          have hAdd : (SiteCylinderPresentation.add O P).radius ≤
              max (SiteCylinderPresentation.add O P).radius R :=
            Nat.le_max_left _ _
          let S := max (SiteCylinderPresentation.add O P).radius R
          have hOS : O.radius ≤ S := hO.trans (Nat.le_max_right _ _)
          have hPS : P.radius ≤ S := hP.trans (Nat.le_max_right _ _)
          have hAS : (SiteCylinderPresentation.add O P).radius ≤ S := hAdd
          have hA := infiniteCenteredLocalGibbsExpectation_lift
            beta gamma alpha halpha0 halpha1 hwin hAS
              ((SiteCylinderPresentation.add O P).toCenteredKernelAt
                (SiteCylinderPresentation.add O P).radius le_rfl)
          have hOlift := infiniteCenteredLocalGibbsExpectation_lift
            beta gamma alpha halpha0 halpha1 hwin hOS
              (O.toCenteredKernelAt O.radius le_rfl)
          have hPlift := infiniteCenteredLocalGibbsExpectation_lift
            beta gamma alpha halpha0 halpha1 hwin hPS
              (P.toCenteredKernelAt P.radius le_rfl)
          rw [SiteCylinderPresentation.liftCenteredObservable_toCenteredKernelAt
            (SiteCylinderPresentation.add O P) le_rfl hAS] at hA
          rw [O.liftCenteredObservable_toCenteredKernelAt le_rfl hOS] at hOlift
          rw [P.liftCenteredObservable_toCenteredKernelAt le_rfl hPS] at hPlift
          unfold SiteCylinderPresentation.infiniteValue
          rw [← hA, ← hOlift, ← hPlift]
          apply infiniteCenteredLocalGibbsExpectation_add

theorem infiniteStateValue_smul
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (c : ℝ) (O : LocalCylinderAlgebra) :
    infiniteStateValue beta gamma alpha halpha0 halpha1 hwin (c • O) =
      c * infiniteStateValue beta gamma alpha halpha0 halpha1 hwin O := by
  induction O using Quotient.inductionOn with
  | _ O =>
      change (SiteCylinderPresentation.smul c O).infiniteValue
          beta gamma alpha halpha0 halpha1 hwin =
        c * O.infiniteValue beta gamma alpha halpha0 halpha1 hwin
      let S := max (SiteCylinderPresentation.smul c O).radius O.radius
      have hS : (SiteCylinderPresentation.smul c O).radius ≤ S := Nat.le_max_left _ _
      have hO : O.radius ≤ S := Nat.le_max_right _ _
      have hsmul := infiniteCenteredLocalGibbsExpectation_lift
        beta gamma alpha halpha0 halpha1 hwin hS
          ((SiteCylinderPresentation.smul c O).toCenteredKernelAt
            (SiteCylinderPresentation.smul c O).radius le_rfl)
      have hOlift := infiniteCenteredLocalGibbsExpectation_lift
        beta gamma alpha halpha0 halpha1 hwin hO
          (O.toCenteredKernelAt O.radius le_rfl)
      rw [SiteCylinderPresentation.liftCenteredObservable_toCenteredKernelAt
        (SiteCylinderPresentation.smul c O) le_rfl hS] at hsmul
      rw [O.liftCenteredObservable_toCenteredKernelAt le_rfl hO] at hOlift
      unfold SiteCylinderPresentation.infiniteValue
      rw [← hsmul, ← hOlift]
      apply infiniteCenteredLocalGibbsExpectation_smul

theorem infiniteStateValue_one
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha) :
    infiniteStateValue beta gamma alpha halpha0 halpha1 hwin 1 = 1 := by
  change (SiteCylinderPresentation.const 1).infiniteValue
    beta gamma alpha halpha0 halpha1 hwin = 1
  unfold SiteCylinderPresentation.infiniteValue
  simpa using infiniteCenteredLocalGibbsExpectation_one
    beta gamma alpha halpha0 halpha1 hwin
      (SiteCylinderPresentation.const 1).radius

theorem infiniteStateValue_nonneg
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (O : LocalCylinderAlgebra)
    (hO : ∀ sigma, 0 ≤ O.realizeGlobal sigma) :
    0 ≤ infiniteStateValue beta gamma alpha halpha0 halpha1 hwin O := by
  induction O using Quotient.inductionOn with
  | _ O =>
      change 0 ≤ O.infiniteValue beta gamma alpha halpha0 halpha1 hwin
      unfold SiteCylinderPresentation.infiniteValue
      apply infiniteCenteredLocalGibbsExpectation_nonneg
      intro eta
      rw [O.toCenteredKernelAt_eq_realizeGlobal_extend]
      exact hO _

/-- Invariance under every element of the full integer translation group. -/
theorem infiniteStateValue_vadd
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)
    (z : IsingSite) (O : LocalCylinderAlgebra) :
    infiniteStateValue beta gamma alpha halpha0 halpha1 hwin (z +ᵥ O) =
      infiniteStateValue beta gamma alpha halpha0 halpha1 hwin O := by
  have hunit : ∀ (i : Fin 2) (P : LocalCylinderAlgebra),
      infiniteStateValue beta gamma alpha halpha0 halpha1 hwin
          (SiteCylinderPresentation.unitVector i +ᵥ P) =
        infiniteStateValue beta gamma alpha halpha0 halpha1 hwin P := by
    intro i P
    induction P using Quotient.inductionOn with
    | _ P =>
        exact P.infiniteValue_translate_unit
          beta gamma alpha halpha0 halpha1 hwin i
  have hsingle : ∀ (i : Fin 2) (k : ℤ) (P : LocalCylinderAlgebra),
      infiniteStateValue beta gamma alpha halpha0 halpha1 hwin
          ((Pi.single i k : IsingSite) +ᵥ P) =
        infiniteStateValue beta gamma alpha halpha0 halpha1 hwin P := by
    intro i k
    cases k with
    | ofNat k =>
        induction k with
        | zero => intro P; simp
        | succ k ih =>
            intro P
            have hv : Pi.single i (Int.ofNat (k + 1)) =
                SiteCylinderPresentation.unitVector i +
                  Pi.single i (Int.ofNat k) := by
              funext j
              by_cases hji : j = i
              · subst j
                simp [SiteCylinderPresentation.unitVector]
                omega
              · simp [SiteCylinderPresentation.unitVector, hji]
            rw [hv, LocalCylinderAlgebra.add_vadd, hunit, ih]
    | negSucc k =>
        induction k with
        | zero =>
            intro P
            have hp := hunit i ((-SiteCylinderPresentation.unitVector i) +ᵥ P)
            have hv : (Pi.single i (Int.negSucc 0) : IsingSite) =
                -SiteCylinderPresentation.unitVector i := by
              funext j
              by_cases hji : j = i
              · subst j; simp [SiteCylinderPresentation.unitVector]
              · simp [SiteCylinderPresentation.unitVector, hji]
            rw [hv]
            rw [← LocalCylinderAlgebra.add_vadd] at hp
            simp at hp
            exact hp.symm
        | succ k ih =>
            intro P
            have hv : Pi.single i (Int.negSucc (k + 1)) =
                -SiteCylinderPresentation.unitVector i +
                  Pi.single i (Int.negSucc k) := by
              funext j
              by_cases hji : j = i
              · subst j
                simp [SiteCylinderPresentation.unitVector]
                omega
              · simp [SiteCylinderPresentation.unitVector, hji]
            rw [hv, LocalCylinderAlgebra.add_vadd]
            have hp := hunit i
              ((-SiteCylinderPresentation.unitVector i) +ᵥ
                ((Pi.single i (Int.negSucc k) : IsingSite) +ᵥ P))
            have hinv :
                SiteCylinderPresentation.unitVector i +ᵥ
                    ((-SiteCylinderPresentation.unitVector i) +ᵥ
                      ((Pi.single i (Int.negSucc k) : IsingSite) +ᵥ P)) =
                  (Pi.single i (Int.negSucc k) : IsingSite) +ᵥ P := by
              rw [← LocalCylinderAlgebra.add_vadd]
              simp
            rw [hinv] at hp
            exact hp.symm.trans (ih P)
  have hfin : ∀ S : Finset (Fin 2),
      infiniteStateValue beta gamma alpha halpha0 halpha1 hwin
          ((∑ i ∈ S, Pi.single i (z i)) +ᵥ O) =
        infiniteStateValue beta gamma alpha halpha0 halpha1 hwin O := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        rw [Finset.sum_insert hi, LocalCylinderAlgebra.add_vadd, hsingle, ih]
  simpa [Finset.univ_sum_single z] using hfin (Finset.univ : Finset (Fin 2))

/-- Positive normalized real-linear state on the integer site-cylinder
algebra, invariant under the genuine `Z^2` action. -/
structure TranslationInvariantSiteCylinderState where
  value : LocalCylinderAlgebra → ℝ
  map_add : ∀ O P, value (O + P) = value O + value P
  map_smul : ∀ c O, value (c • O) = c * value O
  map_one : value 1 = 1
  nonneg : ∀ O, (∀ sigma, 0 ≤ O.realizeGlobal sigma) → 0 ≤ value O
  vadd_invariant : ∀ (z : IsingSite) O, value (z +ᵥ O) = value O

instance : CoeFun TranslationInvariantSiteCylinderState
    (fun _ => LocalCylinderAlgebra → ℝ) :=
  ⟨TranslationInvariantSiteCylinderState.value⟩

/-- **The infinite-volume, positive, normalized, fully `Z^2`-covariant
Dobrushin state on the algebraic direct limit of site cylinders.** -/
noncomputable def infiniteTranslationInvariantSiteCylinderState
    (beta gamma alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha) :
    TranslationInvariantSiteCylinderState where
  value := infiniteStateValue beta gamma alpha halpha0 halpha1 hwin
  map_add := infiniteStateValue_add beta gamma alpha halpha0 halpha1 hwin
  map_smul := infiniteStateValue_smul beta gamma alpha halpha0 halpha1 hwin
  map_one := infiniteStateValue_one beta gamma alpha halpha0 halpha1 hwin
  nonneg := infiniteStateValue_nonneg beta gamma alpha halpha0 halpha1 hwin
  vadd_invariant := infiniteStateValue_vadd beta gamma alpha halpha0 halpha1 hwin

end LocalCylinderAlgebra
end Dobrushin
end YangMills.OS
