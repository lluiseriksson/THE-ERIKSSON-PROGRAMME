/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.QuantitativeFixedPointDerivedMapSecondJet

/-!
# Coefficient jets of the derived fixed-point map

The coefficient in the derived fixed-point map is the literal composition

`(x,A) ↦ DT(x,g(x))`.

This file derives its first and second jets from jets of `T` through order
three and jets of `g` through order two.  The input map ignores `A`; its
first jet costs `max(1,L₁)` and its second jet costs `L₂`.  A quantitative
Faà di Bruno estimate then gives an explicit second-jet bound for

`(x,A) ↦ DT(x,g(x)) ∘ (id,A)`.

No coefficient-jet bound and no derivative of `g` of order three is assumed.
The common source budget `J` below bounds the literal jets of `T` of orders
one through three at `(x,g(x))`.
-/

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev DerivativePoint :=
  E × (E →L[ℝ] F)

/-- The graph input of the coefficient `DT(x,g(x))`.  It deliberately
ignores the linear-map coordinate. -/
noncomputable def fixedPointCoefficientInput
    (g : E → F) :
    DerivativePoint (E := E) (F := F) → E × F :=
  fun p => (p.1, g p.1)

/-- Composing the first jet of `g` with the first projection does not
increase its norm. -/
theorem norm_iteratedFDeriv_one_comp_fixedPointCoefficientFst_le
    (g : E → F) (hg : ContDiff ℝ 2 g)
    (p : DerivativePoint (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ 1
        (fun q : DerivativePoint (E := E) (F := F) => g q.1) p‖ ≤
      ‖iteratedFDeriv ℝ 1 g p.1‖ := by
  let fstCLM : DerivativePoint (E := E) (F := F) →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E (E →L[ℝ] F)
  have hfun :
      (fun q : DerivativePoint (E := E) (F := F) => g q.1) =
        g ∘ fstCLM := by
    rfl
  rw [hfun, fstCLM.iteratedFDeriv_comp_right hg p (by norm_num)]
  calc
    ‖(iteratedFDeriv ℝ 1 g (fstCLM p)).compContinuousLinearMap
        (fun _ => fstCLM)‖ ≤
        ‖iteratedFDeriv ℝ 1 g (fstCLM p)‖ *
          ∏ _ : Fin 1, ‖fstCLM‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ 1 g (fstCLM p)‖ * 1 := by
      gcongr
      exact Finset.prod_le_one
        (fun _ _ => norm_nonneg fstCLM)
        (fun _ _ => ContinuousLinearMap.norm_fst_le _ _ _)
    _ = ‖iteratedFDeriv ℝ 1 g p.1‖ := by
      simp [fstCLM]

/-- Composing the second jet of `g` with the first projection does not
increase its norm. -/
theorem norm_iteratedFDeriv_two_comp_fixedPointCoefficientFst_le
    (g : E → F) (hg : ContDiff ℝ 2 g)
    (p : DerivativePoint (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ 2
        (fun q : DerivativePoint (E := E) (F := F) => g q.1) p‖ ≤
      ‖iteratedFDeriv ℝ 2 g p.1‖ := by
  let fstCLM : DerivativePoint (E := E) (F := F) →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E (E →L[ℝ] F)
  have hfun :
      (fun q : DerivativePoint (E := E) (F := F) => g q.1) =
        g ∘ fstCLM := by
    rfl
  rw [hfun, fstCLM.iteratedFDeriv_comp_right hg p (by norm_num)]
  calc
    ‖(iteratedFDeriv ℝ 2 g (fstCLM p)).compContinuousLinearMap
        (fun _ => fstCLM)‖ ≤
        ‖iteratedFDeriv ℝ 2 g (fstCLM p)‖ *
          ∏ _ : Fin 2, ‖fstCLM‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ 2 g (fstCLM p)‖ * 1 := by
      gcongr
      exact Finset.prod_le_one
        (fun _ _ => norm_nonneg fstCLM)
        (fun _ _ => ContinuousLinearMap.norm_fst_le _ _ _)
    _ = ‖iteratedFDeriv ℝ 2 g p.1‖ := by
      simp [fstCLM]

/-- The first jet of `(x,A) ↦ (x,g(x))` costs `max(1,L₁)`. -/
theorem norm_iteratedFDeriv_one_fixedPointCoefficientInput_le
    (g : E → F) (hg : ContDiff ℝ 2 g)
    (p : DerivativePoint (E := E) (F := F)) {L₁ : ℝ}
    (hfirst : ‖iteratedFDeriv ℝ 1 g p.1‖ ≤ L₁) :
    ‖iteratedFDeriv ℝ 1 (fixedPointCoefficientInput g) p‖ ≤
      max 1 L₁ := by
  change
    ‖iteratedFDeriv ℝ 1
      (fun q : DerivativePoint (E := E) (F := F) =>
        (q.1, g q.1)) p‖ ≤ max 1 L₁
  rw [iteratedFDeriv_prodMk
    (f := fun q : DerivativePoint (E := E) (F := F) => q.1)
    (g := fun q : DerivativePoint (E := E) (F := F) => g q.1)
    contDiff_fst.contDiffAt
    ((hg.comp contDiff_fst).contDiffAt) (by norm_num)]
  rw [ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · have hfst :
        ‖iteratedFDeriv ℝ 1
          (fun q : DerivativePoint (E := E) (F := F) => q.1) p‖ ≤ 1 := by
      simpa [norm_iteratedFDeriv_one, fderiv_fst] using
        (ContinuousLinearMap.norm_fst_le ℝ E (E →L[ℝ] F))
    exact hfst.trans (le_max_left _ _)
  · exact
      ((norm_iteratedFDeriv_one_comp_fixedPointCoefficientFst_le
        g hg p).trans hfirst).trans (le_max_right _ _)

/-- The second jet of `(x,A) ↦ (x,g(x))` costs exactly the supplied
second-jet budget for `g`; the first coordinate is affine. -/
theorem norm_iteratedFDeriv_two_fixedPointCoefficientInput_le
    (g : E → F) (hg : ContDiff ℝ 2 g)
    (p : DerivativePoint (E := E) (F := F)) {L₂ : ℝ}
    (hsecond : ‖iteratedFDeriv ℝ 2 g p.1‖ ≤ L₂) :
    ‖iteratedFDeriv ℝ 2 (fixedPointCoefficientInput g) p‖ ≤ L₂ := by
  change
    ‖iteratedFDeriv ℝ 2
      (fun q : DerivativePoint (E := E) (F := F) =>
        (q.1, g q.1)) p‖ ≤ L₂
  rw [iteratedFDeriv_prodMk
    (f := fun q : DerivativePoint (E := E) (F := F) => q.1)
    (g := fun q : DerivativePoint (E := E) (F := F) => g q.1)
    contDiff_fst.contDiffAt
    ((hg.comp contDiff_fst).contDiffAt) (by norm_num)]
  rw [ContinuousMultilinearMap.opNorm_prod]
  have hproj :
      iteratedFDeriv ℝ 2
        (fun q : DerivativePoint (E := E) (F := F) => q.1) p = 0 := by
    rw [show 2 = 1 + 1 by norm_num,
      iteratedFDeriv_succ_eq_comp_right]
    have hderiv :
        (fun y : DerivativePoint (E := E) (F := F) =>
          fderiv ℝ
            (fun q : DerivativePoint (E := E) (F := F) => q.1) y) =
          fun _ => ContinuousLinearMap.fst ℝ E (E →L[ℝ] F) := by
      funext y
      exact fderiv_fst
    rw [hderiv]
    have hzero :
        iteratedFDeriv ℝ 1
          (fun _ : DerivativePoint (E := E) (F := F) =>
            ContinuousLinearMap.fst ℝ E (E →L[ℝ] F)) = 0 :=
      iteratedFDeriv_const_of_ne one_ne_zero _
    rw [hzero]
    simp only [Function.comp_apply, Pi.zero_apply]
    have hcurryZero :
        (continuousMultilinearCurryRightEquiv'
          ℝ 1 (DerivativePoint (E := E) (F := F)) E).symm 0 = 0 :=
      (continuousMultilinearCurryRightEquiv'
        ℝ 1 (DerivativePoint (E := E) (F := F)) E).symm.map_zero
    rw [hcurryZero]
  rw [hproj, norm_zero, max_eq_right (norm_nonneg _)]
  exact
    (norm_iteratedFDeriv_two_comp_fixedPointCoefficientFst_le
      g hg p).trans hsecond

/-- First-jet bound for the literal coefficient from joint jets of `T`
and the first jet of its graph input. -/
theorem norm_iteratedFDeriv_one_fixedPointDerivativeCoefficient_le
    (T : E × F → F) (g : E → F)
    (p : DerivativePoint (E := E) (F := F)) {J R : ℝ}
    (hT : ContDiff ℝ 3 T)
    (hg : ContDiff ℝ 2 g)
    (hJ : ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i T (fixedPointCoefficientInput g p)‖ ≤ J)
    (hR :
      ‖iteratedFDeriv ℝ 1 (fixedPointCoefficientInput g) p‖ ≤ R) :
    ‖iteratedFDeriv ℝ 1
      (fixedPointDerivativeCoefficient T g) p‖ ≤ J * R := by
  have houter : ContDiff ℝ 1 (fderiv ℝ T) :=
    hT.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)
  have hinput : ContDiff ℝ 1 (fixedPointCoefficientInput g) := by
    exact contDiff_fst.prodMk
      ((hg.of_le (by norm_num)).comp contDiff_fst)
  have hC : ∀ i, i ≤ 1 →
      ‖iteratedFDeriv ℝ i (fderiv ℝ T)
        (fixedPointCoefficientInput g p)‖ ≤ J := by
    intro i hi
    rw [norm_iteratedFDeriv_fderiv]
    exact hJ (i + 1) (by omega) (by omega)
  have hmain :=
    norm_iteratedFDeriv_comp_le houter hinput
      (n := 1) (N := (1 : WithTop ℕ∞)) le_rfl p hC
      (by
        intro i hi hin
        have : i = 1 := by omega
        subst i
        simpa using hR)
  simpa [fixedPointDerivativeCoefficient, fixedPointCoefficientInput,
    Function.comp_def] using hmain

/-- Second-jet bound for the literal coefficient from a common joint-jet
budget `J` and graph-input radius `R`. -/
theorem norm_iteratedFDeriv_two_fixedPointDerivativeCoefficient_le
    (T : E × F → F) (g : E → F)
    (p : DerivativePoint (E := E) (F := F)) {J R : ℝ}
    (hT : ContDiff ℝ 3 T)
    (hg : ContDiff ℝ 2 g)
    (hJ : ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i T (fixedPointCoefficientInput g p)‖ ≤ J)
    (hR : ∀ i, 1 ≤ i → i ≤ 2 →
      ‖iteratedFDeriv ℝ i (fixedPointCoefficientInput g) p‖ ≤ R ^ i) :
    ‖iteratedFDeriv ℝ 2
      (fixedPointDerivativeCoefficient T g) p‖ ≤
        2 * J * R ^ 2 := by
  have houter : ContDiff ℝ 2 (fderiv ℝ T) :=
    hT.fderiv_right (m := (2 : WithTop ℕ∞)) (by norm_num)
  have hinput : ContDiff ℝ 2 (fixedPointCoefficientInput g) := by
    exact contDiff_fst.prodMk (hg.comp contDiff_fst)
  have hC : ∀ i, i ≤ 2 →
      ‖iteratedFDeriv ℝ i (fderiv ℝ T)
        (fixedPointCoefficientInput g p)‖ ≤ J := by
    intro i hi
    rw [norm_iteratedFDeriv_fderiv]
    exact hJ (i + 1) (by omega) (by omega)
  have hmain :=
    norm_iteratedFDeriv_comp_le houter hinput
      (n := 2) (N := (2 : WithTop ℕ∞)) le_rfl p hC hR
  calc
    ‖iteratedFDeriv ℝ 2
        (fixedPointDerivativeCoefficient T g) p‖
        ≤ (Nat.factorial 2 : ℝ) * J * R ^ 2 := by
          simpa [fixedPointDerivativeCoefficient,
            fixedPointCoefficientInput, Function.comp_def] using hmain
    _ = 2 * J * R ^ 2 := by norm_num

/-- The coefficient second jet with the graph-input radius generated
internally from `Dg` and `D²g`. -/
theorem
    norm_iteratedFDeriv_two_fixedPointDerivativeCoefficient_le_of_jets
    (T : E × F → F) (g : E → F)
    (p : DerivativePoint (E := E) (F := F)) {J L₁ L₂ : ℝ}
    (hT : ContDiff ℝ 3 T)
    (hg : ContDiff ℝ 2 g)
    (hJ : ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i T (fixedPointCoefficientInput g p)‖ ≤ J)
    (hfirst : ‖iteratedFDeriv ℝ 1 g p.1‖ ≤ L₁)
    (hsecond : ‖iteratedFDeriv ℝ 2 g p.1‖ ≤ L₂) :
    ‖iteratedFDeriv ℝ 2
      (fixedPointDerivativeCoefficient T g) p‖ ≤
        2 * J * (max (max 1 L₁) L₂) ^ 2 := by
  apply norm_iteratedFDeriv_two_fixedPointDerivativeCoefficient_le
      T g p hT hg hJ
  intro i hi hin
  have hcases : i = 1 ∨ i = 2 := by omega
  rcases hcases with rfl | rfl
  · simpa using
      (norm_iteratedFDeriv_one_fixedPointCoefficientInput_le
        g hg p hfirst).trans (le_max_left _ _)
  · have hR1 : 1 ≤ max (max 1 L₁) L₂ :=
      (le_max_left 1 L₁).trans
        (le_max_left (max 1 L₁) L₂)
    have hRpow :
        max (max 1 L₁) L₂ ≤
          (max (max 1 L₁) L₂) ^ 2 := by
      have hR0 : 0 ≤ max (max 1 L₁) L₂ := zero_le_one.trans hR1
      nlinarith
    exact
      (norm_iteratedFDeriv_two_fixedPointCoefficientInput_le
        g hg p hsecond).trans ((le_max_right _ _).trans hRpow)

/-- **Source-jet bound for the derived fixed-point map.**  All coefficient
budgets are generated from literal jets of `T` through order three and
jets of `g` through order two. -/
theorem norm_iteratedFDeriv_two_fixedPointFirstDerivativeMap_le_of_jets
    (T : E × F → F) (g : E → F)
    (p : DerivativePoint (E := E) (F := F)) {J L₁ L₂ : ℝ}
    (hT : ContDiff ℝ 3 T)
    (hg : ContDiff ℝ 2 g)
    (hJ : ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i T (fixedPointCoefficientInput g p)‖ ≤ J)
    (hA : ‖p.2‖ ≤ L₁)
    (hfirst : ‖iteratedFDeriv ℝ 1 g p.1‖ ≤ L₁)
    (hsecond : ‖iteratedFDeriv ℝ 2 g p.1‖ ≤ L₂) :
    ‖iteratedFDeriv ℝ 2
      (fixedPointFirstDerivativeMap T g) p‖ ≤
        2 * (J * max (max 1 L₁) L₂) +
          (2 * J * (max (max 1 L₁) L₂) ^ 2) *
            max 1 L₁ := by
  let R := max (max 1 L₁) L₂
  have hinput1 :
      ‖iteratedFDeriv ℝ 1 (fixedPointCoefficientInput g) p‖ ≤ R := by
    exact
      (norm_iteratedFDeriv_one_fixedPointCoefficientInput_le
        g hg p hfirst).trans (le_max_left _ _)
  have hC₁ :
      ‖iteratedFDeriv ℝ 1
        (fixedPointDerivativeCoefficient T g) p‖ ≤ J * R :=
    norm_iteratedFDeriv_one_fixedPointDerivativeCoefficient_le
      T g p hT hg hJ hinput1
  have hC₂ :
      ‖iteratedFDeriv ℝ 2
        (fixedPointDerivativeCoefficient T g) p‖ ≤
          2 * J * R ^ 2 :=
    norm_iteratedFDeriv_two_fixedPointDerivativeCoefficient_le_of_jets
      T g p hT hg hJ hfirst hsecond
  have hcoeff :
      ContDiff ℝ 2 (fixedPointDerivativeCoefficient T g) := by
    exact
      (hT.fderiv_right
        (m := (2 : WithTop ℕ∞)) (by norm_num)).comp
          (contDiff_fst.prodMk (hg.comp contDiff_fst))
  exact
    norm_iteratedFDeriv_two_fixedPointFirstDerivativeMap_le
      T g p hA hcoeff hC₁ hC₂

end

end YangMills.RG
