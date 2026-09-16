/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.QuantitativeFixedPointCoefficientJets
import YangMills.RG.LocalQuantitativeComposition

/-!
# Local coefficient jets of the derived fixed-point map

The physical CMP102 fixed-point map is analytic on local chart
neighborhoods rather than globally smooth on the entire ambient space.
This file localizes the quantitative coefficient and bilinear estimates:
`T` need only be `C³` at the physical graph point `(x,g(x))`.

The resulting bound is numerically identical to the global algebraic
estimate.  No global smoothness certificate, coefficient-jet bound, or
third derivative of `g` is assumed.
-/

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev DerivativePoint :=
  E × (E →L[ℝ] F)

/-- Local first-jet bound for the literal coefficient. -/
theorem norm_iteratedFDeriv_one_fixedPointDerivativeCoefficient_le_at
    (T : E × F → F) (g : E → F)
    (p : DerivativePoint (E := E) (F := F)) {J R : ℝ}
    (hT : ContDiffAt ℝ 3 T (fixedPointCoefficientInput g p))
    (hg : ContDiff ℝ 2 g)
    (hJ : ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i T (fixedPointCoefficientInput g p)‖ ≤ J)
    (hR :
      ‖iteratedFDeriv ℝ 1 (fixedPointCoefficientInput g) p‖ ≤ R) :
    ‖iteratedFDeriv ℝ 1
      (fixedPointDerivativeCoefficient T g) p‖ ≤ J * R := by
  have houter : ContDiffAt ℝ 1 (fderiv ℝ T)
      (fixedPointCoefficientInput g p) :=
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
    norm_iteratedFDeriv_comp_le_at houter hinput hC
      (by
        intro i hi hin
        have : i = 1 := by omega
        subst i
        simpa using hR)
  simpa [fixedPointDerivativeCoefficient, fixedPointCoefficientInput,
    Function.comp_def] using hmain

/-- Local second-jet bound for the literal coefficient. -/
theorem norm_iteratedFDeriv_two_fixedPointDerivativeCoefficient_le_at
    (T : E × F → F) (g : E → F)
    (p : DerivativePoint (E := E) (F := F)) {J R : ℝ}
    (hT : ContDiffAt ℝ 3 T (fixedPointCoefficientInput g p))
    (hg : ContDiff ℝ 2 g)
    (hJ : ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i T (fixedPointCoefficientInput g p)‖ ≤ J)
    (hR : ∀ i, 1 ≤ i → i ≤ 2 →
      ‖iteratedFDeriv ℝ i (fixedPointCoefficientInput g) p‖ ≤ R ^ i) :
    ‖iteratedFDeriv ℝ 2
      (fixedPointDerivativeCoefficient T g) p‖ ≤
        2 * J * R ^ 2 := by
  have houter : ContDiffAt ℝ 2 (fderiv ℝ T)
      (fixedPointCoefficientInput g p) :=
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
    norm_iteratedFDeriv_comp_le_at houter hinput hC hR
  calc
    ‖iteratedFDeriv ℝ 2
        (fixedPointDerivativeCoefficient T g) p‖
        ≤ (Nat.factorial 2 : ℝ) * J * R ^ 2 := by
          simpa [fixedPointDerivativeCoefficient,
            fixedPointCoefficientInput, Function.comp_def] using hmain
    _ = 2 * J * R ^ 2 := by norm_num

/-- Local second-jet bound for the literal derived map from already
generated coefficient-jet budgets. -/
theorem norm_iteratedFDeriv_two_fixedPointFirstDerivativeMap_le_at
    (T : E × F → F) (g : E → F)
    (p : DerivativePoint (E := E) (F := F))
    {L₁ C₁ C₂ : ℝ}
    (hA : ‖p.2‖ ≤ L₁)
    (hcoeff :
      ContDiffAt ℝ 2 (fixedPointDerivativeCoefficient T g) p)
    (hC₁ : ‖iteratedFDeriv ℝ 1
      (fixedPointDerivativeCoefficient T g) p‖ ≤ C₁)
    (hC₂ : ‖iteratedFDeriv ℝ 2
      (fixedPointDerivativeCoefficient T g) p‖ ≤ C₂) :
    ‖iteratedFDeriv ℝ 2
      (fixedPointFirstDerivativeMap T g) p‖ ≤
        2 * C₁ + C₂ * max 1 L₁ := by
  have hmap :
      fixedPointFirstDerivativeMap T g =
        fun y =>
          ContinuousLinearMap.compL ℝ E (E × F) F
            (fixedPointDerivativeCoefficient T g y)
            (fixedPointGraphFactor y) := by
    funext y
    exact fixedPointFirstDerivativeMap_eq_bilinear T g y
  rw [hmap]
  have hraw :=
    norm_iteratedFDeriv_two_bilinear_le_at
      (ContinuousLinearMap.compL ℝ E (E × F) F)
      hcoeff
      ((contDiff_fixedPointGraphFactor (E := E) (F := F)).of_le
        (by norm_num))
      (ContinuousLinearMap.norm_compL_le ℝ E (E × F) F)
  have hgraph0 :
      ‖iteratedFDeriv ℝ 0
        (fixedPointGraphFactor :
          DerivativePoint (E := E) (F := F) →
            (E →L[ℝ] E × F)) p‖ ≤ max 1 L₁ := by
    simpa only [norm_iteratedFDeriv_zero] using
      (norm_fixedPointGraphDerivative_le p.2).trans
        (max_le_max le_rfl hA)
  have hgraph1 :=
    norm_iteratedFDeriv_one_fixedPointGraphFactor_le p
  have hgraph2 :
      ‖iteratedFDeriv ℝ 2
        (fixedPointGraphFactor :
          DerivativePoint (E := E) (F := F) →
            (E →L[ℝ] E × F)) p‖ = 0 :=
    norm_iteratedFDeriv_two_fixedPointGraphFactor p
  have hC₁nonneg : 0 ≤ C₁ := by
    exact (norm_nonneg
      (iteratedFDeriv ℝ 1
        (fixedPointDerivativeCoefficient T g) p)).trans hC₁
  have hC₂nonneg : 0 ≤ C₂ := by
    exact (norm_nonneg
      (iteratedFDeriv ℝ 2
        (fixedPointDerivativeCoefficient T g) p)).trans hC₂
  calc
    ‖iteratedFDeriv ℝ 2
        (fun y =>
          ContinuousLinearMap.compL ℝ E (E × F) F
            (fixedPointDerivativeCoefficient T g y)
            (fixedPointGraphFactor y)) p‖
        ≤ 0 +
            2 * ‖iteratedFDeriv ℝ 1
              (fixedPointDerivativeCoefficient T g) p‖ *
              ‖iteratedFDeriv ℝ 1 fixedPointGraphFactor p‖ +
            ‖iteratedFDeriv ℝ 2
              (fixedPointDerivativeCoefficient T g) p‖ *
              ‖iteratedFDeriv ℝ 0 fixedPointGraphFactor p‖ := by
          simpa [hgraph2] using hraw
    _ ≤ 0 + 2 * C₁ * 1 + C₂ * max 1 L₁ := by
      gcongr
    _ = 2 * C₁ + C₂ * max 1 L₁ := by ring

/-- **Physical-ready local source-jet bound.**  The only smoothness
assumption on `T` is local at `(x,g(x))`. -/
theorem
    norm_iteratedFDeriv_two_fixedPointFirstDerivativeMap_le_of_jets_at
    (T : E × F → F) (g : E → F)
    (p : DerivativePoint (E := E) (F := F)) {J L₁ L₂ : ℝ}
    (hT : ContDiffAt ℝ 3 T (fixedPointCoefficientInput g p))
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
    norm_iteratedFDeriv_one_fixedPointDerivativeCoefficient_le_at
      T g p hT hg hJ hinput1
  have hR : ∀ i, 1 ≤ i → i ≤ 2 →
      ‖iteratedFDeriv ℝ i (fixedPointCoefficientInput g) p‖ ≤ R ^ i := by
    intro i hi hin
    have hcases : i = 1 ∨ i = 2 := by omega
    rcases hcases with rfl | rfl
    · simpa using hinput1
    · have hR1 : 1 ≤ R :=
        (le_max_left 1 L₁).trans
          (le_max_left (max 1 L₁) L₂)
      have hRpow : R ≤ R ^ 2 := by
        have hR0 : 0 ≤ R := zero_le_one.trans hR1
        nlinarith
      exact
        (norm_iteratedFDeriv_two_fixedPointCoefficientInput_le
          g hg p hsecond).trans ((le_max_right _ _).trans hRpow)
  have hC₂ :
      ‖iteratedFDeriv ℝ 2
        (fixedPointDerivativeCoefficient T g) p‖ ≤
          2 * J * R ^ 2 :=
    norm_iteratedFDeriv_two_fixedPointDerivativeCoefficient_le_at
      T g p hT hg hJ hR
  have hcoeff :
      ContDiffAt ℝ 2 (fixedPointDerivativeCoefficient T g) p := by
    exact
      (hT.fderiv_right
        (m := (2 : WithTop ℕ∞)) (by norm_num)).comp p
          (contDiff_fst.prodMk
            (hg.comp contDiff_fst)).contDiffAt
  exact
    norm_iteratedFDeriv_two_fixedPointFirstDerivativeMap_le_at
      T g p hA hcoeff hC₁ hC₂

end

end YangMills.RG
