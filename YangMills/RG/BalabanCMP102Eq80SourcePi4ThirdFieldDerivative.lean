/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivativeBound

/-!
# Third physical-field derivatives of equation-(80) domain jets

The cubic radial residual needs one derivative beyond the physical Hessian.
This file extracts the final three physical-field variables from the literal
joint equation-(80) jet.  It does not assume a bound for a completed domain
activity or for an already assembled third derivative.

The quantitative endpoint retains the exact product of the propagator
direction norms.  Thus the next source-facing layer can use the order-four
joint potential jet and the already constructed physical domain matrix.
-/

namespace YangMills.RG

noncomputable section

section MixedJets

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The third physical-field derivative of a partial propagator jet, obtained
by currying the final three variables of the literal joint iterated
derivative and restricting all three to the physical-field factor. -/
noncomputable def cmp102PartialPropagatorJetThirdFieldDerivative
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) : E [×3]→L[ℝ] ℝ :=
  let P := H × E
  let incl : E →L[ℝ] P :=
    (0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)
  let raw : P →L[ℝ] P →L[ℝ] P →L[ℝ] ℝ :=
    ((continuousMultilinearCurryRightEquiv' ℝ n P
        (P →L[ℝ] P →L[ℝ] ℝ))
      ((continuousMultilinearCurryRightEquiv' ℝ (n + 1) P
          (P →L[ℝ] ℝ))
        ((continuousMultilinearCurryRightEquiv' ℝ (n + 2) P ℝ)
          (iteratedFDeriv ℝ (n + 3) F (h, x)))))
      (fun i => (v i, 0))
  let rawOne : P [×1]→L[ℝ] (P →L[ℝ] P →L[ℝ] ℝ) :=
    (continuousMultilinearCurryFin1 ℝ P
      (P →L[ℝ] P →L[ℝ] ℝ)).symm raw
  let rawTwo : P [×2]→L[ℝ] (P →L[ℝ] ℝ) :=
    (continuousMultilinearCurryRightEquiv' ℝ 1 P
      (P →L[ℝ] ℝ)).symm rawOne
  let rawThree : P [×3]→L[ℝ] ℝ :=
    (continuousMultilinearCurryRightEquiv' ℝ 2 P ℝ).symm rawTwo
  let restricted : E [×3]→L[ℝ] ℝ :=
    rawThree.compContinuousLinearMap fun _ => incl
  restricted

theorem cmp102PartialPropagatorJetThirdFieldDerivative_apply
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x a b c : E) :
    cmp102PartialPropagatorJetThirdFieldDerivative F n h v x ![a, b, c] =
      iteratedFDeriv ℝ (n + 3) F (h, x)
        (Fin.snoc
          (Fin.snoc
            (Fin.snoc (fun i => (v i, 0)) (0, a))
          (0, b))
          (0, c)) := by
  simp [cmp102PartialPropagatorJetThirdFieldDerivative]
  congr 1

/-- Extracting the final three physical-field variables costs exactly the
product of the propagator-direction norms.  There is no factorial or
ambient-dimension loss. -/
theorem norm_cmp102PartialPropagatorJetThirdFieldDerivative_le
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) :
    ‖cmp102PartialPropagatorJetThirdFieldDerivative F n h v x‖ ≤
      ‖iteratedFDeriv ℝ (n + 3) F (h, x)‖ * ∏ i, ‖v i‖ := by
  let C :=
    ‖iteratedFDeriv ℝ (n + 3) F (h, x)‖ * ∏ i, ‖v i‖
  have hC : 0 ≤ C :=
    mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro w
  let a := w 0
  let b := w 1
  let c := w 2
  have hw : w = ![a, b, c] := by
    funext i
    fin_cases i <;> rfl
  rw [hw, cmp102PartialPropagatorJetThirdFieldDerivative_apply]
  let directions : Fin (n + 3) → H × E :=
    Fin.snoc (Fin.snoc (Fin.snoc (fun i => (v i, 0)) (0, a))
      (0, b)) (0, c)
  have hprod :
      ∏ i, ‖directions i‖ =
        (∏ i, ‖v i‖) * ‖a‖ * ‖b‖ * ‖c‖ := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc,
      Fin.prod_univ_castSucc]
    simp [directions]
  calc
    ‖iteratedFDeriv ℝ (n + 3) F (h, x) directions‖ ≤
        ‖iteratedFDeriv ℝ (n + 3) F (h, x)‖ *
          ∏ i, ‖directions i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = C * ∏ i, ‖![a, b, c] i‖ := by
      have hthree :
          ∏ i : Fin 3, ‖![a, b, c] i‖ =
            ‖a‖ * ‖b‖ * ‖c‖ := by
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ,
          Fin.prod_univ_succ]
        simp
        ring
      rw [hprod, hthree]
      dsimp [C]
      ring

/-- Restricting a smooth joint map between normed spaces to a fixed
first-coordinate slice cannot increase an iterated-derivative norm. -/
theorem norm_iteratedFDeriv_fixedFirstSlice_normed_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Φ : H × E → G) (hΦ : ContDiff ℝ ⊤ Φ)
    (n : ℕ) (h : H) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => Φ (h, y)) x‖ ≤
      ‖iteratedFDeriv ℝ n Φ (h, x)‖ := by
  let e : E →L[ℝ] H × E := ContinuousLinearMap.inr ℝ H E
  let Φshift : H × E → G := fun p => Φ (p + (h, 0))
  have hshift : ContDiff ℝ ⊤ Φshift :=
    hΦ.comp (contDiff_id.add contDiff_const)
  have hfun : (fun y : E => Φ (h, y)) = Φshift ∘ e := by
    funext y
    simp [Φshift, e]
  rw [hfun, e.iteratedFDeriv_comp_right hshift x le_top]
  rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Φ)
    n (h, 0) (e x)]
  calc
    ‖(iteratedFDeriv ℝ n Φ (e x + (h, 0))).compContinuousLinearMap
        (fun _ => e)‖ ≤
        ‖iteratedFDeriv ℝ n Φ (e x + (h, 0))‖ *
          ∏ _ : Fin n, ‖e‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n Φ (e x + (h, 0))‖ * 1 := by
      gcongr
      exact Finset.prod_le_one
        (fun _ _ => norm_nonneg e)
        (fun _ _ => by
          simpa [e] using
            (ContinuousLinearMap.norm_inr_le_one ℝ H E))
    _ = ‖iteratedFDeriv ℝ n Φ (h, x)‖ := by
      simp [e]

/-- The actual third iterated derivative of a one-direction partial
propagator jet is bounded by the literal joint order-four jet times the
exact propagator-direction norm.  Equation (80) uses precisely this
one-direction specialization. -/
theorem norm_iteratedFDeriv_three_cmp102PartialPropagatorJet_one_le
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (h v : H) (x : E) :
    ‖iteratedFDeriv ℝ 3
        (cmp102PartialPropagatorJet F 1 h (fun _ => v)) x‖ ≤
      ‖iteratedFDeriv ℝ 4 F (h, x)‖ * ‖v‖ := by
  let direction : H × E := (v, 0)
  have hderiv : ContDiff ℝ ⊤ (fderiv ℝ F) :=
    hF.fderiv_right (by simp)
  have happly :
      ContDiff ℝ ⊤ (fun p : H × E => fderiv ℝ F p direction) :=
    hderiv.clm_apply contDiff_const
  have hfun :
      cmp102PartialPropagatorJet F 1 h (fun _ => v) =
        fun y : E => fderiv ℝ F (h, y) direction := by
    funext y
    simp [cmp102PartialPropagatorJet, direction]
  rw [hfun]
  have hslice :
      ‖iteratedFDeriv ℝ 3
          (fun y : E => fderiv ℝ F (h, y) direction) x‖ ≤
        ‖iteratedFDeriv ℝ 3
          (fun p : H × E => fderiv ℝ F p direction) (h, x)‖ :=
    norm_iteratedFDeriv_fixedFirstSlice_normed_le
      (fun p : H × E => fderiv ℝ F p direction)
      happly 3 h x
  have heval :
      ‖iteratedFDeriv ℝ 3
          (fun p : H × E => fderiv ℝ F p direction) (h, x)‖ ≤
        ‖direction‖ *
          ‖iteratedFDeriv ℝ 3 (fderiv ℝ F) (h, x)‖ :=
    norm_iteratedFDeriv_clm_apply_const
      hderiv.contDiffAt (by simp)
  have htotal := hslice.trans heval
  rw [norm_iteratedFDeriv_fderiv] at htotal
  simpa [direction, mul_comm] using htotal

end MixedJets

end

end YangMills.RG
