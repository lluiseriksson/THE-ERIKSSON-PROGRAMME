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

end MixedJets

end

end YangMills.RG
