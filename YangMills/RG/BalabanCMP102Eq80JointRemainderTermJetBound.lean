/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80JointQuadraticTermJetBound

/-!
# Quantitative joint-jet bound for the equation-(80) remainder term

The fourth literal term in CMP102 equation (80) is

`V₀ (A' - H (D A'))`.

Unlike the first three terms, this is a nonlinear composition.  We first
bound the complete jet of its inner map by the coordinate jet plus the
explicit joint-evaluation majorant.  We then apply Mathlib's quantitative
Faà di Bruno bound.  The public hypotheses refer only to derivatives of
the source function `V₀` and to a scalar budget for the explicit inner-map
majorant; no bound for the complete equation-(80) potential is assumed.
-/

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev JointSpace := (F →L[ℝ] E) × E

/-- The literal inner map in the equation-(80) remainder. -/
noncomputable def cmp102Eq80JointRemainderInner
    (D : E → F) (p : JointSpace (E := E) (F := F)) : E :=
  p.2 - p.1 (D p.2)

/-- The inner-map jet is controlled by the coordinate jet plus the explicit
joint-evaluation majorant generated from `D`. -/
theorem norm_iteratedFDeriv_cmp102Eq80JointRemainderInner_le
    (D : E → F) (hD : ContDiff ℝ ⊤ D)
    (n : ℕ) (p : JointSpace (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ n (cmp102Eq80JointRemainderInner D) p‖ ≤
      ‖iteratedFDeriv ℝ n
        (fun q : JointSpace (E := E) (F := F) => q.2) p‖ +
      cmp102Eq80JointEvaluationJetMajorant D n p := by
  let HD : JointSpace (E := E) (F := F) → E :=
    fun q => q.1 (D q.2)
  have hHD : ContDiff ℝ ⊤ HD :=
    contDiff_fst.clm_apply (hD.comp contDiff_snd)
  have hinner :
      cmp102Eq80JointRemainderInner D =
        (fun q : JointSpace (E := E) (F := F) => q.2) - HD := by
    funext q
    rfl
  rw [hinner,
    iteratedFDeriv_sub_apply
      (contDiff_snd.contDiffAt.of_le le_top)
      (hHD.contDiffAt.of_le le_top)]
  calc
    ‖iteratedFDeriv ℝ n
          (fun q : JointSpace (E := E) (F := F) => q.2) p -
        iteratedFDeriv ℝ n HD p‖ ≤
        ‖iteratedFDeriv ℝ n
          (fun q : JointSpace (E := E) (F := F) => q.2) p‖ +
        ‖iteratedFDeriv ℝ n HD p‖ :=
      calc
        ‖iteratedFDeriv ℝ n
              (fun q : JointSpace (E := E) (F := F) => q.2) p -
            iteratedFDeriv ℝ n HD p‖ =
            ‖iteratedFDeriv ℝ n
                (fun q : JointSpace (E := E) (F := F) => q.2) p +
              -iteratedFDeriv ℝ n HD p‖ := by
              rw [sub_eq_add_neg]
        _ ≤
            ‖iteratedFDeriv ℝ n
              (fun q : JointSpace (E := E) (F := F) => q.2) p‖ +
            ‖-iteratedFDeriv ℝ n HD p‖ :=
          ContinuousMultilinearMap.opNorm_add_le _ _
        _ =
            ‖iteratedFDeriv ℝ n
              (fun q : JointSpace (E := E) (F := F) => q.2) p‖ +
            ‖iteratedFDeriv ℝ n HD p‖ := by
          rw [ContinuousMultilinearMap.opNorm_neg]
    _ ≤
        ‖iteratedFDeriv ℝ n
          (fun q : JointSpace (E := E) (F := F) => q.2) p‖ +
        cmp102Eq80JointEvaluationJetMajorant D n p := by
      exact add_le_add le_rfl
        (norm_iteratedFDeriv_cmp102Eq80JointEvaluation_le D hD n p)

/-- Quantitative Faà di Bruno bound for the literal equation-(80) remainder.

`C` bounds the first `n` jets of the source function `V₀` at the physical
inner point.  `R` bounds the explicit inner-map jet by powers `R^i`; the
left side of `hR` displays exactly the coordinate contribution and the
source-generated joint-evaluation majorant. -/
theorem norm_iteratedFDeriv_cmp102Eq80JointRemainderTerm_le
    (D : E → F) (V₀ : E → ℝ)
    (hD : ContDiff ℝ ⊤ D) (hV₀ : ContDiff ℝ ⊤ V₀)
    (n : ℕ) (p : JointSpace (E := E) (F := F))
    (C R : ℝ)
    (hC : ∀ i, i ≤ n →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner D p)‖ ≤ C)
    (hR : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i
        (fun q : JointSpace (E := E) (F := F) => q.2) p‖ +
        cmp102Eq80JointEvaluationJetMajorant D i p ≤ R ^ i) :
    ‖iteratedFDeriv ℝ n (cmp102Eq80JointRemainderTerm D V₀) p‖ ≤
      (n.factorial : ℝ) * C * R ^ n := by
  have hinner : ContDiff ℝ ⊤ (cmp102Eq80JointRemainderInner D) := by
    unfold cmp102Eq80JointRemainderInner
    exact contDiff_snd.sub <|
      contDiff_fst.clm_apply (hD.comp contDiff_snd)
  have hremainder :
      cmp102Eq80JointRemainderTerm D V₀ =
        V₀ ∘ cmp102Eq80JointRemainderInner D := by
    funext q
    rfl
  rw [hremainder]
  apply norm_iteratedFDeriv_comp_le hV₀ hinner le_top p hC
  intro i hi hin
  exact
    (norm_iteratedFDeriv_cmp102Eq80JointRemainderInner_le
      D hD i p).trans (hR i hi hin)

end

end YangMills.RG
