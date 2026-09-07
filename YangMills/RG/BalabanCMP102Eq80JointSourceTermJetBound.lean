/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80JointPotentialJetDecomposition

/-!
# Quantitative joint-jet bound for the equation-(80) source term

The first literal term in CMP102 equation (80) is

`-⟪H (D₃ A), J⟫`.

This file bounds its complete joint jet directly from the derivatives of the
physical source map `D₃`.  The proof first applies the fixed continuous
functional `-innerSL ℝ J`, whose operator norm is exactly `‖J‖`, and then
uses the binomial derivative bound for the joint evaluation
`(H, A) ↦ H (D₃ A)`.

No bound on the full equation-(80) jet and no domain-level Hessian premise is
used.  The binomial coefficients are kept explicitly; no additional
factorial or ambient-dimension factor is introduced.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev JointSpace := (F →L[ℝ] E) × E

/-- The literal `D₃` source jet is controlled by the exact norm of `J` and
the binomial joint-evaluation majorant built from the derivatives of `D₃`. -/
theorem norm_iteratedFDeriv_cmp102Eq80JointSourceTerm_le
    (D₃ : E → F) (J : E) (hD₃ : ContDiff ℝ ⊤ D₃)
    (n : ℕ) (p : JointSpace (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ n (cmp102Eq80JointSourceTerm D₃ J) p‖ ≤
      ‖J‖ *
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i
              (fun q : JointSpace (E := E) (F := F) => q.1) p‖ *
            ‖iteratedFDeriv ℝ (n - i)
              (fun q : JointSpace (E := E) (F := F) => D₃ q.2) p‖ := by
  let HD₃ : JointSpace (E := E) (F := F) → E :=
    fun q => q.1 (D₃ q.2)
  have hHD₃ : ContDiff ℝ ⊤ HD₃ :=
    contDiff_fst.clm_apply (hD₃.comp contDiff_snd)
  have hsource :
      cmp102Eq80JointSourceTerm D₃ J =
        (-innerSL ℝ J) ∘ HD₃ := by
    funext q
    simp [cmp102Eq80JointSourceTerm, HD₃, real_inner_comm]
  rw [hsource]
  calc
    ‖iteratedFDeriv ℝ n ((-innerSL ℝ J) ∘ HD₃) p‖ ≤
        ‖-innerSL ℝ J‖ * ‖iteratedFDeriv ℝ n HD₃ p‖ :=
      (-innerSL ℝ J).norm_iteratedFDeriv_comp_left
        hHD₃.contDiffAt le_top
    _ = ‖J‖ * ‖iteratedFDeriv ℝ n HD₃ p‖ := by
      rw [norm_neg, innerSL_apply_norm]
    _ ≤
        ‖J‖ *
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i
                (fun q : JointSpace (E := E) (F := F) => q.1) p‖ *
              ‖iteratedFDeriv ℝ (n - i)
                (fun q : JointSpace (E := E) (F := F) => D₃ q.2) p‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg J)
      simpa [HD₃] using
        (norm_iteratedFDeriv_clm_apply
          (contDiff_fst :
            ContDiff ℝ ⊤
              (fun q : JointSpace (E := E) (F := F) => q.1))
          (hD₃.comp contDiff_snd) p le_top)

end

end YangMills.RG
