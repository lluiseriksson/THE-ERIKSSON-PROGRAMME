/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80JointSourceTermJetBound

/-!
# Quantitative joint-jet bound for the equation-(80) transport term

The second literal term in CMP102 equation (80) is

`-⟪A', Δπ (H (D A'))⟫`.

This file bounds its complete joint jet by applying the bilinear Leibniz
estimate first to the outer inner product and then to the joint evaluation
`(H, A') ↦ H (D A')`.  The fixed operator `Δπ` contributes exactly its
operator norm.  Both binomial sums remain visible, so the statement does not
hide the source derivatives of `D` inside a bound for the complete
equation-(80) potential.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev JointSpace := (F →L[ℝ] E) × E

/-- The literal transport jet is controlled by two explicit Leibniz sums:
the outer pairing with `A'`, and the inner joint evaluation `H (D A')`. -/
theorem norm_iteratedFDeriv_cmp102Eq80JointTransportTerm_le
    (D : E → F) (Δπ : E →L[ℝ] E) (hD : ContDiff ℝ ⊤ D)
    (n : ℕ) (p : JointSpace (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ n (cmp102Eq80JointTransportTerm D Δπ) p‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i
            (fun q : JointSpace (E := E) (F := F) => q.2) p‖ *
          (‖Δπ‖ *
            ∑ j ∈ Finset.range (n - i + 1),
              ((n - i).choose j : ℝ) *
                ‖iteratedFDeriv ℝ j
                  (fun q : JointSpace (E := E) (F := F) => q.1) p‖ *
                ‖iteratedFDeriv ℝ (n - i - j)
                  (fun q : JointSpace (E := E) (F := F) => D q.2) p‖) := by
  let HD : JointSpace (E := E) (F := F) → E :=
    fun q => q.1 (D q.2)
  have hHD : ContDiff ℝ ⊤ HD :=
    contDiff_fst.clm_apply (hD.comp contDiff_snd)
  have hΔHD : ContDiff ℝ ⊤ (fun q => Δπ (HD q)) :=
    Δπ.contDiff.comp hHD
  let pairing : JointSpace (E := E) (F := F) → ℝ :=
    fun q => (innerSL ℝ) q.2 (Δπ (HD q))
  have htransport :
      cmp102Eq80JointTransportTerm D Δπ =
        -pairing := by
    funext q
    rfl
  rw [htransport, iteratedFDeriv_neg_apply]
  suffices
      ‖iteratedFDeriv ℝ n pairing p‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i
              (fun q : JointSpace (E := E) (F := F) => q.2) p‖ *
            (‖Δπ‖ *
              ∑ j ∈ Finset.range (n - i + 1),
                ((n - i).choose j : ℝ) *
                  ‖iteratedFDeriv ℝ j
                    (fun q : JointSpace (E := E) (F := F) => q.1) p‖ *
                  ‖iteratedFDeriv ℝ (n - i - j)
                    (fun q : JointSpace (E := E) (F := F) => D q.2) p‖) by
    simpa only [ContinuousMultilinearMap.opNorm_neg] using this
  change
    ‖iteratedFDeriv ℝ n
        (fun q => (innerSL ℝ) q.2 (Δπ (HD q))) p‖ ≤ _
  apply
    ((innerSL ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
      contDiff_snd hΔHD p le_top (norm_innerSL_le ℝ (E := E))).trans
  gcongr with i hi
  have hcomp :
      ‖iteratedFDeriv ℝ (n - i) (fun q => Δπ (HD q)) p‖ ≤
        ‖Δπ‖ * ‖iteratedFDeriv ℝ (n - i) HD p‖ :=
    Δπ.norm_iteratedFDeriv_comp_left hHD.contDiffAt le_top
  calc
    ‖iteratedFDeriv ℝ (n - i) (fun q => Δπ (HD q)) p‖ ≤
        ‖Δπ‖ * ‖iteratedFDeriv ℝ (n - i) HD p‖ := hcomp
    _ ≤
        ‖Δπ‖ *
          ∑ j ∈ Finset.range (n - i + 1),
            ((n - i).choose j : ℝ) *
              ‖iteratedFDeriv ℝ j
                (fun q : JointSpace (E := E) (F := F) => q.1) p‖ *
              ‖iteratedFDeriv ℝ (n - i - j)
                (fun q : JointSpace (E := E) (F := F) => D q.2) p‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg Δπ)
      simpa [HD] using
        (norm_iteratedFDeriv_clm_apply
          (contDiff_fst :
            ContDiff ℝ ⊤
              (fun q : JointSpace (E := E) (F := F) => q.1))
          (hD.comp contDiff_snd) p le_top)

end

end YangMills.RG
