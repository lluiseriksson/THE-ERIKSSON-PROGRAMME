/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFFiberEntropy
import YangMills.RG.PolymerClusterWithHolesBridge

/-!
# Appendix F: local modified-metric summability adapters

This module is the finite local-summability adapter before the first
integrated `K#` estimate.  It restricts the already-proved rooted
modified-metric summability theorem to a finite raw family `Λ`, and converts
rooted local control into a target-contained local estimate by overcounting
through roots in the active skeleton of the target.

This is finite geometry and summation bookkeeping only.  It does not prove the
pointwise Appendix-F `K(Y)` bound, Dimock (642), ultralocal factorization
(643), the second Ursell gas, any Yang--Mills raw activity estimate, or a Clay
mass gap.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open Finset
open scoped BigOperators

/-- Shifted Appendix-F modified-metric exponential weight.  The shift
`d_M + 1` matches both the existing modified-metric summability theorem and
the finite stitching inequality. -/
noncomputable def appendixFHoleExpWeight
    {d L : ℕ} (HF : HoleFamily d L) (κ : ℝ)
    (X : Finset (Cube d L)) : ℝ :=
  Real.exp (-(κ *
    (((discreteModifiedMetric HF X + 1 : ℕ) : ℝ))))

/-- First-gas `K#` decay rate before the second Ursell expansion pays the
additional loss leading to the final residual `H#` rate. -/
def appendixFKsharpRate (κ κ₀ : ℝ) : ℝ :=
  κ - κ₀ - 2

theorem appendixFHoleExpWeight_nonneg
    {d L : ℕ} (HF : HoleFamily d L) (κ : ℝ)
    (X : Finset (Cube d L)) :
    0 ≤ appendixFHoleExpWeight HF κ X :=
  Real.exp_nonneg _

/-- The first-gas `K#` rate is the final second-Ursell residual rate plus the
extra leaf budget `2κ₀ + 1`. -/
theorem appendixFKsharpRate_eq_residual_add_leafRemainder
    (κ κ₀ : ℝ) :
    appendixFKsharpRate κ κ₀ =
      polymerClusterResidualRate κ κ₀ + (2 * κ₀ + 1) := by
  unfold appendixFKsharpRate polymerClusterResidualRate
  ring

/-- Shifted modified-metric exponential weights multiply when rates add. -/
theorem appendixFHoleExpWeight_add
    {d L : ℕ} (HF : HoleFamily d L) (a b : ℝ)
    (X : Finset (Cube d L)) :
    appendixFHoleExpWeight HF (a + b) X =
      appendixFHoleExpWeight HF a X *
        appendixFHoleExpWeight HF b X := by
  unfold appendixFHoleExpWeight
  rw [← Real.exp_add]
  congr 1
  ring

/-- The canonical first-gas rate factors into the final residual rate and the
spare leaf budget used by the hard-core leaf summation. -/
theorem appendixFHoleExpWeight_ksharpRate_factor
    {d L : ℕ} (HF : HoleFamily d L) (κ κ₀ : ℝ)
    (X : Finset (Cube d L)) :
    appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) X =
      appendixFHoleExpWeight HF
          (polymerClusterResidualRate κ κ₀) X *
        appendixFHoleExpWeight HF (2 * κ₀ + 1) X := by
  rw [appendixFKsharpRate_eq_residual_add_leafRemainder,
    appendixFHoleExpWeight_add]

/-- The shifted modified-metric exponential weight is antitone in its rate. -/
theorem appendixFHoleExpWeight_antitone
    {d L : ℕ} (HF : HoleFamily d L) {a b : ℝ}
    (hab : a ≤ b) (X : Finset (Cube d L)) :
    appendixFHoleExpWeight HF b X ≤
      appendixFHoleExpWeight HF a X := by
  unfold appendixFHoleExpWeight
  apply Real.exp_le_exp.mpr
  have hm :
      0 ≤ (((discreteModifiedMetric HF X + 1 : ℕ) : ℝ)) := by
    positivity
  nlinarith [mul_le_mul_of_nonneg_right hab hm]

/-- The canonical spare leaf budget is bounded by the hard-core `2κ₀` leaf
budget consumed by the finite leaf summation. -/
theorem appendixFHoleExpWeight_leafRemainder_le
    {d L : ℕ} (HF : HoleFamily d L) (κ₀ : ℝ)
    (X : Finset (Cube d L)) :
    appendixFHoleExpWeight HF (2 * κ₀ + 1) X ≤
      appendixFHoleExpWeight HF (2 * κ₀) X :=
  appendixFHoleExpWeight_antitone HF (by linarith) X

/-- Restrict the existing rooted geometric modified-metric sum to a finite
raw family `Λ`.  This adds no analytic content: it is the finite subsum of the
rooted `OmegaPolymerType` summability theorem. -/
theorem appendixFHole_rootedFiniteExpWeightSum_le
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (r : Cube d L) (κ₀ : ℝ)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    (∑ X ∈ Λ.filter
        (fun X => r ∈ skeleton HF X.val),
      appendixFHoleExpWeight HF κ₀ X.val)
      ≤
    (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹ := by
  classical
  let full := (Finset.univ : Finset (OmegaPolymerType HF z)).filter
    (fun X => r ∈ skeleton HF X.val)
  have hsub :
      Λ.filter (fun X => r ∈ skeleton HF X.val) ⊆ full := by
    intro X hX
    rw [mem_filter] at hX ⊢
    exact ⟨mem_univ X, hX.2⟩
  have hfinite :
      (∑ X ∈ Λ.filter (fun X => r ∈ skeleton HF X.val),
          appendixFHoleExpWeight HF κ₀ X.val)
        ≤
      ∑ X ∈ full, appendixFHoleExpWeight HF κ₀ X.val := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun X _ _ => appendixFHoleExpWeight_nonneg HF κ₀ X.val)
  have hfilter_eq :
      (∑ X ∈ full, appendixFHoleExpWeight HF κ₀ X.val)
        =
      ∑ P : { P : OmegaPolymerType HF z // r ∈ skeleton HF P.val },
        appendixFHoleExpWeight HF κ₀ P.val.val := by
    exact (Finset.sum_subtype full (fun X => by simp [full])
      (fun X => appendixFHoleExpWeight HF κ₀ X.val))
  have hroot :
      (∑ P : { P : OmegaPolymerType HF z // r ∈ skeleton HF P.val },
        appendixFHoleExpWeight HF κ₀ P.val.val)
        ≤
      (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹ := by
    simpa [appendixFHoleExpWeight, tsum_fintype] using
      omega_rooted_exp_discreteModifiedMetric_tsum_le HF z r κ₀
        hdisj hnoedges hholes_ne hCq
  exact hfinite.trans (hfilter_eq.trans_le hroot)

/-- Rooted local control implies the local estimate over all raw supports
contained in a representable full target `Y`.  The proof overcounts each raw
polymer by choosing an active skeleton root in `skeleton HF Y`, then bounds the
number of roots by `d_M(Y)+1`. -/
theorem appendixFHole_containedWeightSum_le_metric_mul_of_rooted
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (w : OmegaPolymerType HF z → ℝ)
    {K₀ : ℝ}
    (hw : ∀ X, X ∈ Λ → 0 ≤ w X)
    (hK₀ : 0 ≤ K₀)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val), w X) ≤ K₀)
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ) :
    (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), w X)
      ≤
    (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) * K₀ := by
  classical
  let g : OmegaPolymerType HF z → ℝ := fun X => if X ∈ Λ then w X else 0
  have hg : ∀ X, 0 ≤ g X := by
    intro X
    by_cases hX : X ∈ Λ
    · simpa [g, hX] using hw X hX
    · simp [g, hX]
  have hleft_eq :
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), w X)
        =
      ∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), g X := by
    refine Finset.sum_congr rfl ?_
    intro X hX
    rw [mem_filter] at hX
    simp [g, hX.1]
  have hroot_g : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val), g X) ≤ K₀ := by
    intro r
    calc
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val), g X)
          =
        ∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val), w X := by
            refine Finset.sum_congr rfl ?_
            intro X hX
            rw [mem_filter] at hX
            simp [g, hX.1]
      _ ≤ K₀ := hroot r
  have hsub :
      Λ.filter (fun X => X.val ⊆ Y) ⊆
        (skeleton HF Y).biUnion
          (fun r => Λ.filter
            (fun X : OmegaPolymerType HF z => r ∈ skeleton HF X.val)) := by
    intro X hX
    rw [mem_filter] at hX
    rcases X.property.right.right.right with ⟨r, hrX⟩
    have hrY : r ∈ skeleton HF Y :=
      skeleton_mono_of_subset HF hX.2 hrX
    rw [mem_biUnion]
    exact ⟨r, hrY, by
      rw [mem_filter]
      exact ⟨hX.1, hrX⟩⟩
  have hsub_sum :
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), g X)
        ≤
      ∑ X ∈ (skeleton HF Y).biUnion
          (fun r => Λ.filter
            (fun X : OmegaPolymerType HF z => r ∈ skeleton HF X.val)), g X := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun X _ _ => hg X)
  have hbi :
      ∑ X ∈ (skeleton HF Y).biUnion
          (fun r => Λ.filter
            (fun X : OmegaPolymerType HF z => r ∈ skeleton HF X.val)), g X
        ≤
      ∑ r ∈ skeleton HF Y,
        ∑ X ∈ Λ.filter
          (fun X : OmegaPolymerType HF z => r ∈ skeleton HF X.val), g X :=
    sum_biUnion_le (skeleton HF Y)
      (fun r => Λ.filter
        (fun X : OmegaPolymerType HF z => r ∈ skeleton HF X.val)) g hg
  have hroots :
      (∑ r ∈ skeleton HF Y,
        ∑ X ∈ Λ.filter
          (fun X : OmegaPolymerType HF z => r ∈ skeleton HF X.val), g X)
        ≤
      ∑ _r ∈ skeleton HF Y, K₀ := by
    refine Finset.sum_le_sum ?_
    intro r _hr
    exact hroot_g r
  have hsum_const :
      (∑ _r ∈ skeleton HF Y, K₀) =
        ((skeleton HF Y).card : ℝ) * K₀ := by
    rw [sum_const, nsmul_eq_mul]
  have hcard :
      ((skeleton HF Y).card : ℝ) ≤
        (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) := by
    have hconn : cubeConnected Y :=
      appendixFHoleTargetRegion_cubeConnected HF z Λ hY
    exact_mod_cast skeleton_card_le_discreteModifiedMetric_add_one HF Y hconn
  calc
    (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), w X)
        =
      ∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), g X := hleft_eq
    _ ≤
      ∑ X ∈ (skeleton HF Y).biUnion
          (fun r => Λ.filter
            (fun X : OmegaPolymerType HF z => r ∈ skeleton HF X.val)), g X :=
        hsub_sum
    _ ≤
      ∑ r ∈ skeleton HF Y,
        ∑ X ∈ Λ.filter
          (fun X : OmegaPolymerType HF z => r ∈ skeleton HF X.val), g X :=
        hbi
    _ ≤ ∑ _r ∈ skeleton HF Y, K₀ := hroots
    _ = ((skeleton HF Y).card : ℝ) * K₀ := hsum_const
    _ ≤ (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) * K₀ :=
        mul_le_mul_of_nonneg_right hcard hK₀

end YangMills.RG
