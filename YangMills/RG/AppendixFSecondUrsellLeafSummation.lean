/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellMarkedFugacity
import YangMills.RG.AppendixFSecondUrsellGeometry

/-!
# Appendix F second-Ursell leaf-summation input

This module exposes the hard-core neighbor estimate from
`AppendixFSecondUrsellGeometry` as a nonnegative incompatibility kernel.  This
is the finite input needed by later rooted leaf-summation arguments: the local
choice at a child vertex can be read as a full-universe sum with an explicit
zero outside the incompatible fiber.

No source theorem, continuum statement, or infinite tree summation is added
here.  The only analytic content is the already-proved finite hard-core
metric-moment estimate, repackaged for downstream tree recursions.  The
moment-lift lemma records the elementary bookkeeping needed when a child
subtree leaves a power of the child metric to be summed at the parent edge.
The final two lemmas in this file are the target-decay composition layer:
extract the fixed-union exponential first, then consume any marked-root
leaf-summation estimate.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
-/

attribute [local instance] Classical.propDecidable

open Finset
open scoped BigOperators

namespace YangMills.RG

/-- Nonnegative child-choice kernel for a source-facing omega polymer `Q`.

It is the shifted metric moment times the spare exponential weight on `Q'`,
and is set to zero unless `Q'` is hard-core incompatible with `Q`. -/
noncomputable def appendixFHoleIncompMomentKernel
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ) (κ₀ : ℝ) (j : ℕ)
    (Q Q' : OmegaPolymerType HF zK) : ℝ :=
  if (omegaHolePolymerSystem HF zK).incomp Q Q' then
    (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
      appendixFHoleExpWeight HF (2 * κ₀) Q'.val
  else
    0

/-- The child-choice kernel is pointwise nonnegative. -/
theorem appendixFHoleIncompMomentKernel_nonneg
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ) (κ₀ : ℝ) (j : ℕ)
    (Q Q' : OmegaPolymerType HF zK) :
    0 ≤ appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q' := by
  classical
  by_cases hinc : (omegaHolePolymerSystem HF zK).incomp Q Q'
  · have hweight :
        0 ≤
          (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
            appendixFHoleExpWeight HF (2 * κ₀) Q'.val := by
      exact mul_nonneg (pow_nonneg (by positivity) j)
        (appendixFHoleExpWeight_nonneg HF (2 * κ₀) Q'.val)
    simpa [appendixFHoleIncompMomentKernel, hinc] using hweight
  · simp [appendixFHoleIncompMomentKernel, hinc]

/-- Full-universe child-choice sum controlled by the finite hard-core
metric-moment estimate.  This is the form consumed by rooted leaf-summation:
the incompatibility condition has been moved into the kernel. -/
theorem appendixFHoleIncompMomentKernel_sum_le_factorial_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Q : OmegaPolymerType HF zK) (κ₀ : ℝ) (j : ℕ)
    (hκ₀ : 0 < κ₀)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    (∑ Q' : OmegaPolymerType HF zK,
      appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q')
      ≤
    (j.factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + 1) *
        (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)) := by
  classical
  let p : OmegaPolymerType HF zK → Prop := fun Q' =>
    (omegaHolePolymerSystem HF zK).incomp Q Q'
  let w : OmegaPolymerType HF zK → ℝ := fun Q' =>
    (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ j) *
      appendixFHoleExpWeight HF (2 * κ₀) Q'.val
  have hsum :
      (∑ Q' : OmegaPolymerType HF zK,
        appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q')
        =
      (∑ Q' ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter p,
        w Q') := by
    calc
      (∑ Q' : OmegaPolymerType HF zK,
        appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q')
          =
        ∑ Q' : OmegaPolymerType HF zK, if p Q' then w Q' else 0 := by
          simp [appendixFHoleIncompMomentKernel, p, w]
      _ =
        (∑ Q' ∈ (Finset.univ : Finset (OmegaPolymerType HF zK)).filter p,
          w Q') := by
          simpa using
            (Finset.sum_filter (s := (Finset.univ : Finset (OmegaPolymerType HF zK)))
              (p := p) (f := w)).symm
  rw [hsum]
  simpa [p, w] using
    appendixFHole_incomp_expWeight_metricMomentSum_le_factorial_mul
      HF zK Q κ₀ j hκ₀ hdisj hnoedges hholes_ne hCq

/-- Multiplying a child-choice kernel by an additional child metric moment is
the same as increasing its moment index.  This is the one-edge bookkeeping
identity used before applying the finite hard-core moment estimate. -/
theorem appendixFHoleIncompMomentKernel_childMoment_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ) (κ₀ : ℝ) (j k : ℕ)
    (Q Q' : OmegaPolymerType HF zK) :
    (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ k) *
      appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q'
      =
    appendixFHoleIncompMomentKernel HF zK κ₀ (j + k) Q Q' := by
  classical
  by_cases hinc : (omegaHolePolymerSystem HF zK).incomp Q Q'
  · simp [appendixFHoleIncompMomentKernel, hinc, pow_add, mul_comm,
      mul_assoc]
  · simp [appendixFHoleIncompMomentKernel, hinc]

/-- Child-moment version of the hard-core kernel bound.  Any extra metric
moment produced by a child subtree can be absorbed into the factorial moment
index on the local parent-edge sum. -/
theorem appendixFHoleIncompMomentKernel_childMoment_sum_le_factorial_mul
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Q : OmegaPolymerType HF zK) (κ₀ : ℝ) (j k : ℕ)
    (hκ₀ : 0 < κ₀)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    (∑ Q' : OmegaPolymerType HF zK,
      (((discreteModifiedMetric HF Q'.val + 1 : ℕ) : ℝ) ^ k) *
        appendixFHoleIncompMomentKernel HF zK κ₀ j Q Q')
      ≤
    ((j + k).factorial : ℝ) *
      appendixFSecondUrsellMomentConstant d κ₀ ^ (j + k + 1) *
        (((discreteModifiedMetric HF Q.val + 1 : ℕ) : ℝ)) := by
  classical
  rw [Finset.sum_congr rfl (fun Q' _ =>
    appendixFHoleIncompMomentKernel_childMoment_mul HF zK κ₀ j k Q Q')]
  exact appendixFHoleIncompMomentKernel_sum_le_factorial_mul
    HF zK Q κ₀ (j + k) hκ₀ hdisj hnoedges hholes_ne hCq

/-- Target-decaying composition from a marked-root leaf-summation bound.

The order matters: first use the fixed-union metric stitching theorem to
extract the target exponential weight, and only then pass to the marked-root
overcount.  Thus the marked-root estimate may be proved later without needing
to remember the exact union fiber. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w u : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (r : Cube d L)
    (n : ℕ)
    (rate Croot Cleaf : ℝ)
    (hrate : 0 ≤ rate)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hu : ∀ Q : OmegaPolymerType HF zK, 0 ≤ u Q)
    (hsplit :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF rate Q.val * u Q)
    (hr : r ∈ skeleton HF Y)
    (hleaf :
      ((n : ℝ) + 1) *
          appendixFHoleHsharpWeightedTreeMarkedRootSum
            HF zK u r n
        ≤ Croot * Cleaf ^ n) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      Croot *
        appendixFHoleExpWeight HF rate Y *
        Cleaf ^ n := by
  calc
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n
        ≤ appendixFHoleExpWeight HF rate Y *
            appendixFHoleHsharpWeightedTreeTerm HF zK u Y n :=
      appendixFHoleHsharpWeightedTreeTerm_le_targetExpWeight_mul
        HF zK w u Y n rate hrate hw hu hsplit
    _ ≤ appendixFHoleExpWeight HF rate Y *
          (((n : ℝ) + 1) *
            appendixFHoleHsharpWeightedTreeMarkedRootSum
              HF zK u r n) := by
      exact mul_le_mul_of_nonneg_left
        (appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum_of_mem_skeleton
          HF zK u Y r n hu hr)
        (appendixFHoleExpWeight_nonneg HF rate Y)
    _ ≤ appendixFHoleExpWeight HF rate Y *
          (Croot * Cleaf ^ n) := by
      exact mul_le_mul_of_nonneg_left hleaf
        (appendixFHoleExpWeight_nonneg HF rate Y)
    _ = Croot *
          appendixFHoleExpWeight HF rate Y *
          Cleaf ^ n := by
      ring

/-- Nonempty-target version of
`appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation`.
It chooses a skeleton root after the target exponential has been made
available, while requiring the marked-root bound uniformly over skeleton
roots. -/
theorem appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation_of_skeleton_nonempty
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w u : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (n : ℕ)
    (rate Croot Cleaf : ℝ)
    (hrate : 0 ≤ rate)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hu : ∀ Q : OmegaPolymerType HF zK, 0 ≤ u Q)
    (hsplit :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF rate Q.val * u Q)
    (hY : (skeleton HF Y).Nonempty)
    (hleaf :
      ∀ r : Cube d L, r ∈ skeleton HF Y →
        ((n : ℝ) + 1) *
            appendixFHoleHsharpWeightedTreeMarkedRootSum
              HF zK u r n
          ≤ Croot * Cleaf ^ n) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      Croot *
        appendixFHoleExpWeight HF rate Y *
        Cleaf ^ n := by
  classical
  rcases hY with ⟨r, hr⟩
  exact
    appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation
      HF zK w u Y r n rate Croot Cleaf hrate hw hu hsplit hr
      (hleaf r hr)

end YangMills.RG
