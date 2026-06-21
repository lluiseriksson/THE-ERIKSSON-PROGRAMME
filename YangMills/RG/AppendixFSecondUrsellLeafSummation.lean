/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

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

end YangMills.RG
