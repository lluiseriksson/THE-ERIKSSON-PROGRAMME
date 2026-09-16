/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The smooth partition profile in Balaban (1.118)

Balaban, *Propagators and Renormalization Transformations for Lattice Gauge
Theories. I*, printed p. 36, equation (1.118), chooses a real smooth profile
`h` supported in `(-2/3, 2/3)`, equal to one on `[-1/3, 1/3]`, and normalized
by

`sum_n h(t - n)^2 = 1`.

The corresponding `d`-dimensional cutoff is

`h_z(x) = prod_mu h((x_mu - z_mu) / M0)`.

This module records that source datum and proves the analytic consequence
used in the random-walk estimate: scaling by `M0` gives a tensor cutoff with
Lipschitz cost `L / M0` in each coordinate.  It does not postulate a bound on
`K(h)G h`; that operator estimate must be derived later from this slope and
the literal precision/Green kernels.
-/

namespace YangMills.RG

noncomputable section

/-- The one-dimensional source profile selected in (1.118), together with a
finite derivative budget for that selected smooth compactly supported
function.  The budget is analytic data about `h`, not a commutator estimate. -/
structure CMP95SourceSmoothPartitionProfile where
  value : ℝ → ℝ
  contDiff : ContDiff ℝ ⊤ value
  support_subset : Function.support value ⊆ Set.Ioo (-(2 / 3 : ℝ)) (2 / 3)
  plateau : ∀ t ∈ Set.Icc (-(1 / 3 : ℝ)) (1 / 3), value t = 1
  square_tsum : ∀ t, ∑' n : ℤ, value (t - n) ^ 2 = 1
  norm_value_le_one : ∀ t, ‖value t‖ ≤ 1
  derivBound : ℝ
  derivBound_nonneg : 0 ≤ derivBound
  norm_deriv_le : ∀ t, ‖deriv value t‖ ≤ derivBound

namespace CMP95SourceSmoothPartitionProfile

/-- The derivative budget makes the selected source profile globally
Lipschitz.  Compact support is what guarantees such a finite budget for the
smooth profile chosen in the paper. -/
theorem norm_value_sub_value_le
    (P : CMP95SourceSmoothPartitionProfile) (x y : ℝ) :
    ‖P.value y - P.value x‖ ≤ P.derivBound * ‖y - x‖ := by
  exact convex_univ.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := P.value)
    (fun _ _ => P.contDiff.differentiable (by simp) _)
    (fun t _ => P.norm_deriv_le t) (Set.mem_univ x) (Set.mem_univ y)

/-- The square appearing literally in the commutator `[G',(h')²]` is
globally Lipschitz with only the sharp elementary factor two.  Proving this
at profile level avoids asking downstream code for an abstract squared-
cutoff estimate. -/
theorem norm_value_sq_sub_value_sq_le
    (P : CMP95SourceSmoothPartitionProfile) (x y : ℝ) :
    ‖P.value y ^ 2 - P.value x ^ 2‖ ≤
      (2 * P.derivBound) * ‖y - x‖ := by
  rw [show P.value y ^ 2 - P.value x ^ 2 =
      (P.value y - P.value x) * (P.value y + P.value x) by ring,
    norm_mul]
  calc
    ‖P.value y - P.value x‖ * ‖P.value y + P.value x‖ ≤
        (P.derivBound * ‖y - x‖) * (1 + 1) := by
      apply mul_le_mul (P.norm_value_sub_value_le x y)
      · exact (norm_add_le _ _).trans
          (add_le_add (P.norm_value_le_one y) (P.norm_value_le_one x))
      · exact norm_nonneg _
      · exact (norm_nonneg _).trans (P.norm_value_sub_value_le x y)
    _ = (2 * P.derivBound) * ‖y - x‖ := by ring

/-- The literal one-dimensional rescaling in (1.118). -/
def scaledValue (P : CMP95SourceSmoothPartitionProfile)
    (M0 center x : ℝ) : ℝ :=
  P.value ((x - center) / M0)

/-- Rescaling the source profile by a positive `M0` produces the exact
`M0⁻¹` slope. -/
theorem norm_scaledValue_sub_scaledValue_le
    (P : CMP95SourceSmoothPartitionProfile)
    {M0 : ℝ} (hM0 : 0 < M0) (center x y : ℝ) :
    ‖P.scaledValue M0 center y - P.scaledValue M0 center x‖ ≤
      (P.derivBound / M0) * ‖y - x‖ := by
  have h := P.norm_value_sub_value_le
    ((x - center) / M0) ((y - center) / M0)
  unfold scaledValue
  calc
    ‖P.value ((y - center) / M0) - P.value ((x - center) / M0)‖ ≤
        P.derivBound *
          ‖((y - center) / M0) - ((x - center) / M0)‖ := h
    _ = P.derivBound * ‖(y - x) / M0‖ := by ring_nf
    _ = (P.derivBound / M0) * ‖y - x‖ := by
      rw [norm_div, show ‖M0‖ = M0 by
        simpa [Real.norm_eq_abs] using abs_of_pos hM0]
      ring

/-- At scale `M0`, the squared source profile has slope
`2 * derivBound / M0`, exactly the quantity entering the printed squared
partition commutator. -/
theorem norm_scaledValue_sq_sub_scaledValue_sq_le
    (P : CMP95SourceSmoothPartitionProfile)
    {M0 : ℝ} (hM0 : 0 < M0) (center x y : ℝ) :
    ‖P.scaledValue M0 center y ^ 2 -
        P.scaledValue M0 center x ^ 2‖ ≤
      ((2 * P.derivBound) / M0) * ‖y - x‖ := by
  have h := P.norm_value_sq_sub_value_sq_le
    ((x - center) / M0) ((y - center) / M0)
  unfold scaledValue
  calc
    ‖P.value ((y - center) / M0) ^ 2 -
        P.value ((x - center) / M0) ^ 2‖ ≤
      (2 * P.derivBound) *
        ‖((y - center) / M0) - ((x - center) / M0)‖ := h
    _ = (2 * P.derivBound) * ‖(y - x) / M0‖ := by ring_nf
    _ = ((2 * P.derivBound) / M0) * ‖y - x‖ := by
      rw [norm_div, show ‖M0‖ = M0 by
        simpa [Real.norm_eq_abs] using abs_of_pos hM0]
      ring

/-- Tensor-product cutoff `h_z` from the display preceding (1.118). -/
def tensorCutoff {d : ℕ} (P : CMP95SourceSmoothPartitionProfile)
    (M0 : ℝ) (z x : Fin d → ℝ) : ℝ :=
  ∏ μ, P.scaledValue M0 (z μ) (x μ)

/-- Every tensor cutoff remains contractive because every source profile
factor is contractive. -/
theorem norm_tensorCutoff_le_one {d : ℕ}
    (P : CMP95SourceSmoothPartitionProfile)
    (M0 : ℝ) (z x : Fin d → ℝ) :
    ‖P.tensorCutoff M0 z x‖ ≤ 1 := by
  classical
  rw [tensorCutoff, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun μ _ => P.norm_value_le_one _)

/-- A finite product of contractive real factors changes by at most the sum
of the changes of its factors. -/
theorem norm_prod_sub_prod_le_sum_norm_sub
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℝ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤
      ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : ‖f a‖ ≤ 1 := hf a (Finset.mem_insert_self a s)
      have hga : ‖g a‖ ≤ 1 := hg a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)
      have hgs : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi =>
        hg i (Finset.mem_insert_of_mem hi)
      have hprodG : ‖∏ i ∈ s, g i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) hgs
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha]
      calc
        ‖f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i‖ =
            ‖f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
              (f a - g a) * ∏ i ∈ s, g i‖ := by
                congr 1
                ring
        _ ≤ ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ +
            ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ := by
              simpa only [norm_mul] using norm_add_le
                (f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
                ((f a - g a) * ∏ i ∈ s, g i)
        _ ≤ 1 * (∑ i ∈ s, ‖f i - g i‖) +
            ‖f a - g a‖ * 1 := by
              gcongr
              exact ih hfs hgs
        _ = ‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖ := by ring

/-- Source-facing tensor slope.  The bound uses the `ℓ¹` coordinate
distance, matching Balaban's distance convention stated at the start of
Part II.  Crucially, the scale appears as `M0⁻¹`. -/
theorem norm_tensorCutoff_sub_tensorCutoff_le {d : ℕ}
    (P : CMP95SourceSmoothPartitionProfile)
    {M0 : ℝ} (hM0 : 0 < M0) (z x y : Fin d → ℝ) :
    ‖P.tensorCutoff M0 z y - P.tensorCutoff M0 z x‖ ≤
      (P.derivBound / M0) * ∑ μ, ‖y μ - x μ‖ := by
  classical
  unfold tensorCutoff
  calc
    ‖∏ μ, P.scaledValue M0 (z μ) (y μ) -
        ∏ μ, P.scaledValue M0 (z μ) (x μ)‖ ≤
        ∑ μ, ‖P.scaledValue M0 (z μ) (y μ) -
          P.scaledValue M0 (z μ) (x μ)‖ := by
      apply norm_prod_sub_prod_le_sum_norm_sub Finset.univ
      · intro μ _
        exact P.norm_value_le_one _
      · intro μ _
        exact P.norm_value_le_one _
    _ ≤ ∑ μ, (P.derivBound / M0) * ‖y μ - x μ‖ := by
      gcongr with μ
      exact P.norm_scaledValue_sub_scaledValue_le hM0 (z μ) (x μ) (y μ)
    _ = (P.derivBound / M0) * ∑ μ, ‖y μ - x μ‖ := by
      rw [Finset.mul_sum]

end CMP95SourceSmoothPartitionProfile

end
end YangMills.RG
