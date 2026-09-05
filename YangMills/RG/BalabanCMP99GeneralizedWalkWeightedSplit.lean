/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99GeneralizedRandomWalk
import YangMills.RG.PhysicalWeightedRowKernel

/-!
# Weighted-row estimates for a split generalized walk

A split at any literal factor occurrence has two source-faithful pieces.  The
prefix contains the distinguished head and has amplitude `Ahead * rho^i`;
the suffix contains only continuations and has amplitude
`rho^(walk.length-i)`.  Both retain one unchanged spatial rate.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The prefix through factor `i` is exactly an ordered product of the head
and the first `i` continuation factors. -/
theorem CMP99GeneralizedWalk.prod_take_mul_factorAt_eq_physicalOrderedProduct_take
    {Label Domain : Type*}
    {d N Nc : ℕ} [NeZero N]
    (walk : CMP99GeneralizedWalk Label Domain)
    (R0 : Domain → PhysicalEndomorphism d N Nc)
    (R : Label → Domain → PhysicalEndomorphism d N Nc)
    (i : Fin walk.domains.length) :
    ((walk.factors R0 R).take i).prod *
        walk.factorAt R0 R i =
      physicalOrderedProduct (R0 walk.head)
        ((walk.tail.map (fun step => R step.label step.domain)).take i) := by
  have hiFactors : i.val < (walk.factors R0 R).length := by
    rw [walk.length_factors R0 R]
    exact i.isLt
  have htake :=
    List.prod_take_succ (walk.factors R0 R) i hiFactors
  calc
    ((walk.factors R0 R).take i).prod *
        walk.factorAt R0 R i =
      ((walk.factors R0 R).take (i + 1)).prod := by
        simpa [CMP99GeneralizedWalk.factorAt] using htake.symm
    _ = physicalOrderedProduct (R0 walk.head)
        ((walk.tail.map (fun step => R step.label step.domain)).take i) := by
      rw [physicalOrderedProduct_eq_head_mul_prod]
      simp [CMP99GeneralizedWalk.factors]

/-- The suffix strictly after factor `i` is exactly the product of the
remaining continuation factors. -/
theorem CMP99GeneralizedWalk.prod_drop_succ_factors_eq_tail_drop_prod
    {Label Domain E : Type*} [Monoid E]
    (walk : CMP99GeneralizedWalk Label Domain)
    (R0 : Domain → E) (R : Label → Domain → E)
    (i : Fin walk.domains.length) :
    ((walk.factors R0 R).drop (i + 1)).prod =
      ((walk.tail.map (fun step => R step.label step.domain)).drop i).prod := by
  simp [CMP99GeneralizedWalk.factors]

/-- The prefix through a selected factor inherits the exact head-times-power
weighted-row amplitude. -/
theorem CMP99GeneralizedWalk.prefixThroughFactor_weightedRowKernelBound
    {Label Domain : Type*}
    {d N Nc : ℕ} [NeZero N]
    (walk : CMP99GeneralizedWalk Label Domain)
    (R0 : Domain → PhysicalEndomorphism d N Nc)
    (R : Label → Domain → PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    {Ahead rho rate : ℝ}
    (hhead : ∀ X,
      PhysicalCovarianceWeightedRowKernelBound (R0 X) dist Ahead rate)
    (hcontinuation : ∀ label X,
      PhysicalCovarianceWeightedRowKernelBound (R label X) dist rho rate)
    (i : Fin walk.domains.length) :
    PhysicalCovarianceWeightedRowKernelBound
      (((walk.factors R0 R).take i).prod *
        walk.factorAt R0 R i)
      dist (Ahead * rho ^ i.val) rate := by
  rw [
    walk.prod_take_mul_factorAt_eq_physicalOrderedProduct_take R0 R i]
  have htail :
      ∀ next,
        next ∈
            (walk.tail.map
              (fun step => R step.label step.domain)).take i →
          PhysicalCovarianceWeightedRowKernelBound next dist rho rate := by
    intro next hnext
    have hmem :
        next ∈ walk.tail.map (fun step => R step.label step.domain) :=
      List.mem_of_mem_take hnext
    rcases List.mem_map.mp hmem with ⟨step, _hstep, rfl⟩
    exact hcontinuation step.label step.domain
  have hout :=
    physicalCovarianceWeightedRowKernelBound_orderedProduct
      dist htri (R0 walk.head) (hhead walk.head)
      ((walk.tail.map
        (fun step => R step.label step.domain)).take i) htail
  have hi : i.val ≤ walk.tail.length := by
    simpa [CMP99GeneralizedWalk.domains] using i.isLt
  simpa [List.length_take, hi, Nat.min_eq_left] using hout

/-- The suffix after a selected factor is a possibly empty continuation
product with the exact remaining power amplitude. -/
theorem CMP99GeneralizedWalk.suffixAfterFactor_weightedRowKernelBound
    {Label Domain : Type*}
    {d N Nc : ℕ} [NeZero N]
    (walk : CMP99GeneralizedWalk Label Domain)
    (R0 : Domain → PhysicalEndomorphism d N Nc)
    (R : Label → Domain → PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hdiag : ∀ source, dist source source = 0)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    {rho rate : ℝ} (hrate : 0 ≤ rate)
    (hcontinuation : ∀ label X,
      PhysicalCovarianceWeightedRowKernelBound (R label X) dist rho rate)
    (i : Fin walk.domains.length) :
    PhysicalCovarianceWeightedRowKernelBound
      ((walk.factors R0 R).drop (i + 1)).prod
      dist (rho ^ (walk.tail.length - i.val)) rate := by
  rw [walk.prod_drop_succ_factors_eq_tail_drop_prod R0 R i]
  let suffix :=
    (walk.tail.map (fun step => R step.label step.domain)).drop i
  have hsuffix :
      ∀ next, next ∈ suffix →
        PhysicalCovarianceWeightedRowKernelBound next dist rho rate := by
    intro next hnext
    have hmem :
        next ∈ walk.tail.map (fun step => R step.label step.domain) :=
      List.mem_of_mem_drop hnext
    rcases List.mem_map.mp hmem with ⟨step, _hstep, rfl⟩
    exact hcontinuation step.label step.domain
  have hout :=
    physicalCovarianceWeightedRowKernelBound_list_prod
      dist hdiag htri suffix hrate hsuffix
  simpa [suffix, List.length_drop] using hout

/-- The complementary continuation powers carried by a split factor
recombine into the exact total continuation length. -/
theorem CMP99GeneralizedWalk.rho_pow_suffix_mul_prefix_eq
    {Label Domain : Type*}
    (walk : CMP99GeneralizedWalk Label Domain)
    (rho : ℝ) (i : Fin walk.domains.length) :
    rho ^ (walk.tail.length - i.val) * rho ^ i.val =
      rho ^ walk.tail.length := by
  have hi : i.val ≤ walk.tail.length := by
    simpa [CMP99GeneralizedWalk.domains] using i.isLt
  rw [← pow_add, Nat.sub_add_cancel hi]

end

end YangMills.RG
