/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalExponentialKernelComposition

/-!
# Fixed-rate weighted row kernels

Pointwise exponential kernel estimates lose a fixed amount of decay rate at
every use of the elementary composition theorem.  That is unsuitable for an
ordered random walk of arbitrary length.  This file packages the standard
weighted-row (Schur) norm instead.  Its amplitude is submultiplicative while
its spatial rate is fixed.

This is the analytic product mechanism needed by a CMP99 `(3.108)`-shaped
bound.  It deliberately does not claim the source estimate itself: the
nonzero Sect. C factor alphabet and its concrete operator dictionary remain
separate source data.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- A fixed-rate weighted row-kernel bound.  The source bond is fixed and the
target bond is summed.  Unlike a pointwise exponential bound, this predicate
is submultiplicative at the same rate. -/
def PhysicalCovarianceWeightedRowKernelBound
    {d N Nc : ℕ} [NeZero N]
    (T : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (A rate : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ rate ∧
    ∀ source (v : SUNLieCoord Nc),
      ∑ target : PhysicalBond d N,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singlePhysicalBondCochain source v) target‖ ≤
        A * ‖v‖

/-- A pointwise exponential kernel estimate yields a weighted-row estimate at
any lower chosen rate.  The row sum at the rate deficit remains explicit so
that volume uniformity cannot be hidden in a finite ambient cardinality. -/
theorem physicalCovarianceWeightedRowKernelBound_of_exponential
    {d N Nc : ℕ} [NeZero N]
    (T : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A rate weight S : ℝ}
    (hweight : 0 ≤ weight) (hS : 0 ≤ S)
    (hT : PhysicalCovarianceExponentialKernelBound T dist A rate)
    (hsum : ∀ source,
      ∑ target : PhysicalBond d N,
        Real.exp (-((rate - weight) * (dist target source : ℝ))) ≤ S) :
    PhysicalCovarianceWeightedRowKernelBound T dist (A * S) weight := by
  refine ⟨mul_nonneg hT.1 hS, hweight, ?_⟩
  intro source v
  calc
    ∑ target : PhysicalBond d N,
          Real.exp (weight * (dist target source : ℝ)) *
            ‖T (singlePhysicalBondCochain source v) target‖
        ≤ ∑ target : PhysicalBond d N,
            A * Real.exp (-((rate - weight) *
              (dist target source : ℝ))) * ‖v‖ := by
          apply Finset.sum_le_sum
          intro target _
          calc
            Real.exp (weight * (dist target source : ℝ)) *
                ‖T (singlePhysicalBondCochain source v) target‖
              ≤ Real.exp (weight * (dist target source : ℝ)) *
                  (A * Real.exp (-(rate *
                    (dist target source : ℝ))) * ‖v‖) :=
                mul_le_mul_of_nonneg_left
                  (hT.2.2 source target v) (Real.exp_pos _).le
            _ = A * Real.exp (-((rate - weight) *
                  (dist target source : ℝ))) * ‖v‖ := by
                have hexp :
                    Real.exp (weight * (dist target source : ℝ)) *
                        Real.exp (-(rate * (dist target source : ℝ))) =
                      Real.exp (-((rate - weight) *
                        (dist target source : ℝ))) := by
                  rw [← Real.exp_add]
                  congr 1
                  ring
                calc
                  Real.exp (weight * (dist target source : ℝ)) *
                      (A * Real.exp (-(rate *
                        (dist target source : ℝ))) * ‖v‖) =
                    A *
                      (Real.exp (weight * (dist target source : ℝ)) *
                        Real.exp (-(rate *
                          (dist target source : ℝ)))) * ‖v‖ := by ring
                  _ = A * Real.exp (-((rate - weight) *
                        (dist target source : ℝ))) * ‖v‖ := by rw [hexp]
    _ = (A * ‖v‖) * ∑ target : PhysicalBond d N,
          Real.exp (-((rate - weight) *
            (dist target source : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro target _
        ring
    _ ≤ (A * ‖v‖) * S :=
      mul_le_mul_of_nonneg_left (hsum source)
        (mul_nonneg hT.1 (norm_nonneg v))
    _ = (A * S) * ‖v‖ := by ring

/-- Weighted row-kernel amplitudes multiply under operator composition, with
no loss of the spatial rate.  Only the directed triangle inequality in the
target--intermediate--source order is used. -/
theorem physicalCovarianceWeightedRowKernelBound_comp
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    {Left Right : PhysicalEndomorphism d N Nc}
    {A B rate : ℝ}
    (hLeft : PhysicalCovarianceWeightedRowKernelBound Left dist A rate)
    (hRight : PhysicalCovarianceWeightedRowKernelBound Right dist B rate) :
    PhysicalCovarianceWeightedRowKernelBound
      (Left.comp Right) dist (A * B) rate := by
  refine ⟨mul_nonneg hLeft.1 hRight.1, hLeft.2.1, ?_⟩
  intro source v
  let delta := singlePhysicalBondCochain
    (d := d) (N := N) (Nc := Nc) source v
  have hdecomp :
      Right delta =
        ∑ middle : PhysicalBond d N,
          singlePhysicalBondCochain middle (Right delta middle) :=
    (sum_singlePhysicalBondCochain_eq (Right delta)).symm
  have happ : ∀ target,
      (Left.comp Right) delta target =
        ∑ middle : PhysicalBond d N,
          Left (singlePhysicalBondCochain middle
            (Right delta middle)) target := by
    intro target
    calc
      (Left.comp Right) delta target = Left (Right delta) target := rfl
      _ = Left (∑ middle : PhysicalBond d N,
          singlePhysicalBondCochain middle (Right delta middle)) target :=
        congrArg (fun w => Left w target) hdecomp
      _ = ∑ middle : PhysicalBond d N,
          Left (singlePhysicalBondCochain middle
            (Right delta middle)) target := by
        rw [map_sum, physicalCochain_sum_apply]
  have hweight : ∀ target middle,
      Real.exp (rate * (dist target source : ℝ)) ≤
        Real.exp (rate * (dist target middle : ℝ)) *
          Real.exp (rate * (dist middle source : ℝ)) := by
    intro target middle
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htri' : (dist target source : ℝ) ≤
        (dist target middle : ℝ) + (dist middle source : ℝ) := by
      exact_mod_cast htri target source middle
    calc
      rate * (dist target source : ℝ) ≤
          rate * ((dist target middle : ℝ) +
            (dist middle source : ℝ)) :=
        mul_le_mul_of_nonneg_left htri' hLeft.2.1
      _ = rate * (dist target middle : ℝ) +
          rate * (dist middle source : ℝ) := by ring
  calc
    ∑ target : PhysicalBond d N,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖(Left.comp Right) delta target‖
        ≤ ∑ target : PhysicalBond d N,
            Real.exp (rate * (dist target source : ℝ)) *
              ∑ middle : PhysicalBond d N,
                ‖Left (singlePhysicalBondCochain middle
                  (Right delta middle)) target‖ := by
          apply Finset.sum_le_sum
          intro target _
          rw [happ target]
          exact mul_le_mul_of_nonneg_left
            (norm_sum_le _ _) (Real.exp_pos _).le
    _ ≤ ∑ target : PhysicalBond d N,
          ∑ middle : PhysicalBond d N,
            (Real.exp (rate * (dist target middle : ℝ)) *
              ‖Left (singlePhysicalBondCochain middle
                (Right delta middle)) target‖) *
              Real.exp (rate * (dist middle source : ℝ)) := by
        apply Finset.sum_le_sum
        intro target _
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro middle _
        calc
          Real.exp (rate * (dist target source : ℝ)) *
              ‖Left (singlePhysicalBondCochain middle
                (Right delta middle)) target‖
            ≤ (Real.exp (rate * (dist target middle : ℝ)) *
                Real.exp (rate * (dist middle source : ℝ))) *
                ‖Left (singlePhysicalBondCochain middle
                  (Right delta middle)) target‖ :=
              mul_le_mul_of_nonneg_right (hweight target middle)
                (norm_nonneg _)
          _ = (Real.exp (rate * (dist target middle : ℝ)) *
                ‖Left (singlePhysicalBondCochain middle
                  (Right delta middle)) target‖) *
                Real.exp (rate * (dist middle source : ℝ)) := by ring
    _ = ∑ middle : PhysicalBond d N,
          (∑ target : PhysicalBond d N,
            Real.exp (rate * (dist target middle : ℝ)) *
              ‖Left (singlePhysicalBondCochain middle
                (Right delta middle)) target‖) *
            Real.exp (rate * (dist middle source : ℝ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro middle _
        rw [Finset.sum_mul]
    _ ≤ ∑ middle : PhysicalBond d N,
          (A * ‖Right delta middle‖) *
            Real.exp (rate * (dist middle source : ℝ)) := by
        apply Finset.sum_le_sum
        intro middle _
        exact mul_le_mul_of_nonneg_right
          (hLeft.2.2 middle (Right delta middle)) (Real.exp_pos _).le
    _ = A * ∑ middle : PhysicalBond d N,
          Real.exp (rate * (dist middle source : ℝ)) *
            ‖Right delta middle‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro middle _
        ring
    _ ≤ A * (B * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hRight.2.2 source v) hLeft.1
    _ = (A * B) * ‖v‖ := by ring

/-- A weighted row estimate contains each individual target term and hence
implies the corresponding pointwise exponential kernel estimate. -/
theorem physicalCovarianceExponentialKernelBound_of_weightedRow
    {d N Nc : ℕ} [NeZero N]
    (T : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A rate : ℝ}
    (hrate : 0 < rate)
    (hT : PhysicalCovarianceWeightedRowKernelBound T dist A rate) :
    PhysicalCovarianceExponentialKernelBound T dist A rate := by
  refine ⟨hT.1, hrate, ?_⟩
  intro source target v
  have hterm :
      Real.exp (rate * (dist target source : ℝ)) *
          ‖T (singlePhysicalBondCochain source v) target‖ ≤
        ∑ next : PhysicalBond d N,
          Real.exp (rate * (dist next source : ℝ)) *
            ‖T (singlePhysicalBondCochain source v) next‖ := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (PhysicalBond d N)))
      (f := fun next : PhysicalBond d N =>
        Real.exp (rate * (dist next source : ℝ)) *
          ‖T (singlePhysicalBondCochain source v) next‖)
      (fun next _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (Finset.mem_univ target)
  have hmul :
      Real.exp (rate * (dist target source : ℝ)) *
          ‖T (singlePhysicalBondCochain source v) target‖ ≤ A * ‖v‖ :=
    hterm.trans (hT.2.2 source v)
  have hpos := Real.exp_pos (rate * (dist target source : ℝ))
  calc
    ‖T (singlePhysicalBondCochain source v) target‖
        ≤ (A * ‖v‖) /
            Real.exp (rate * (dist target source : ℝ)) :=
      (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hmul)
    _ = A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring

/-- Left-to-right ordered composition: the head is target-adjacent and the
last list entry is source-adjacent.  This is the operator order used by the
CMP99 generalized-walk term. -/
def physicalOrderedProduct
    {d N Nc : ℕ} [NeZero N]
    (head : PhysicalEndomorphism d N Nc)
    (tail : List (PhysicalEndomorphism d N Nc)) :
    PhysicalEndomorphism d N Nc :=
  tail.foldl (fun acc next => acc.comp next) head

@[simp] theorem physicalOrderedProduct_nil
    {d N Nc : ℕ} [NeZero N]
    (head : PhysicalEndomorphism d N Nc) :
    physicalOrderedProduct head [] = head :=
  rfl

@[simp] theorem physicalOrderedProduct_cons
    {d N Nc : ℕ} [NeZero N]
    (head next : PhysicalEndomorphism d N Nc)
    (tail : List (PhysicalEndomorphism d N Nc)) :
    physicalOrderedProduct head (next :: tail) =
      physicalOrderedProduct (head.comp next) tail :=
  rfl

/-- The ordered-composition presentation agrees with the multiplication and
`List.prod` convention used by generalized CMP99 walk terms. -/
theorem physicalOrderedProduct_eq_head_mul_prod
    {d N Nc : ℕ} [NeZero N]
    (head : PhysicalEndomorphism d N Nc)
    (tail : List (PhysicalEndomorphism d N Nc)) :
    physicalOrderedProduct head tail = head * tail.prod := by
  induction tail generalizing head with
  | nil => simp
  | cons next tail ih =>
      rw [physicalOrderedProduct_cons, ih]
      simp only [List.prod_cons]
      change head * next * tail.prod = head * (next * tail.prod)
      rw [mul_assoc]

/-- A head weighted-row amplitude and one uniform continuation amplitude give
the exact `A * rho^n` majorant for an arbitrary ordered product, without any
loss of spatial rate. -/
theorem physicalCovarianceWeightedRowKernelBound_orderedProduct
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    (head : PhysicalEndomorphism d N Nc)
    {A rho rate : ℝ}
    (hhead : PhysicalCovarianceWeightedRowKernelBound head dist A rate)
    (tail : List (PhysicalEndomorphism d N Nc))
    (htail : ∀ next, next ∈ tail →
      PhysicalCovarianceWeightedRowKernelBound next dist rho rate) :
    PhysicalCovarianceWeightedRowKernelBound
      (physicalOrderedProduct head tail) dist
      (A * rho ^ tail.length) rate := by
  induction tail generalizing head A with
  | nil => simpa using hhead
  | cons next tail ih =>
      have hnext := htail next (by simp)
      have hcomp := physicalCovarianceWeightedRowKernelBound_comp
        dist htri hhead hnext
      have hrest : ∀ op, op ∈ tail →
          PhysicalCovarianceWeightedRowKernelBound op dist rho rate := by
        intro op hop
        exact htail op (by simp [hop])
      have hout := ih (head := head.comp next) (A := A * rho) hcomp hrest
      simpa [pow_succ', mul_assoc] using hout

/-- Pointwise fixed-rate consequence of the ordered weighted-row product.
This is the abstract `A * rho^n * exp(-mu d)` skeleton used toward CMP99
equation `(3.108)`. -/
theorem physicalCovarianceExponentialKernelBound_orderedProduct
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    (head : PhysicalEndomorphism d N Nc)
    {A rho rate : ℝ} (hrate : 0 < rate)
    (hhead : PhysicalCovarianceWeightedRowKernelBound head dist A rate)
    (tail : List (PhysicalEndomorphism d N Nc))
    (htail : ∀ next, next ∈ tail →
      PhysicalCovarianceWeightedRowKernelBound next dist rho rate) :
    PhysicalCovarianceExponentialKernelBound
      (physicalOrderedProduct head tail) dist
      (A * rho ^ tail.length) rate :=
  physicalCovarianceExponentialKernelBound_of_weightedRow
    (physicalOrderedProduct head tail) dist hrate
    (physicalCovarianceWeightedRowKernelBound_orderedProduct
      dist htri head hhead tail htail)

end

end YangMills.RG
