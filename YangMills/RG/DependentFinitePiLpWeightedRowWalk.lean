/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.DependentArrowWalk
import YangMills.RG.FinitePiLpTypedWeightedRowKernel

/-!
# Fixed-rate estimates for scale-typed finite walks

This module composes rectangular weighted-row estimates along the canonical
`Fin` scale path.  Every intermediate carrier remains in its actual type.  The
amplitudes multiply recursively while the spatial rate is fixed once for the
entire path.
-/

namespace YangMills.RG

noncomputable section

universe u

/-- A rectangular continuous linear arrow between two members of a typed
finite-site family. -/
abbrev DependentFinitePiLpArrow {n : ℕ}
    (Site : Fin (n + 1) → Type u) (g : Type*)
    [∀ r, Fintype (Site r)] [∀ r, DecidableEq (Site r)]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (r s : Fin (n + 1)) :=
  FinitePiLpField (Site r) g →L[ℝ] FinitePiLpField (Site s) g

/-- Evaluation of a dependent finite-site walk by genuine rectangular
composition. -/
noncomputable def dependentFinitePiLpWalkOperator {n : ℕ}
    (Site : Fin (n + 1) → Type u) (g : Type*)
    [∀ r, Fintype (Site r)] [∀ r, DecidableEq (Site r)]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {r s : Fin (n + 1)}
    (walk : DependentArrowWalk
      (DependentFinitePiLpArrow Site g) r s) :
    DependentFinitePiLpArrow Site g r s :=
  walk.evaluate
    (fun i => ContinuousLinearMap.id ℝ (FinitePiLpField (Site i) g))
    (fun f h => f.comp h)

/-- Evaluation respects concatenation in the physically ordered direction. -/
theorem dependentFinitePiLpWalkOperator_append {n : ℕ}
    (Site : Fin (n + 1) → Type u) (g : Type*)
    [∀ r, Fintype (Site r)] [∀ r, DecidableEq (Site r)]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {r s t : Fin (n + 1)}
    (first : DependentArrowWalk
      (DependentFinitePiLpArrow Site g) r s)
    (second : DependentArrowWalk
      (DependentFinitePiLpArrow Site g) s t) :
    dependentFinitePiLpWalkOperator Site g (first.append second) =
      (dependentFinitePiLpWalkOperator Site g second).comp
        (dependentFinitePiLpWalkOperator Site g first) := by
  exact DependentArrowWalk.evaluate_append
    (fun i => ContinuousLinearMap.id ℝ (FinitePiLpField (Site i) g))
    (fun f h => f.comp h)
    (fun f => by ext x; rfl)
    (fun f h k => by ext x; rfl)
    first second

/-- Evaluation of the canonical prefix satisfies the expected successor
recursion. -/
theorem dependentFinitePiLpWalkOperator_finSuccPrefix_succ {n : ℕ}
    (Site : Fin (n + 1) → Type u) (g : Type*)
    [∀ r, Fintype (Site r)] [∀ r, DecidableEq (Site r)]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (step : ∀ r : Fin n, DependentFinitePiLpArrow Site g r.castSucc r.succ)
    (r : Fin n) :
    dependentFinitePiLpWalkOperator Site g
        (DependentArrowWalk.finSuccPrefix step r.succ) =
      (step r).comp
        (dependentFinitePiLpWalkOperator Site g
          (DependentArrowWalk.finSuccPrefix step r.castSucc)) := by
  rw [DependentArrowWalk.finSuccPrefix_succ,
    dependentFinitePiLpWalkOperator_append]
  simp [dependentFinitePiLpWalkOperator]

/-- Recursive product of the amplitudes preceding a scale endpoint. -/
def dependentFinSuccPrefixAmplitude {n : ℕ}
    (A : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.induction 1 (fun i previous => A i * previous)

@[simp] theorem dependentFinSuccPrefixAmplitude_zero {n : ℕ}
    (A : Fin n → ℝ) :
    dependentFinSuccPrefixAmplitude A 0 = 1 :=
  rfl

@[simp] theorem dependentFinSuccPrefixAmplitude_succ {n : ℕ}
    (A : Fin n → ℝ) (r : Fin n) :
    dependentFinSuccPrefixAmplitude A r.succ =
      A r * dependentFinSuccPrefixAmplitude A r.castSucc :=
  rfl

/-- A constant one-step amplitude gives the expected power at each prefix. -/
@[simp] theorem dependentFinSuccPrefixAmplitude_const {n : ℕ}
    (A : ℝ) (r : Fin (n + 1)) :
    dependentFinSuccPrefixAmplitude (fun _ : Fin n => A) r = A ^ r.val := by
  refine Fin.induction ?_ ?_ r
  · simp
  · intro i ih
    rw [dependentFinSuccPrefixAmplitude_succ, ih]
    simp only [Fin.val_castSucc, Fin.val_succ, pow_succ]
    ring

/-- The identity walk has weighted-row amplitude one when the distance is
zero on the diagonal. -/
theorem finitePiLpTypedWeightedRowKernelBound_id {ι g : Type*}
    [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (dist : ι → ι → ℕ) {rate : ℝ} (hrate : 0 ≤ rate)
    (hdiag : ∀ x, dist x x = 0) :
    FinitePiLpTypedWeightedRowKernelBound
      (ContinuousLinearMap.id ℝ (FinitePiLpField ι g)) dist 1 rate := by
  refine ⟨zero_le_one, hrate, ?_⟩
  intro source v
  classical
  calc
    ∑ target : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖(ContinuousLinearMap.id ℝ (FinitePiLpField ι g))
              (singleFinitePiLp source v) target‖ =
        Real.exp (rate * (dist source source : ℝ)) *
          ‖(ContinuousLinearMap.id ℝ (FinitePiLpField ι g))
            (singleFinitePiLp source v) source‖ := by
      apply Fintype.sum_eq_single source
      intro target hne
      simp [singleFinitePiLp, hne]
    _ =
        Real.exp (rate * (dist source source : ℝ)) * ‖v‖ := by
      simp [singleFinitePiLp]
    _ = ‖v‖ := by simp [hdiag]
    _ ≤ 1 * ‖v‖ := by simp

set_option maxHeartbeats 800000 in
/-- A canonical scale prefix inherits the product amplitude of its consecutive
rectangular factors at one unchanged spatial rate. -/
theorem dependentFinitePiLpWalkOperator_finSuccPrefix_weightedRowKernelBound
    {n : ℕ}
    (Site : Fin (n + 1) → Type u) (g : Type*)
    [∀ r, Fintype (Site r)] [∀ r, DecidableEq (Site r)]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (dist : ∀ r s, Site s → Site r → ℕ)
    (hdiag : ∀ r x, dist r r x x = 0)
    (htri : ∀ r s t target middle source,
      dist r t target source ≤
        dist s t target middle + dist r s middle source)
    (step : ∀ r : Fin n, DependentFinitePiLpArrow Site g r.castSucc r.succ)
    (A : Fin n → ℝ) {rate : ℝ} (hrate : 0 ≤ rate)
    (hstep : ∀ r,
      FinitePiLpTypedWeightedRowKernelBound
        (step r) (dist r.castSucc r.succ) (A r) rate)
    (endpoint : Fin (n + 1)) :
    FinitePiLpTypedWeightedRowKernelBound
      (dependentFinitePiLpWalkOperator Site g
        (DependentArrowWalk.finSuccPrefix step endpoint))
      (dist 0 endpoint)
      (dependentFinSuccPrefixAmplitude A endpoint) rate := by
  refine Fin.induction ?_ ?_ endpoint
  · simpa [dependentFinitePiLpWalkOperator] using
      finitePiLpTypedWeightedRowKernelBound_id
        (dist 0 0) hrate (hdiag 0)
  · intro r ih
    rw [dependentFinitePiLpWalkOperator_finSuccPrefix_succ,
      dependentFinSuccPrefixAmplitude_succ]
    exact finitePiLpTypedWeightedRowKernelBound_comp
      (dist r.castSucc r.succ) (dist 0 r.castSucc) (dist 0 r.succ)
      (htri 0 r.castSucc r.succ)
      (hstep r) ih

/-- Full-path specialization: all `n` physical transitions compose without
loss of the chosen spatial rate. -/
theorem dependentFinitePiLpWalkOperator_finSuccPath_weightedRowKernelBound
    {n : ℕ}
    (Site : Fin (n + 1) → Type u) (g : Type*)
    [∀ r, Fintype (Site r)] [∀ r, DecidableEq (Site r)]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (dist : ∀ r s, Site s → Site r → ℕ)
    (hdiag : ∀ r x, dist r r x x = 0)
    (htri : ∀ r s t target middle source,
      dist r t target source ≤
        dist s t target middle + dist r s middle source)
    (step : ∀ r : Fin n, DependentFinitePiLpArrow Site g r.castSucc r.succ)
    (A : Fin n → ℝ) {rate : ℝ} (hrate : 0 ≤ rate)
    (hstep : ∀ r,
      FinitePiLpTypedWeightedRowKernelBound
        (step r) (dist r.castSucc r.succ) (A r) rate) :
    FinitePiLpTypedWeightedRowKernelBound
      (dependentFinitePiLpWalkOperator Site g
        (DependentArrowWalk.finSuccPath step))
      (dist 0 (Fin.last n))
      (dependentFinSuccPrefixAmplitude A (Fin.last n)) rate :=
  dependentFinitePiLpWalkOperator_finSuccPrefix_weightedRowKernelBound
    Site g dist hdiag htri step A hrate hstep (Fin.last n)

end

end YangMills.RG
