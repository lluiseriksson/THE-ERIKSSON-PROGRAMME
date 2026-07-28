/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3d: the Osterwalder-Seiler identification for the Z_2 chain, and the exact
two-point function of the measure.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 8 (five pre-registered judges).
-/

import Mathlib
import YangMills.OS.Z2Transfer

/-!
# O-3d — the identification, and the endpoint

## The point of this module

O-3c built the transfer operator from the Gibbs weight and proved it has a
spectral gap.  What was missing — and what Addendum 511 named as the load
bearing gap — is the IDENTIFICATION: the statement that the expectation taken
in the MEASURE equals a matrix element of that operator.  Without it the two
halves of the chain sit next to each other rather than joined.

Everything on the measure side of this file is defined from `Real.exp` and the
bond sign, and from nothing else.  No transfer operator, no `z2A`, no `z2B`
occurs in `z2Bond`, `z2PathWeight`, `z2Partition`, `z2PathSum` or `z2Expect`.
That separation is the whole content: two independently defined objects are
then PROVED to agree.

## What comes out

* `z2Partition_eq` — the partition function is exactly `2·(e^β+e^{-β})^n`,
  computed, not assumed.
* `z2_identification` — for every `n` and every pair of observables,
  `E_n[conj A(σ_0)·B(σ_n)] = ⟪A·Ω, T^n (B·Ω)⟫`.
* `z2_two_point_tanh` — the endpoint: the two-point function of the sign
  observable is exactly `(tanh β)^n`.  This is a statement purely about the
  MEASURE whose rate is the gap of O-3c.
* `z2_one_point_sign_eq_zero` — the one-point function vanishes, so the
  connected two-point function coincides with the full one.

## Scope, stated plainly

One `Z_2` variable per time slice, so `T` is `2 x 2` and the spatial slice is a
point.  A lattice with spatial extent is NOT treated.  Fixed finite size; NOT
volume-uniform.  The pairing here is definite, so the GNS quotient is the
identity and remains ABSENT rather than closed.  `Z_N` for `N > 2` untouched.
The mathematics of the one-dimensional chain is textbook; what is new here is
that every interface of the chain is a machine-checked theorem.  Nothing in
this module is a claim about `SU(N)`, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

open scoped InnerProductSpace

/-! ## §1  The Boltzmann weights — physics input, no operator anywhere -/

/-- The bond sign: `+1` when the two spins agree, `-1` when they differ. -/
def z2Sign (i j : Fin 2) : ℝ := if i = j then 1 else -1

theorem z2Sign_symm (i j : Fin 2) : z2Sign i j = z2Sign j i := by
  unfold z2Sign
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- The Boltzmann weight of one bond.  `Real.exp` and the sign; nothing else. -/
noncomputable def z2Bond (β : ℝ) (i j : Fin 2) : ℝ := Real.exp (β * z2Sign i j)

theorem z2Bond_symm (β : ℝ) (i j : Fin 2) : z2Bond β i j = z2Bond β j i := by
  unfold z2Bond; rw [z2Sign_symm]

theorem z2Bond_pos (β : ℝ) (i j : Fin 2) : 0 < z2Bond β i j := Real.exp_pos _

/-- The Boltzmann weight of a whole path of `n` bonds. -/
noncomputable def z2PathWeight (β : ℝ) {n : ℕ} (σ : Fin (n + 1) → Fin 2) : ℝ :=
  ∏ t : Fin n, z2Bond β (σ t.castSucc) (σ t.succ)

/-- The partition function. -/
noncomputable def z2Partition (β : ℝ) (n : ℕ) : ℝ :=
  ∑ σ : Fin (n + 1) → Fin 2, z2PathWeight β σ

/-- The unnormalised two-point sum. -/
noncomputable def z2PathSum (β : ℝ) (n : ℕ) (A B : Fin 2 → ℂ) : ℂ :=
  ∑ σ : Fin (n + 1) → Fin 2,
    (starRingEnd ℂ) (A (σ 0)) * B (σ (Fin.last n)) * ((z2PathWeight β σ : ℝ) : ℂ)

/-- **The expectation in the measure.**  Defined from the Boltzmann weights
alone; no operator occurs anywhere in this definition or in the definitions it
depends on. -/
noncomputable def z2Expect (β : ℝ) (n : ℕ) (A B : Fin 2 → ℂ) : ℂ :=
  z2PathSum β n A B / ((z2Partition β n : ℝ) : ℂ)

/-! ## §2  The dictionary between observables and vectors -/

/-- An observable, read as a vector of the Hilbert space. -/
noncomputable def z2Vec (A : Fin 2 → ℂ) : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 A

theorem z2Vec_apply (A : Fin 2 → ℂ) (i : Fin 2) : (z2Vec A).ofLp i = A i := rfl

/-- The observable multiplied by the vacuum — the vector `AΩ` of the
Osterwalder-Seiler dictionary. -/
noncomputable def z2Obs (A : Fin 2 → ℂ) : EuclideanSpace ℂ (Fin 2) :=
  ((invSqrtTwo : ℝ) : ℂ) • z2Vec A

/-! ## §3  From the bond weight to the transfer operator -/

/-- The normalised bond weight is the transfer matrix entry.  This is the ONLY
place where the two sides meet. -/
theorem z2Bond_eq (β : ℝ) (i j : Fin 2) :
    z2Bond β i j = z2Norm β * (if i = j then z2A β else z2B β) := by
  have hn : z2Norm β ≠ 0 := (z2Norm_pos β).ne'
  by_cases h : i = j
  · rw [if_pos h]
    unfold z2Bond z2Sign z2A
    rw [if_pos h, mul_one]
    field_simp
  · rw [if_neg h]
    unfold z2Bond z2Sign z2B
    rw [if_neg h, show β * (-1 : ℝ) = -β by ring]
    field_simp

/-- One application of the unnormalised transfer kernel to an observable. -/
noncomputable def z2Act (β : ℝ) (A : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => ∑ j, ((z2Bond β i j : ℝ) : ℂ) * A j

/-- The unnormalised kernel is `z2Norm β` times the transfer operator. -/
theorem z2Vec_z2Act (β : ℝ) (A : Fin 2 → ℂ) :
    z2Vec (z2Act β A) = ((z2Norm β : ℝ) : ℂ) • z2TransferOp β (z2Vec A) := by
  refine PiLp.ext fun i => ?_
  rw [z2Vec_apply, PiLp.smul_apply, z2TransferOp_apply, z2Vec_apply, z2Vec_apply]
  show (∑ j, ((z2Bond β i j : ℝ) : ℂ) * A j) = _
  rw [Fin.sum_univ_two]
  simp only [z2Bond_eq, Complex.ofReal_mul, smul_eq_mul]
  fin_cases i <;> · norm_num; ring

/-! ## §4  The induction: sum over paths equals iterated kernel -/

/-- Splitting the sum over paths at the first spin. -/
theorem z2_sum_cons (n : ℕ) (F : (Fin (n + 2) → Fin 2) → ℂ) :
    ∑ σ : Fin (n + 2) → Fin 2, F σ
      = ∑ s : Fin 2, ∑ τ : Fin (n + 1) → Fin 2, F (Fin.cons s τ) := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 2) => Fin 2).sum_comp F, Fintype.sum_prod_type]
  rfl

/-- The weight of a path splits off its first bond. -/
theorem z2PathWeight_cons (β : ℝ) (n : ℕ) (s : Fin 2) (τ : Fin (n + 1) → Fin 2) :
    z2PathWeight β (Fin.cons s τ : Fin (n + 2) → Fin 2)
      = z2Bond β s (τ 0) * z2PathWeight β τ := by
  unfold z2PathWeight
  rw [Fin.prod_univ_succ]
  congr 1

theorem z2PathSum_zero (β : ℝ) (A B : Fin 2 → ℂ) :
    z2PathSum β 0 A B = ∑ i, (starRingEnd ℂ) (A i) * B i := by
  unfold z2PathSum
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold z2PathWeight
  simp

/-- **The induction step.**  One bond is absorbed into the observable. -/
theorem z2PathSum_succ (β : ℝ) (n : ℕ) (A B : Fin 2 → ℂ) :
    z2PathSum β (n + 1) A B = z2PathSum β n (z2Act β A) B := by
  unfold z2PathSum
  rw [z2_sum_cons, Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hact : (starRingEnd ℂ) (z2Act β A (τ 0))
      = ∑ s, ((z2Bond β s (τ 0) : ℝ) : ℂ) * (starRingEnd ℂ) (A s) := by
    unfold z2Act
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_mul, Complex.conj_ofReal, z2Bond_symm]
  rw [hact, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show (Fin.last (n + 1)) = (Fin.last n).succ from rfl]
  simp only [Fin.cons_zero, Fin.cons_succ, z2PathWeight_cons]
  push_cast
  ring

theorem z2PathSum_eq_iterate (β : ℝ) (n : ℕ) (A B : Fin 2 → ℂ) :
    z2PathSum β n A B = ∑ i, (starRingEnd ℂ) ((z2Act β)^[n] A i) * B i := by
  induction n generalizing A with
  | zero => simpa using z2PathSum_zero β A B
  | succ n ih => rw [z2PathSum_succ, ih, Function.iterate_succ_apply]

/-- Iterating the unnormalised kernel is `z2Norm^n` times the operator power. -/
theorem z2Vec_iterate (β : ℝ) (n : ℕ) (A : Fin 2 → ℂ) :
    z2Vec ((z2Act β)^[n] A)
      = (((z2Norm β : ℝ) : ℂ) ^ n) • ((z2TransferOp β) ^ n) (z2Vec A) := by
  induction n generalizing A with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', z2Vec_z2Act, ih, map_smul, smul_smul,
        pow_succ' ((z2Norm β : ℝ) : ℂ) n, pow_succ' (z2TransferOp β) n,
        ContinuousLinearMap.mul_apply]

/-! ## §5  The partition function, computed -/

theorem z2Vac_eq_obs_one : z2Obs (fun _ => (1 : ℂ)) = z2Vac := by
  refine PiLp.ext fun i => ?_
  show ((invSqrtTwo : ℝ) : ℂ) * (1 : ℂ) = z2Vac.ofLp i
  rw [z2Vac_apply, mul_one]

theorem z2TransferOp_pow_z2Vac (β : ℝ) (n : ℕ) :
    ((z2TransferOp β) ^ n) z2Vac = z2Vac := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, z2TransferOp_fix]

/-- **The partition function, computed exactly.** -/
theorem z2Partition_eq (β : ℝ) (n : ℕ) :
    z2Partition β n = 2 * (z2Norm β) ^ n := by
  have key : ((z2Partition β n : ℝ) : ℂ) = ((2 * (z2Norm β) ^ n : ℝ) : ℂ) := by
    have h : z2PathSum β n (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))
        = ((z2Partition β n : ℝ) : ℂ) := by
      unfold z2PathSum z2Partition
      push_cast
      simp
    rw [← h, z2PathSum_eq_iterate]
    have hv : z2Vec ((z2Act β)^[n] (fun _ => (1 : ℂ)))
        = (((z2Norm β : ℝ) : ℂ) ^ n) • ((z2TransferOp β) ^ n) (z2Vec fun _ => (1 : ℂ)) :=
      z2Vec_iterate β n _
    have hone : z2Vec (fun _ => (1 : ℂ)) = ((Real.sqrt 2 : ℝ) : ℂ) • z2Vac := by
      refine PiLp.ext fun i => ?_
      rw [z2Vec_apply, PiLp.smul_apply, z2Vac_apply, smul_eq_mul, ← Complex.ofReal_mul]
      unfold invSqrtTwo
      rw [mul_inv_cancel₀ (by positivity : (Real.sqrt 2 : ℝ) ≠ 0)]
      norm_num
    rw [hone, map_smul, z2TransferOp_pow_z2Vac] at hv
    have hcoord : ∀ i, ((z2Act β)^[n] (fun _ => (1 : ℂ))) i
        = (((z2Norm β : ℝ) : ℂ) ^ n) * (((Real.sqrt 2 : ℝ) : ℂ) * ((invSqrtTwo : ℝ) : ℂ)) := by
      intro i
      have := congrArg (fun w => (w : EuclideanSpace ℂ (Fin 2)).ofLp i) hv
      simpa [z2Vec_apply, z2Vac_apply, mul_assoc] using this
    have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) * ((invSqrtTwo : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      unfold invSqrtTwo
      rw [mul_inv_cancel₀ (by positivity : (Real.sqrt 2 : ℝ) ≠ 0)]
      norm_num
    simp only [hcoord, hsqrt, mul_one, map_pow, Complex.conj_ofReal, Fin.sum_univ_two,
      mul_one]
    push_cast
    ring
  exact_mod_cast key

theorem z2Partition_ne_zero (β : ℝ) (n : ℕ) : z2Partition β n ≠ 0 := by
  rw [z2Partition_eq]
  have := z2Norm_pos β
  positivity

/-! ## §6  THE IDENTIFICATION -/

/-- **The Osterwalder-Seiler identification for the `Z_2` chain.**

The left-hand side is the expectation in the measure defined by the Boltzmann
weights; no operator occurs in its definition.  The right-hand side is a matrix
element of the transfer operator of O-3c.  They are equal for every `n` and
every pair of observables. -/
theorem z2_identification (β : ℝ) (n : ℕ) (A B : Fin 2 → ℂ) :
    z2Expect β n A B = ⟪z2Obs A, ((z2TransferOp β) ^ n) (z2Obs B)⟫_ℂ := by
  have hself : IsSelfAdjoint ((z2TransferOp β) ^ n) :=
    (z2TransferOp_selfAdjoint β).pow n
  have hsym : ∀ x y : EuclideanSpace ℂ (Fin 2),
      ⟪((z2TransferOp β) ^ n) x, y⟫_ℂ = ⟪x, ((z2TransferOp β) ^ n) y⟫_ℂ := by
    intro x y
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself) x y
    simpa only [ContinuousLinearMap.coe_coe] using h
  -- the path sum, in operator form
  have hpath : z2PathSum β n A B
      = ((z2Norm β : ℝ) : ℂ) ^ n * ⟪z2Vec A, ((z2TransferOp β) ^ n) (z2Vec B)⟫_ℂ := by
    rw [z2PathSum_eq_iterate]
    have hv := z2Vec_iterate β n A
    have hco : ∀ i, ((z2Act β)^[n] A) i
        = ((z2Norm β : ℝ) : ℂ) ^ n * (((z2TransferOp β) ^ n) (z2Vec A)).ofLp i := by
      intro i
      have := congrArg (fun w => (w : EuclideanSpace ℂ (Fin 2)).ofLp i) hv
      simpa [z2Vec_apply] using this
    simp only [hco, map_mul, map_pow, Complex.conj_ofReal, mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    rw [← hsym]
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, z2Vec_apply]
    ring
  rw [z2Expect, hpath, z2Partition_eq]
  have hobs : ⟪z2Obs A, ((z2TransferOp β) ^ n) (z2Obs B)⟫_ℂ
      = (((invSqrtTwo : ℝ) : ℂ) * ((invSqrtTwo : ℝ) : ℂ))
        * ⟪z2Vec A, ((z2TransferOp β) ^ n) (z2Vec B)⟫_ℂ := by
    unfold z2Obs
    rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  rw [hobs, invSqrtTwo_sq_complex]
  have hz : ((z2Norm β : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (z2Norm_pos β)
  push_cast
  field_simp

/-! ## §7  THE ENDPOINT — a statement purely about the measure -/

/-- The sign observable: `+1` on the first configuration, `-1` on the second. -/
def z2SignObs : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1

theorem z2Vec_signObs_eigen (β : ℝ) :
    z2TransferOp β (z2Vec z2SignObs) = ((z2A β - z2B β : ℝ) : ℂ) • z2Vec z2SignObs := by
  refine PiLp.ext fun i => ?_
  rw [z2TransferOp_apply, PiLp.smul_apply, z2Vec_apply, z2Vec_apply]
  unfold z2SignObs
  fin_cases i <;> · simp only [smul_eq_mul]; norm_num; ring

theorem z2TransferOp_pow_signObs (β : ℝ) (n : ℕ) :
    ((z2TransferOp β) ^ n) (z2Vec z2SignObs)
      = (((z2A β - z2B β : ℝ) : ℂ) ^ n) • z2Vec z2SignObs := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, z2Vec_signObs_eigen,
        smul_smul, pow_succ']
      congr 1
      ring

/-- **The endpoint.**  The two-point function of the sign observable in the
measure is exactly `(a - b)^n`.  The left-hand side mentions no operator; the
proof goes through one. -/
theorem z2_two_point_exact (β : ℝ) (n : ℕ) :
    z2Expect β n z2SignObs z2SignObs = ((z2A β - z2B β : ℝ) : ℂ) ^ n := by
  rw [z2_identification]
  unfold z2Obs
  rw [map_smul, z2TransferOp_pow_signObs, inner_smul_left, inner_smul_right,
    inner_smul_right, Complex.conj_ofReal]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, z2Vec_apply]
  unfold z2SignObs
  norm_num
  linear_combination (2 * (((z2A β : ℝ) : ℂ) - ((z2B β : ℝ) : ℂ)) ^ n) * invSqrtTwo_sq_complex

/-- **The endpoint, named.**  The rate is `tanh β` — the gap of O-3c. -/
theorem z2_two_point_tanh (β : ℝ) (n : ℕ) :
    z2Expect β n z2SignObs z2SignObs = ((Real.tanh β : ℝ) : ℂ) ^ n := by
  rw [z2_two_point_exact, z2A_sub_z2B_eq_tanh]

/-- The one-point function vanishes, so the connected two-point function of the
sign observable coincides with the full one. -/
theorem z2_one_point_sign_eq_zero (β : ℝ) (n : ℕ) :
    z2Expect β n z2SignObs (fun _ => (1 : ℂ)) = 0 := by
  rw [z2_identification, z2Vac_eq_obs_one, z2TransferOp_pow_z2Vac]
  unfold z2Obs
  rw [inner_smul_left, Complex.conj_ofReal]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, z2Vec_apply,
    z2Vac_apply]
  unfold z2SignObs
  norm_num

/-- **Exponential decay of a correlation of the MEASURE**, at the rate that is
the spectral gap of O-3c. -/
theorem z2_measure_clustering {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    ‖z2Expect β n z2SignObs z2SignObs‖ = (Real.tanh β) ^ n := by
  rw [z2_two_point_tanh, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by rw [← z2A_sub_z2B_eq_tanh]; exact z2A_sub_z2B_nonneg hβ)]

/-- The rate is strictly below one: the correlation genuinely decays. -/
theorem z2_measure_rate_lt_one (β : ℝ) : Real.tanh β < 1 := by
  rw [← z2A_sub_z2B_eq_tanh]; exact z2A_sub_z2B_lt_one β

/-- **Non-vacuity of the identification** (judge 4): at `β > 0` and every `n`
both sides are nonzero, and they depend on `n`. -/
theorem z2_two_point_ne_zero {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    z2Expect β n z2SignObs z2SignObs ≠ 0 := by
  rw [z2_two_point_tanh]
  have h : 0 < Real.tanh β := by
    rw [← z2A_sub_z2B_eq_tanh]
    unfold z2A z2B
    rw [div_sub_div_same, lt_div_iff₀ (z2Norm_pos β)]
    have : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
    linarith
  simp only [ne_eq, pow_eq_zero_iff', Complex.ofReal_eq_zero, not_and]
  intro hc
  exact absurd hc (ne_of_gt h)

/-! ## §8  Why the quotient step is the identity, and what `complete' means

The Osterwalder-Seiler reconstruction quotients by the null space of the
pairing.  Here that step exists and is the identity, and this section proves
that rather than asserting it.  The `n = 0` instance of `z2_identification`
IS the pairing of this system, so its non-degeneracy is exactly the
statement that the null space is zero.  Consequently `A ↦ AΩ` is the
reconstruction map, and the general-`n` identification says that
`z2TransferOp` implements the time translation on its image. -/

/-- The reconstruction map `A ↦ AΩ` is injective. -/
theorem z2Obs_injective : Function.Injective z2Obs := by
  intro A B h
  funext i
  have hi := congrArg (fun w => (w : EuclideanSpace ℂ (Fin 2)).ofLp i) h
  simp only [z2Obs, PiLp.smul_apply, z2Vec_apply, smul_eq_mul] at hi
  have hne : ((invSqrtTwo : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt invSqrtTwo_pos
  exact mul_left_cancel₀ hne hi

theorem z2Obs_zero : z2Obs (fun _ => (0 : ℂ)) = 0 := by
  refine PiLp.ext fun i => ?_
  show ((invSqrtTwo : ℝ) : ℂ) * (0 : ℂ) = _
  simp

/-- **The pairing is non-degenerate, so the Osterwalder-Seiler quotient is
the identity.**  The hypothesis is the `n = 0` instance of the
identification, i.e. the self-pairing of the observable in the measure. -/
theorem z2_pairing_nondegenerate (β : ℝ) {A : Fin 2 → ℂ}
    (h : z2Expect β 0 A A = 0) : A = fun _ => 0 := by
  rw [z2_identification] at h
  simp only [pow_zero, ContinuousLinearMap.one_apply] at h
  have hz : z2Obs A = 0 := inner_self_eq_zero.mp h
  exact z2Obs_injective (hz.trans z2Obs_zero.symm)

end YangMills.OS
