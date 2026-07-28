/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3c: the transfer operator of the Z_2 system, built from the Wilson weights,
and its spectral gap.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 6.
-/

import Mathlib
import YangMills.OS.SharpBridge
import YangMills.OS.WilsonCharCombo

/-!
# O-3c — the transfer operator, and the gap, from the Boltzmann weights

## The point of this module

The O-1 arc proved a criterion about transfer operators, and every witness it
exhibited was of the form `r·1 + (1-r)P` — an operator built *from* the
conclusion.  Both the adversarial audit and the external review named that as
the arc's remaining weakness.  This module removes it.

The operator is
```
  z2TransferOp β  =  a β • 1  +  b β • swapOp,
```
where `swapOp` is the geometric exchange of the two configurations of `Z_2` and
`a β`, `b β` are the **normalised Wilson weights** `e^β/(e^β+e^{-β})` and
`e^{-β}/(e^β+e^{-β})`.  No eigenvector and no spectral datum occurs in the
definition: it is the normalised transfer matrix

  `1/(e^β + e^{-β}) · [[e^β, e^{-β}], [e^{-β}, e^β]]`

of the `Z_2` gauge system, read off the Gibbs weight.  The gap is then a
theorem about it, not an input to it.

## What comes out

* `z2TransferOp_vacuumTransfer` — it is transfer data for the uniform vacuum;
  the fixing of the vacuum is a consequence of `a + b = 1`, i.e. of
  normalisation, not an assumption.
* `z2TransferOp_gap` — the projected operator has norm at most `a - b`, which
  is `tanh β`, and `z2_gap_rate_lt_one` records that this is `< 1`.
* `z2_clustering_of_transfer` — feeding that into the criterion of the
  companion development gives exponential decay of the connected two-point
  function at that rate, for an operator that came from the measure.

## Scope, stated plainly

This is the `Z_2` system whose spatial slice is a single variable, so its
transfer operator is a `2 x 2` matrix.  A lattice with spatial extent has a
transfer operator on a larger space and is **not** treated here.  The gap is at
fixed finite size; it is *not* a volume-uniform statement, and for a system of
this size the question does not arise.  There is no Gelfand--Naimark--Segal
quotient here either: the pairing of this system is already definite, so the
quotient is the identity and nothing is gained by naming it.  Nothing in this
module is a claim about `SU(N)`, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

open scoped InnerProductSpace

/-- Abbreviation for the real number `1/√2`, kept as a real so that every
coercion into `ℂ` has the same shape. -/
noncomputable def invSqrtTwo : ℝ := (Real.sqrt 2)⁻¹

theorem invSqrtTwo_pos : 0 < invSqrtTwo := by
  unfold invSqrtTwo; positivity

theorem invSqrtTwo_sq : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  unfold invSqrtTwo
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem invSqrtTwo_sq_complex :
    ((invSqrtTwo : ℝ) : ℂ) * ((invSqrtTwo : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_mul, invSqrtTwo_sq]
  norm_num

/-! ## The geometric swap of the two `Z_2` configurations -/

/-- Exchange of the two configurations, as a linear map. -/
noncomputable def swapLin : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := fun v => WithLp.toLp 2 (fun i => v.ofLp (1 - i))
  map_add' := by intro u v; rfl
  map_smul' := by intro c v; rfl

/-- The same, as a continuous linear map (automatic in finite dimension). -/
noncomputable def swapOp : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap swapLin

theorem swapOp_apply (v : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    (swapOp v).ofLp i = v.ofLp (1 - i) := rfl

theorem swapOp_zero (v : EuclideanSpace ℂ (Fin 2)) : (swapOp v).ofLp 0 = v.ofLp 1 := rfl

theorem swapOp_one (v : EuclideanSpace ℂ (Fin 2)) : (swapOp v).ofLp 1 = v.ofLp 0 := rfl

theorem swapOp_selfAdjoint : IsSelfAdjoint swapOp := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro v w
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  show w.ofLp 0 * (starRingEnd ℂ) (v.ofLp 1) + w.ofLp 1 * (starRingEnd ℂ) (v.ofLp 0)
      = w.ofLp 1 * (starRingEnd ℂ) (v.ofLp 0) + w.ofLp 0 * (starRingEnd ℂ) (v.ofLp 1)
  ring

/-! ## The normalised Wilson weights -/

/-- The normalising factor of the `Z_2` Wilson weights. -/
noncomputable def z2Norm (β : ℝ) : ℝ := Real.exp β + Real.exp (-β)

theorem z2Norm_pos (β : ℝ) : 0 < z2Norm β := by
  unfold z2Norm; positivity

/-- Diagonal entry of the normalised transfer matrix. -/
noncomputable def z2A (β : ℝ) : ℝ := Real.exp β / z2Norm β

/-- Off-diagonal entry of the normalised transfer matrix. -/
noncomputable def z2B (β : ℝ) : ℝ := Real.exp (-β) / z2Norm β

theorem z2A_add_z2B (β : ℝ) : z2A β + z2B β = 1 := by
  unfold z2A z2B z2Norm
  field_simp

theorem z2A_sub_z2B_nonneg {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ z2A β - z2B β := by
  unfold z2A z2B
  rw [div_sub_div_same, le_div_iff₀ (z2Norm_pos β)]
  have : Real.exp (-β) ≤ Real.exp β := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- The rate is exactly `tanh β`.  The docstrings of this module name that
value, so it is proved here rather than asserted in prose. -/
theorem z2A_sub_z2B_eq_tanh (β : ℝ) : z2A β - z2B β = Real.tanh β := by
  unfold z2A z2B z2Norm
  rw [div_sub_div_same, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h : Real.exp β + Real.exp (-β) ≠ 0 := by positivity
  field_simp

theorem z2A_sub_z2B_lt_one (β : ℝ) : z2A β - z2B β < 1 := by
  unfold z2A z2B
  rw [div_sub_div_same, div_lt_one (z2Norm_pos β)]
  unfold z2Norm
  have : 0 < Real.exp (-β) := Real.exp_pos _
  linarith

/-! ## The transfer operator and its vacuum -/

/-- **The transfer operator of the `Z_2` system, read off the Gibbs weight.** -/
noncomputable def z2TransferOp (β : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (z2A β : ℂ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    + (z2B β : ℂ) • swapOp

/-- The vacuum: the uniform configuration vector. -/
noncomputable def z2Vac : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun _ => ((invSqrtTwo : ℝ) : ℂ))

theorem z2Vac_apply (i : Fin 2) : z2Vac.ofLp i = ((invSqrtTwo : ℝ) : ℂ) := rfl

theorem z2Vac_norm : ‖z2Vac‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [z2Vac_apply, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos invSqrtTwo_pos]
  rw [show invSqrtTwo ^ 2 + invSqrtTwo ^ 2 = 2 * (invSqrtTwo * invSqrtTwo) by ring,
    invSqrtTwo_sq]
  norm_num

theorem swapOp_z2Vac : swapOp z2Vac = z2Vac := by
  refine PiLp.ext fun i => ?_
  rw [swapOp_apply, z2Vac_apply, z2Vac_apply]

/-- The inner product against the vacuum. -/
theorem inner_z2Vac (v : EuclideanSpace ℂ (Fin 2)) :
    (⟪z2Vac, v⟫_ℂ) = ((invSqrtTwo : ℝ) : ℂ) * (v.ofLp 0 + v.ofLp 1) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, z2Vac_apply, RCLike.inner_apply,
    Complex.conj_ofReal]
  ring

/-- The transfer operator fixes the vacuum — a consequence of `a + b = 1`. -/
theorem z2TransferOp_fix (β : ℝ) : z2TransferOp β z2Vac = z2Vac := by
  unfold z2TransferOp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, swapOp_z2Vac, ← add_smul]
  rw [show ((z2A β : ℂ) + (z2B β : ℂ)) = ((z2A β + z2B β : ℝ) : ℂ) by push_cast; ring,
    z2A_add_z2B]
  simp

/-- Coordinates of the transfer operator. -/
theorem z2TransferOp_apply (β : ℝ) (v : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    (z2TransferOp β v).ofLp i
      = (z2A β : ℂ) * v.ofLp i + (z2B β : ℂ) * v.ofLp (1 - i) := by
  show ((z2A β : ℂ) • v + (z2B β : ℂ) • swapOp v).ofLp i = _
  rw [PiLp.add_apply]
  rfl

theorem z2TransferOp_selfAdjoint (β : ℝ) : IsSelfAdjoint (z2TransferOp β) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro v w
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    ContinuousLinearMap.coe_coe, z2TransferOp_apply, map_add, map_mul,
    Complex.conj_ofReal]
  show w.ofLp 0 * ((z2A β : ℂ) * (starRingEnd ℂ) (v.ofLp 0)
        + (z2B β : ℂ) * (starRingEnd ℂ) (v.ofLp 1))
      + w.ofLp 1 * ((z2A β : ℂ) * (starRingEnd ℂ) (v.ofLp 1)
        + (z2B β : ℂ) * (starRingEnd ℂ) (v.ofLp 0))
      = ((z2A β : ℂ) * w.ofLp 0 + (z2B β : ℂ) * w.ofLp 1) * (starRingEnd ℂ) (v.ofLp 0)
      + ((z2A β : ℂ) * w.ofLp 1 + (z2B β : ℂ) * w.ofLp 0) * (starRingEnd ℂ) (v.ofLp 1)
  ring

/-- **The transfer operator is transfer data for the uniform vacuum.** -/
theorem z2TransferOp_vacuumTransfer (β : ℝ) :
    VacuumTransferC (z2TransferOp β) z2Vac where
  selfAdjoint := z2TransferOp_selfAdjoint β
  unit := z2Vac_norm
  fix := z2TransferOp_fix β

/-! ## The gap -/

/-- Coordinates of the projected transfer operator. -/
theorem z2Projected_apply (β : ℝ) (v : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    (projectedTransferC (z2TransferOp β) z2Vac v).ofLp i
      = (z2A β : ℂ) * v.ofLp i + (z2B β : ℂ) * v.ofLp (1 - i)
        - (⟪z2Vac, v⟫_ℂ) * ((invSqrtTwo : ℝ) : ℂ) := by
  show ((z2TransferOp β) v - (⟪z2Vac, v⟫_ℂ) • z2Vac).ofLp i = _
  rw [PiLp.sub_apply, z2TransferOp_apply]
  rfl

/-- **The key identity.**  The projected transfer operator acts as `a - b` times
the projection off the vacuum.  Proved componentwise, using only `a + b = 1`. -/
theorem z2Projected_eq (β : ℝ) (v : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    (projectedTransferC (z2TransferOp β) z2Vac v).ofLp i
      = ((z2A β - z2B β : ℝ) : ℂ) * (v.ofLp i - (v.ofLp 0 + v.ofLp 1) / 2) := by
  have hsum : ((z2A β : ℂ)) + ((z2B β : ℂ)) = 1 := by
    rw [show ((z2A β : ℂ) + (z2B β : ℂ)) = ((z2A β + z2B β : ℝ) : ℂ) by push_cast; ring,
      z2A_add_z2B]
    norm_num
  have hvac : (⟪z2Vac, v⟫_ℂ) * ((invSqrtTwo : ℝ) : ℂ) = (v.ofLp 0 + v.ofLp 1) / 2 := by
    rw [inner_z2Vac, mul_comm ((invSqrtTwo : ℝ) : ℂ) (v.ofLp 0 + v.ofLp 1), mul_assoc,
      invSqrtTwo_sq_complex]
    ring
  have hb : ((z2B β : ℝ) : ℂ) = 1 - ((z2A β : ℝ) : ℂ) := by
    have h : (z2B β : ℝ) = 1 - z2A β := by
      have := z2A_add_z2B β; linarith
    rw [h]; push_cast; ring
  fin_cases i <;>
    · rw [z2Projected_apply, hvac]
      push_cast
      rw [hb]
      ring

/-- **The gap.**  The projected transfer operator has norm at most `a - b`. -/
theorem z2TransferOp_gap {β : ℝ} (hβ : 0 ≤ β) :
    ‖projectedTransferC (z2TransferOp β) z2Vac‖ ≤ z2A β - z2B β := by
  refine ContinuousLinearMap.opNorm_le_bound _ (z2A_sub_z2B_nonneg hβ) fun v => ?_
  have hcomp : ∀ i : Fin 2,
      ‖(projectedTransferC (z2TransferOp β) z2Vac v).ofLp i‖
        = (z2A β - z2B β) * ‖v.ofLp i - (v.ofLp 0 + v.ofLp 1) / 2‖ := by
    intro i
    rw [z2Projected_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (z2A_sub_z2B_nonneg hβ)]
  have hv : ‖v‖ ^ 2 = ‖v.ofLp 0‖ ^ 2 + ‖v.ofLp 1‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  have hQ : ‖v.ofLp 0 - (v.ofLp 0 + v.ofLp 1) / 2‖ ^ 2
      + ‖v.ofLp 1 - (v.ofLp 0 + v.ofLp 1) / 2‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hv, show v.ofLp 0 - (v.ofLp 0 + v.ofLp 1) / 2 = (v.ofLp 0 - v.ofLp 1) / 2 by ring,
      show v.ofLp 1 - (v.ofLp 0 + v.ofLp 1) / 2 = -((v.ofLp 0 - v.ofLp 1) / 2) by ring,
      norm_neg]
    have hd : ‖(v.ofLp 0 - v.ofLp 1) / 2‖ ^ 2 = ‖v.ofLp 0 - v.ofLp 1‖ ^ 2 / 4 := by
      rw [norm_div]
      norm_num
      ring
    rw [hd]
    have htri : ‖v.ofLp 0 - v.ofLp 1‖ ≤ ‖v.ofLp 0‖ + ‖v.ofLp 1‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (v.ofLp 0), norm_nonneg (v.ofLp 1),
      norm_nonneg (v.ofLp 0 - v.ofLp 1), sq_nonneg (‖v.ofLp 0‖ - ‖v.ofLp 1‖)]
  rw [EuclideanSpace.norm_eq,
    show (∑ i : Fin 2, ‖(projectedTransferC (z2TransferOp β) z2Vac v).ofLp i‖ ^ 2)
      = (z2A β - z2B β) ^ 2 * (‖v.ofLp 0 - (v.ofLp 0 + v.ofLp 1) / 2‖ ^ 2
          + ‖v.ofLp 1 - (v.ofLp 0 + v.ofLp 1) / 2‖ ^ 2) by
      rw [Fin.sum_univ_two, hcomp 0, hcomp 1]; ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (z2A_sub_z2B_nonneg hβ)]
  refine mul_le_mul_of_nonneg_left ?_ (z2A_sub_z2B_nonneg hβ)
  calc Real.sqrt (‖v.ofLp 0 - (v.ofLp 0 + v.ofLp 1) / 2‖ ^ 2
        + ‖v.ofLp 1 - (v.ofLp 0 + v.ofLp 1) / 2‖ ^ 2)
      ≤ Real.sqrt (‖v‖ ^ 2) := Real.sqrt_le_sqrt hQ
    _ = ‖v‖ := Real.sqrt_sq (norm_nonneg v)

/-- **The chain closes.**  The transfer operator built from the `Z_2` Wilson
weights satisfies the clustering criterion of the companion development at rate
`a - b = tanh β`: the connected two-point function decays exponentially, and the
operator came from the measure rather than from the conclusion. -/
theorem z2_clustering_of_transfer {β : ℝ} (hβ : 0 ≤ β) (v : EuclideanSpace ℂ (Fin 2)) :
    ∃ C : ℝ, ∀ n : ℕ,
      ‖connCorrC (z2TransferOp β) z2Vac v n‖ ≤ C * (z2A β - z2B β) ^ n :=
  ⟨2 * ‖v‖ ^ 2, fun n =>
    connCorrC_le_of_gap (z2TransferOp_vacuumTransfer β) (z2TransferOp_gap hβ) v n⟩

/-- The rate is strictly below one, so the mass `-log (a-b)` is strictly
positive: at fixed finite size the system has a gap. -/
theorem z2_gap_rate_lt_one (β : ℝ) : z2A β - z2B β < 1 := z2A_sub_z2B_lt_one β

/-! ## The three spectral quantities, named correctly

With the vacuum eigenvalue normalised to `1`, three different numbers are
in play and the literature keeps them apart:

* `a - b = tanh b` is the NON-VACUUM eigenvalue -- the spectral radius of
  the operator restricted to the orthogonal complement of the vacuum, i.e.
  the contraction rate.  It is what `z2TransferOp_gap` bounds.
* `1 - tanh b` is the SPECTRAL GAP of the transfer operator.
* `-log (tanh b)` is the MASS -- the gap of the Hamiltonian `H` in
  `T = exp (-H)`.

The identifier `z2TransferOp_gap` keeps its name for compatibility with the
companion developments that already consume it; an identifier is not a
claim, and what it states is the non-vacuum bound.  The two lemmas below
supply the other two quantities as theorems rather than as prose. -/

/-- **The spectral gap of the transfer operator**, in the standard
normalisation where the vacuum eigenvalue is `1`.  Strictly positive for
every `b`. -/
theorem z2_spectral_gap_pos (β : ℝ) : 0 < 1 - Real.tanh β := by
  have h := z2A_sub_z2B_lt_one β
  rw [z2A_sub_z2B_eq_tanh] at h
  linarith

/-- The non-vacuum eigenvalue is strictly positive at positive coupling. -/
theorem z2_tanh_pos {β : ℝ} (hβ : 0 < β) : 0 < Real.tanh β := by
  rw [← z2A_sub_z2B_eq_tanh]
  unfold z2A z2B
  rw [div_sub_div_same, lt_div_iff₀ (z2Norm_pos β)]
  have h : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- **The mass.**  Writing the transfer operator as `exp (-H)`, the gap of
`H` is `-log (tanh b)`, and it is strictly positive at positive coupling.
This is the physically meaningful quantity; the norm bound of
`z2TransferOp_gap` is not it. -/
theorem z2_mass_pos {β : ℝ} (hβ : 0 < β) : 0 < -Real.log (Real.tanh β) := by
  have h1 : Real.tanh β < 1 := by
    have h := z2A_sub_z2B_lt_one β
    rw [z2A_sub_z2B_eq_tanh] at h
    exact h
  have h := Real.log_neg (z2_tanh_pos hβ) h1
  linarith

end YangMills.OS
