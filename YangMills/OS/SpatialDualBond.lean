/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.SpatialRing
import YangMills.OS.Z2Quotient

/-!
# The exact local dual-bond identity

This file opens the algebraic infrastructure that may eventually support a
fermionic or domain-wall analysis of the spatial-ring transfer matrix.  It does
one thing only: it rewrites one `Z₂` bond as a positive scalar times the
hyperbolic `2 × 2` field bond.

## Status

**EXACT.**  `z2Bond_dual_factorization` is an entrywise identity.  It assumes
`0 < β` and the exact duality relation `tanh a = exp (-2 * β)`.  The endpoint
`β = 0` has no finite real dual coupling and is deliberately not hidden in this
parametrisation.

**CERTIFIED / VERIFIED.**  The symbolic gate
`scripts/judge_spatial_dual_bond.py` was preregistered before this theorem.  It
checks the same identity in normal and optimised Python execution.  Lean and
oracle certification are separate obligations recorded in the verification
ledger.

**NOT CLAIMED.**  This local identity is not a many-site factorisation, a
Jordan--Wigner transform, either flip-sector estimate, or progress on the
uniform spatial-ring bound itself.
-/

namespace YangMills.OS

/-- The entrywise matrix of `exp (a X)` in the two-state spin basis. -/
noncomputable def dualFieldBond (a : ℝ) (i j : Fin 2) : ℝ :=
  if i = j then Real.cosh a else Real.sinh a

/-- The positive scalar relating the Ising bond at `β` to the dual field bond. -/
noncomputable def dualFieldScale (β a : ℝ) : ℝ :=
  Real.exp β / Real.cosh a

/-- **Exact local dual-bond factorisation.**

For `0 < β` and a finite real dual coupling satisfying
`tanh a = exp (-2 * β)`, the Ising bond is entrywise the scaled matrix
`cosh(a) I + sinh(a) X`.  The strict sign hypothesis is active: at `β = 0`
the required dual coupling is not finite.

This theorem is only the local `2 × 2` algebraic identity.  In particular it
does not identify a many-site transfer matrix or prove a spectral bound. -/
theorem z2Bond_dual_factorization
    (β a : ℝ) (hβ : 0 < β)
    (hdual : Real.tanh a = Real.exp (-2 * β))
    (i j : Fin 2) :
    z2Bond β i j = dualFieldScale β a * dualFieldBond a i j := by
  have _hr_lt_one : Real.exp (-2 * β) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hcosh : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos a)
  by_cases hij : i = j
  · subst j
    rw [z2Bond_same]
    simp only [dualFieldScale, dualFieldBond, if_pos]
    exact (div_mul_cancel₀ (Real.exp β) hcosh).symm
  · rw [z2Bond_ne hij]
    simp only [dualFieldScale, dualFieldBond, if_neg hij]
    calc
      Real.exp (-β) = Real.exp β * Real.exp (-2 * β) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp β * Real.tanh a := by rw [hdual]
      _ = Real.exp β * (Real.sinh a / Real.cosh a) := by
        rw [Real.tanh_eq_sinh_div_cosh]
      _ = Real.exp β / Real.cosh a * Real.sinh a := by ring

/-- **Exact finite-product lift to the decoupled spatial kernel.**

Under the same strict positive-`β` duality relation as the local identity, the
product defining `spatialKernel` is a scalar `dualFieldScale β a ^ L` times the
product of the dual-field entries.  This is still only an entrywise identity:
it does not include the ring weight, identify a tensor-product exponential, or
prove a sector bound. -/
theorem spatialKernel_dual_factorization
    (β a : ℝ) (hβ : 0 < β)
    (hdual : Real.tanh a = Real.exp (-2 * β))
    {L : ℕ} (σ τ : Fin L → Fin 2) :
    spatialKernel β σ τ =
      dualFieldScale β a ^ L * ∏ j, dualFieldBond a (σ j) (τ j) := by
  unfold spatialKernel
  simp_rw [z2Bond_dual_factorization β a hβ hdual]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## The periodic ring weight as one exponential -/

/-- The signed nearest-neighbour energy of a periodic two-state ring. -/
noncomputable def ringBondSum {L : ℕ} (σ : Fin (L + 1) → Fin 2) : ℝ :=
  ∑ j, z2Sign (σ j) (σ (j + 1))

/-- **Exact exponential form of the full periodic ring weight.**

The product includes the closing bond through arithmetic on `Fin (L + 1)`.
This identity is algebraic and therefore holds for every real `γ`; it does not
weaken the active hypothesis `0 ≤ γ` in the spatial spectral target.  It does
not rewrite the square roots in `symWeighted` or prove a sector bound. -/
theorem spatialWeightRing_eq_exp_ringBondSum
    (γ : ℝ) {L : ℕ} (σ : Fin (L + 1) → Fin 2) :
    spatialWeightRing γ σ = Real.exp (γ * ringBondSum σ) := by
  unfold spatialWeightRing ringBondSum z2Bond
  rw [← Real.exp_sum, Finset.mul_sum]

end YangMills.OS
