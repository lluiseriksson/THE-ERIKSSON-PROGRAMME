/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3e: the Gelfand-Naimark-Segal quotient, exercised on a genuinely degenerate
reflection pairing for the Z_2 chain.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 9 (five pre-registered judges).
-/

import Mathlib
import YangMills.OS.Z2Identification

/-!
# O-3e — a quotient that is not the identity

## The point of this module

The OS-chain development proved a complete reconstruction for the `Z_2` chain,
with one hole named in its own abstract: the pairing there is definite, so the
Gelfand-Naimark-Segal quotient is the identity and does no work.  This module
removes that hole.

The degeneracy is not manufactured.  Half-space observables of TWO time slices
form a `4`-dimensional space; the physical space of the chain is
`2`-dimensional.  Integrating out the future collapses four observables onto two
states, and the collapse IS the null space.  That is the mechanism the
reconstruction exists to handle, and it is the one that reappears at every
larger system.

As in O-3d, the two sides are defined independently.  `reflPairing` is built
from `z2Bond` -- `Real.exp` and the bond sign -- and from nothing else; no
`slicePhi`, no `z2TransferOp`, no `z2A`, no `z2B` occurs in it.  That the
pairing factors through `slicePhi` is then a theorem.

## What comes out

* `reflPairing_eq` -- the pairing factors through `slicePhi` with the transfer
  kernel between the two halves.
* `reflPairing_self` -- the self-pairing is a MANIFEST SUM OF TWO NON-NEGATIVE
  TERMS.  Positivity and the null-space characterisation both follow from this
  one identity.
* `nullObs_ne_zero` and `reflPairing_nullObs` -- an explicit NON-ZERO observable
  in the null space.  This is the judge: without it the brick would have rebuilt
  the trivial case.
* `reflPairing_self_eq_zero_iff` -- the null space is EXACTLY the kernel of
  `slicePhi`, not merely non-empty.
* `quotEquivPhysical` -- the quotient is the physical space, and the isomorphism
  is induced by the reconstruction map itself.

## Scope, stated plainly

Two time slices, not `m`.  Still `Z_2`, one variable per slice, fixed finite
size, not volume-uniform.  `Z_N` for `N > 2` untouched.  The completion step of
the reconstruction is trivial here because every space in sight is
finite-dimensional; that is stated, not presented as work done.  The pairing is
definite only for `beta > 0`: at `beta = 0` the kernel itself degenerates, and
that boundary is stated rather than quietly excluded.  Nothing here is a claim
about `SU(N)`, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

/-! ## §1  The bond weight at the two available arguments -/

theorem z2Bond_same (β : ℝ) (i : Fin 2) : z2Bond β i i = Real.exp β := by
  unfold z2Bond z2Sign
  simp

theorem z2Bond_ne {i j : Fin 2} (h : i ≠ j) (β : ℝ) : z2Bond β i j = Real.exp (-β) := by
  unfold z2Bond z2Sign
  rw [if_neg h]
  congr 1
  ring

/-! ## §2  The reflected pairing — measure side, no operator anywhere -/

/-- **The reflected pairing on two-slice half-space observables.**  The four
spins are, in order, `σ_{-2}, σ_{-1}, σ_0, σ_1`; the reflection sends the
half-space `{0,1}` to `{-1,-2}`.  Defined from `z2Bond` and from nothing else. -/
noncomputable def reflPairing (β : ℝ) (A B : Fin 2 → Fin 2 → ℂ) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    (starRingEnd ℂ) (A b a) * B c d *
      ((z2Bond β a b * z2Bond β b c * z2Bond β c d : ℝ) : ℂ)

/-! ## §3  The reconstruction map -/

/-- **The reconstruction map**: integrate the future out of a two-slice
observable. -/
noncomputable def slicePhi (β : ℝ) (A : Fin 2 → Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun c => ∑ d, ((z2Bond β c d : ℝ) : ℂ) * A c d

theorem slicePhi_apply (β : ℝ) (A : Fin 2 → Fin 2 → ℂ) (c : Fin 2) :
    slicePhi β A c
      = ((z2Bond β c 0 : ℝ) : ℂ) * A c 0 + ((z2Bond β c 1 : ℝ) : ℂ) * A c 1 := by
  unfold slicePhi
  rw [Fin.sum_univ_two]

/-- The reconstruction map, as a linear map. -/
noncomputable def slicePhiLin (β : ℝ) :
    (Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := slicePhi β
  map_add' := by
    intro A B
    funext c
    simp only [slicePhi_apply, Pi.add_apply]
    ring
  map_smul' := by
    intro r A
    funext c
    simp only [slicePhi_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem slicePhiLin_apply (β : ℝ) (A : Fin 2 → Fin 2 → ℂ) :
    slicePhiLin β A = slicePhi β A := rfl

/-! ## §4  The pairing factors through the reconstruction map -/

/-- **The pairing factors through `slicePhi`**, with the transfer kernel between
the two halves.  This is the analogue of the identification theorem: two
independently defined objects turn out to agree. -/
theorem reflPairing_eq (β : ℝ) (A B : Fin 2 → Fin 2 → ℂ) :
    reflPairing β A B
      = ∑ b, ∑ c,
          (starRingEnd ℂ) (slicePhi β A b) * ((z2Bond β b c : ℝ) : ℂ) * slicePhi β B c := by
  unfold reflPairing
  simp only [slicePhi_apply, Fin.sum_univ_two, map_add, map_mul, Complex.conj_ofReal,
    z2Bond_symm β 0 1]
  push_cast
  ring

/-! ## §5  The self-pairing is a sum of two non-negative terms -/

/-- **The key identity.**  The self-pairing rearranges into a manifest sum of two
non-negative real terms.  Positivity and the null-space characterisation both
come from here. -/
theorem reflPairing_self (β : ℝ) (A : Fin 2 → Fin 2 → ℂ) :
    reflPairing β A A
      = (((Real.exp β - Real.exp (-β)) *
            (Complex.normSq (slicePhi β A 0) + Complex.normSq (slicePhi β A 1))
          + Real.exp (-β) *
            Complex.normSq (slicePhi β A 0 + slicePhi β A 1) : ℝ) : ℂ) := by
  rw [reflPairing_eq]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [z2Bond_same, z2Bond_same, z2Bond_ne (by decide) β, z2Bond_ne (by decide : (1:Fin 2) ≠ 0) β]
  simp only [Complex.ext_iff, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  constructor <;> ring

/-! ## §6  Positivity, and the exact null space -/

theorem reflPairing_self_nonneg {β : ℝ} (hβ : 0 ≤ β) (A : Fin 2 → Fin 2 → ℂ) :
    0 ≤ (reflPairing β A A).re := by
  rw [reflPairing_self]
  simp only [Complex.ofReal_re]
  have h : Real.exp (-β) ≤ Real.exp β := Real.exp_le_exp.mpr (by linarith)
  have h1 : (0:ℝ) ≤ Real.exp (-β) := (Real.exp_pos _).le
  nlinarith [Complex.normSq_nonneg (slicePhi β A 0),
    Complex.normSq_nonneg (slicePhi β A 1),
    Complex.normSq_nonneg (slicePhi β A 0 + slicePhi β A 1)]

/-- **The null space is exactly the kernel of the reconstruction map.**  Not
merely non-empty: an equivalence. -/
theorem reflPairing_self_eq_zero_iff {β : ℝ} (hβ : 0 < β) (A : Fin 2 → Fin 2 → ℂ) :
    reflPairing β A A = 0 ↔ slicePhi β A = 0 := by
  have hgap : 0 < Real.exp β - Real.exp (-β) := by
    have : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hq : (0:ℝ) < Real.exp (-β) := Real.exp_pos _
  constructor
  · intro h
    rw [reflPairing_self] at h
    have hr : (Real.exp β - Real.exp (-β)) *
        (Complex.normSq (slicePhi β A 0) + Complex.normSq (slicePhi β A 1))
        + Real.exp (-β) * Complex.normSq (slicePhi β A 0 + slicePhi β A 1) = 0 := by
      exact_mod_cast h
    have h0 : Complex.normSq (slicePhi β A 0) + Complex.normSq (slicePhi β A 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (slicePhi β A 0),
        Complex.normSq_nonneg (slicePhi β A 1),
        Complex.normSq_nonneg (slicePhi β A 0 + slicePhi β A 1)]
    funext c
    have e0 : Complex.normSq (slicePhi β A 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (slicePhi β A 0),
        Complex.normSq_nonneg (slicePhi β A 1)]
    have e1 : Complex.normSq (slicePhi β A 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (slicePhi β A 0),
        Complex.normSq_nonneg (slicePhi β A 1)]
    fin_cases c
    · simpa using Complex.normSq_eq_zero.mp e0
    · simpa using Complex.normSq_eq_zero.mp e1
  · intro h
    rw [reflPairing_self]
    have h0 : slicePhi β A 0 = 0 := by rw [h]; rfl
    have h1 : slicePhi β A 1 = 0 := by rw [h]; rfl
    rw [h0, h1]
    simp

/-! ## §7  THE JUDGE — the null space is not zero -/

/-- An explicit two-slice observable annihilated by the reconstruction map.
Defined by pattern matching rather than with a conditional, so that its two
values reduce definitionally. -/
noncomputable def nullObs (β : ℝ) : Fin 2 → Fin 2 → ℂ
  | c, 0 => ((z2Bond β c 1 : ℝ) : ℂ)
  | c, 1 => -((z2Bond β c 0 : ℝ) : ℂ)

theorem nullObs_zero (β : ℝ) (c : Fin 2) :
    nullObs β c 0 = ((z2Bond β c 1 : ℝ) : ℂ) := rfl

theorem nullObs_one (β : ℝ) (c : Fin 2) :
    nullObs β c 1 = -((z2Bond β c 0 : ℝ) : ℂ) := rfl

theorem slicePhi_nullObs (β : ℝ) : slicePhi β (nullObs β) = 0 := by
  funext c
  show slicePhi β (nullObs β) c = 0
  rw [slicePhi_apply, nullObs_zero, nullObs_one]
  ring

/-- **THE JUDGE OF AMENDMENT 9.**  The null space is NOT zero: this observable
is nonzero and lies in it.  Without this the module would have rebuilt the
trivial case of the OS-chain paper. -/
theorem nullObs_ne_zero (β : ℝ) : nullObs β ≠ 0 := by
  intro h
  have h0 : nullObs β 0 0 = 0 := by rw [h]; rfl
  rw [nullObs_zero] at h0
  exact absurd (Complex.ofReal_eq_zero.mp h0) (ne_of_gt (z2Bond_pos β 0 1))

theorem reflPairing_nullObs {β : ℝ} (hβ : 0 < β) :
    reflPairing β (nullObs β) (nullObs β) = 0 :=
  (reflPairing_self_eq_zero_iff hβ _).mpr (slicePhi_nullObs β)

/-! ## §8  The quotient is the physical space, by the reconstruction map -/

/-- A preimage witness, again by pattern matching. -/
noncomputable def surjWitness (β : ℝ) (v : Fin 2 → ℂ) : Fin 2 → Fin 2 → ℂ
  | c, 0 => v c / ((z2Bond β c 0 : ℝ) : ℂ)
  | _, 1 => 0

theorem surjWitness_zero (β : ℝ) (v : Fin 2 → ℂ) (c : Fin 2) :
    surjWitness β v c 0 = v c / ((z2Bond β c 0 : ℝ) : ℂ) := rfl

theorem surjWitness_one (β : ℝ) (v : Fin 2 → ℂ) (c : Fin 2) :
    surjWitness β v c 1 = 0 := rfl

theorem slicePhi_surjective (β : ℝ) : Function.Surjective (slicePhiLin β) := by
  intro v
  refine ⟨surjWitness β v, ?_⟩
  rw [slicePhiLin_apply]
  funext c
  rw [slicePhi_apply, surjWitness_zero, surjWitness_one]
  have hne : ((z2Bond β c 0 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (z2Bond_pos β c 0)
  rw [mul_zero, add_zero]
  field_simp

/-- The null space, as a submodule. -/
noncomputable def nullSubmodule (β : ℝ) : Submodule ℂ (Fin 2 → Fin 2 → ℂ) :=
  LinearMap.ker (slicePhiLin β)

theorem mem_nullSubmodule_iff {β : ℝ} (hβ : 0 < β) (A : Fin 2 → Fin 2 → ℂ) :
    A ∈ nullSubmodule β ↔ reflPairing β A A = 0 := by
  rw [nullSubmodule, LinearMap.mem_ker, slicePhiLin_apply,
    reflPairing_self_eq_zero_iff hβ]

theorem nullSubmodule_ne_bot (β : ℝ) : nullSubmodule β ≠ ⊥ := by
  intro h
  have hmem : nullObs β ∈ nullSubmodule β := by
    rw [nullSubmodule, LinearMap.mem_ker, slicePhiLin_apply]
    exact slicePhi_nullObs β
  rw [h, Submodule.mem_bot] at hmem
  exact nullObs_ne_zero β hmem

/-- **The quotient is the physical space, and the isomorphism is induced by the
reconstruction map.**  Not a dimension count: the map is `slicePhi`. -/
noncomputable def quotEquivPhysical (β : ℝ) :
    ((Fin 2 → Fin 2 → ℂ) ⧸ nullSubmodule β) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (slicePhiLin β).quotKerEquivOfSurjective (slicePhi_surjective β)

end YangMills.OS
