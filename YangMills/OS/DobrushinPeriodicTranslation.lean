/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinSiteCylinder

/-!
# Exact translations of the finite periodic Ising model

The periodic coupling used in D-7 is invariant under the two cyclic coordinate
rotations.  This file proves that fact at the finite level and transports it
through the normalized Gibbs sum.  Arbitrary integer translations of an
integer-site cylinder then follow by iteration of the two generators.

This is an exact finite-volume statement.  No limiting or Dobrushin hypothesis
occurs in the translation proof.
-/

namespace YangMills.OS
namespace Dobrushin

open Classical

/-! ## The cyclic successor -/

/-- Successor on a nonempty finite cyclic coordinate. -/
def finRotate {N : ℕ} [NeZero N] (a : Fin N) : Fin N :=
  ⟨(a.val + 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩

/-- Predecessor on a nonempty finite cyclic coordinate. -/
def finRotateBack {N : ℕ} [NeZero N] (a : Fin N) : Fin N :=
  ⟨(a.val + N - 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩

@[simp] theorem finRotateBack_finRotate {N : ℕ} [NeZero N] (a : Fin N) :
    finRotateBack (finRotate a) = a := by
  apply Fin.ext
  change (((a.val + 1) % N + N - 1) % N) = a.val
  by_cases hlast : a.val + 1 = N
  · rw [hlast, Nat.mod_self, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : a.val + 1 < N)]
    rw [show a.val + 1 + N - 1 = a.val + N by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]

@[simp] theorem finRotate_finRotateBack {N : ℕ} [NeZero N] (a : Fin N) :
    finRotate (finRotateBack a) = a := by
  apply Fin.ext
  change (((a.val + N - 1) % N + 1) % N) = a.val
  obtain ha | ha := Nat.eq_zero_or_pos a.val
  · rw [ha, Nat.zero_add, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    rw [show N - 1 + 1 = N by omega, Nat.mod_self]
  · rw [show a.val + N - 1 = (a.val - 1) + N by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a.val - 1 < N)]
    rw [show a.val - 1 + 1 = a.val by omega, Nat.mod_eq_of_lt a.isLt]

/-- Rotation as a literal equivalence. -/
def finRotateEquiv (N : ℕ) [NeZero N] : Fin N ≃ Fin N where
  toFun := finRotate
  invFun := finRotateBack
  left_inv := finRotateBack_finRotate
  right_inv := finRotate_finRotateBack

theorem cyclicNeighbor_iff_rotate {N : ℕ} [NeZero N] (a b : Fin N) :
    cyclicNeighbor a b ↔
      a ≠ b ∧ (finRotate a = b ∨ finRotate b = a) := by
  unfold cyclicNeighbor
  constructor
  · rintro ⟨hne, hdist | hwrap | hwrap⟩
    · refine ⟨hne, ?_⟩
      unfold Nat.dist at hdist
      by_cases hab : a.val ≤ b.val
      · left
        apply Fin.ext
        change (a.val + 1) % N = b.val
        rw [Nat.mod_eq_of_lt (by omega : a.val + 1 < N)]
        omega
      · right
        apply Fin.ext
        change (b.val + 1) % N = a.val
        rw [Nat.mod_eq_of_lt (by omega : b.val + 1 < N)]
        omega
    · refine ⟨hne, Or.inr ?_⟩
      apply Fin.ext
      change (b.val + 1) % N = a.val
      rw [hwrap.2, Nat.mod_self]
      exact hwrap.1.symm
    · refine ⟨hne, Or.inl ?_⟩
      apply Fin.ext
      change (a.val + 1) % N = b.val
      rw [hwrap.2, Nat.mod_self]
      exact hwrap.1.symm
  · rintro ⟨hne, hrot | hrot⟩
    · refine ⟨hne, ?_⟩
      have hv := congrArg Fin.val hrot
      change (a.val + 1) % N = b.val at hv
      by_cases hlast : a.val + 1 = N
      · exact Or.inr (Or.inr ⟨by simpa [hlast] using hv.symm, hlast⟩)
      · left
        rw [Nat.mod_eq_of_lt (by omega : a.val + 1 < N)] at hv
        unfold Nat.dist
        omega
    · refine ⟨hne, ?_⟩
      have hv := congrArg Fin.val hrot
      change (b.val + 1) % N = a.val at hv
      by_cases hlast : b.val + 1 = N
      · exact Or.inr (Or.inl ⟨by simpa [hlast] using hv.symm, hlast⟩)
      · left
        rw [Nat.mod_eq_of_lt (by omega : b.val + 1 < N)] at hv
        unfold Nat.dist
        omega

theorem cyclicNeighbor_finRotate {N : ℕ} [NeZero N] (a b : Fin N) :
    cyclicNeighbor (finRotate a) (finRotate b) ↔ cyclicNeighbor a b := by
  rw [cyclicNeighbor_iff_rotate, cyclicNeighbor_iff_rotate]
  constructor
  · rintro ⟨hne, h | h⟩
    · refine ⟨fun hab => hne (congrArg finRotate hab), Or.inl ?_⟩
      exact (finRotateEquiv N).injective h
    · refine ⟨fun hab => hne (congrArg finRotate hab), Or.inr ?_⟩
      exact (finRotateEquiv N).injective h
  · rintro ⟨hne, h | h⟩
    · exact ⟨fun hab => hne ((finRotateEquiv N).injective hab),
        Or.inl (congrArg finRotate h)⟩
    · exact ⟨fun hab => hne ((finRotateEquiv N).injective hab),
        Or.inr (congrArg finRotate h)⟩

/-! ## The two torus generators -/

/-- Positive cyclic shift in the first coordinate. -/
def torusShiftX (N : ℕ) [NeZero N] :
    (Fin N × Fin N) ≃ (Fin N × Fin N) :=
  (finRotateEquiv N).prodCongr (Equiv.refl (Fin N))

/-- Positive cyclic shift in the second coordinate. -/
def torusShiftY (N : ℕ) [NeZero N] :
    (Fin N × Fin N) ≃ (Fin N × Fin N) :=
  (Equiv.refl (Fin N)).prodCongr (finRotateEquiv N)

@[simp] theorem torusShiftX_fst_val (N : ℕ) [NeZero N]
    (p : Fin N × Fin N) :
    (torusShiftX N p).1.val = (p.1.val + 1) % N := rfl

@[simp] theorem torusShiftX_snd (N : ℕ) [NeZero N]
    (p : Fin N × Fin N) :
    (torusShiftX N p).2 = p.2 := rfl

@[simp] theorem torusShiftY_fst (N : ℕ) [NeZero N]
    (p : Fin N × Fin N) :
    (torusShiftY N p).1 = p.1 := rfl

@[simp] theorem torusShiftY_snd_val (N : ℕ) [NeZero N]
    (p : Fin N × Fin N) :
    (torusShiftY N p).2.val = (p.2.val + 1) % N := rfl

theorem reindex_periodicRectJ_torusShiftX
    (N : ℕ) [NeZero N] (beta gamma : ℝ) :
    reindexCoupling (torusShiftX N)
        (periodicRectJ (L := N) (T := N) beta gamma) =
      periodicRectJ (L := N) (T := N) beta gamma := by
  funext p q
  unfold reindexCoupling periodicRectJ torusShiftX
  change
    (if cyclicNeighbor (finRotate p.1) (finRotate q.1) ∧ p.2 = q.2 then beta
      else if finRotate p.1 = finRotate q.1 ∧ cyclicNeighbor p.2 q.2
        then gamma else 0) =
      (if cyclicNeighbor p.1 q.1 ∧ p.2 = q.2 then beta
        else if p.1 = q.1 ∧ cyclicNeighbor p.2 q.2 then gamma else 0)
  rw [propext (cyclicNeighbor_finRotate p.1 q.1)]
  by_cases hpq : p.1 = q.1
  · simp [hpq]
  · have hrot : finRotate p.1 ≠ finRotate q.1 :=
      fun h => hpq ((finRotateEquiv N).injective h)
    simp [hpq, hrot]

theorem reindex_periodicRectJ_torusShiftY
    (N : ℕ) [NeZero N] (beta gamma : ℝ) :
    reindexCoupling (torusShiftY N)
        (periodicRectJ (L := N) (T := N) beta gamma) =
      periodicRectJ (L := N) (T := N) beta gamma := by
  funext p q
  unfold reindexCoupling periodicRectJ torusShiftY
  change
    (if cyclicNeighbor p.1 q.1 ∧ finRotate p.2 = finRotate q.2 then beta
      else if p.1 = q.1 ∧ cyclicNeighbor (finRotate p.2) (finRotate q.2)
        then gamma else 0) =
      (if cyclicNeighbor p.1 q.1 ∧ p.2 = q.2 then beta
        else if p.1 = q.1 ∧ cyclicNeighbor p.2 q.2 then gamma else 0)
  rw [propext (cyclicNeighbor_finRotate p.2 q.2)]
  by_cases hpq : p.2 = q.2
  · simp [hpq]
  · have hrot : finRotate p.2 ≠ finRotate q.2 :=
      fun h => hpq ((finRotateEquiv N).injective h)
    simp [hpq, hrot]

/-- Exact invariance of every periodic Gibbs expectation under the positive
first-coordinate shift of its argument. -/
theorem expect_periodic_torusShiftX
    (N : ℕ) [NeZero N] (beta gamma : ℝ)
    (f : ((Fin N × Fin N) → Fin 2) → ℝ) :
    expect (gibbsMu (isingWeight
        (periodicRectJ (L := N) (T := N) beta gamma)))
        (fun eta => f (fun p => eta (torusShiftX N p))) =
      expect (gibbsMu (isingWeight
        (periodicRectJ (L := N) (T := N) beta gamma))) f := by
  have h := expect_gibbs_reindex (torusShiftX N).symm
    (periodicRectJ (L := N) (T := N) beta gamma) f
  have hJ : reindexCoupling (torusShiftX N).symm
      (periodicRectJ (L := N) (T := N) beta gamma) =
        periodicRectJ (L := N) (T := N) beta gamma := by
    funext p q
    have hforward := congrFun
      (congrFun (reindex_periodicRectJ_torusShiftX N beta gamma)
        ((torusShiftX N).symm p)) ((torusShiftX N).symm q)
    simpa [reindexCoupling] using hforward.symm
  rw [hJ] at h
  simpa [configEquiv_apply] using h

/-- Exact invariance under the positive second-coordinate shift. -/
theorem expect_periodic_torusShiftY
    (N : ℕ) [NeZero N] (beta gamma : ℝ)
    (f : ((Fin N × Fin N) → Fin 2) → ℝ) :
    expect (gibbsMu (isingWeight
        (periodicRectJ (L := N) (T := N) beta gamma)))
        (fun eta => f (fun p => eta (torusShiftY N p))) =
      expect (gibbsMu (isingWeight
        (periodicRectJ (L := N) (T := N) beta gamma))) f := by
  have h := expect_gibbs_reindex (torusShiftY N).symm
    (periodicRectJ (L := N) (T := N) beta gamma) f
  have hJ : reindexCoupling (torusShiftY N).symm
      (periodicRectJ (L := N) (T := N) beta gamma) =
        periodicRectJ (L := N) (T := N) beta gamma := by
    funext p q
    have hforward := congrFun
      (congrFun (reindex_periodicRectJ_torusShiftY N beta gamma)
        ((torusShiftY N).symm p)) ((torusShiftY N).symm q)
    simpa [reindexCoupling] using hforward.symm
  rw [hJ] at h
  simpa [configEquiv_apply] using h

end Dobrushin
end YangMills.OS
