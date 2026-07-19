/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Data.Nat.Basic

/-!
# Dependent walks of typed arrows

CMP99 Section C explicitly allows neighboring factors to act between different
scales.  A monoid product of endomorphisms cannot express that statement
without zero extension or an unaudited carrier identification.  The chain below
stores every intermediate object in its type and composes only arrows whose
source and target match definitionally.  Continuous linear maps are the physical
instantiation used by the regional Section C factors.
-/

namespace YangMills.RG

universe u v

/-- A composable finite walk through a typed family of arrows. -/
inductive DependentArrowWalk {ι : Type u} (Hom : ι → ι → Type v) :
    ι → ι → Type (max u v) where
  | nil (i : ι) : DependentArrowWalk Hom i i
  | cons {i k l : ι} (head : Hom i k) (tail : DependentArrowWalk Hom k l) :
      DependentArrowWalk Hom i l

namespace DependentArrowWalk

variable {ι : Type u} {Hom : ι → ι → Type v}

/-- Number of non-identity factors in a dependent walk. -/
def length {i k : ι} : DependentArrowWalk Hom i k → ℕ
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

/-- Ordered evaluation in any typed composition law. -/
def evaluate
    (identity : ∀ i, Hom i i)
    (compose : ∀ {i k l}, Hom k l → Hom i k → Hom i l)
    {i k : ι} : DependentArrowWalk Hom i k → Hom i k
  | .nil i => identity i
  | .cons head tail => compose (tail.evaluate identity compose) head

@[simp] theorem evaluate_nil
    (identity : ∀ i, Hom i i)
    (compose : ∀ {i k l}, Hom k l → Hom i k → Hom i l)
    (i : ι) :
    (DependentArrowWalk.nil (Hom := Hom) i).evaluate identity compose =
      identity i :=
  rfl

@[simp] theorem evaluate_cons
    (identity : ∀ i, Hom i i)
    (compose : ∀ {i k l}, Hom k l → Hom i k → Hom i l)
    {i k l : ι} (head : Hom i k) (tail : DependentArrowWalk Hom k l) :
    (DependentArrowWalk.cons head tail).evaluate identity compose =
      compose (tail.evaluate identity compose) head :=
  rfl

/-- Concatenation preserves every intermediate type. -/
def append {i k l : ι}
    (first : DependentArrowWalk Hom i k)
    (second : DependentArrowWalk Hom k l) : DependentArrowWalk Hom i l :=
  match first with
  | .nil _ => second
  | .cons head tail => .cons head (tail.append second)

@[simp] theorem length_append {i k l : ι}
    (first : DependentArrowWalk Hom i k)
    (second : DependentArrowWalk Hom k l) :
    (first.append second).length = first.length + second.length := by
  induction first with
  | nil => simp [append, length]
  | cons head tail ih =>
      simp only [append, length, ih]
      omega

/-- Evaluation of a concatenated walk is the correctly ordered composition,
provided the supplied arrow laws have a right identity and are associative. -/
theorem evaluate_append
    (identity : ∀ i, Hom i i)
    (compose : ∀ {i k l}, Hom k l → Hom i k → Hom i l)
    (right_identity : ∀ {i k} (f : Hom i k), compose f (identity i) = f)
    (assoc : ∀ {i k l m} (f : Hom l m) (g : Hom k l) (h : Hom i k),
      compose f (compose g h) = compose (compose f g) h)
    {i k l : ι} (first : DependentArrowWalk Hom i k)
    (second : DependentArrowWalk Hom k l) :
    (first.append second).evaluate identity compose =
      compose (second.evaluate identity compose)
        (first.evaluate identity compose) := by
  induction first with
  | nil =>
      exact (right_identity (second.evaluate identity compose)).symm
  | cons head tail ih =>
      simp only [append, evaluate_cons, ih]
      exact (assoc _ _ _).symm

/-- A one-factor walk evaluates to that factor. -/
@[simp] theorem evaluate_singleton
    (identity : ∀ i, Hom i i)
    (compose : ∀ {i k l}, Hom k l → Hom i k → Hom i l)
    (left_identity : ∀ {i k} (f : Hom i k), compose (identity k) f = f)
    {i k : ι} (A : Hom i k) :
    (DependentArrowWalk.cons A
      (DependentArrowWalk.nil (Hom := Hom) k)).evaluate identity compose = A :=
  left_identity A

/-- The canonical prefix `0 → 1 → ... → r` formed from consecutive arrows on
`Fin (n+1)`.  Every intermediate index remains visible in the type. -/
def finSuccPrefix {n : ℕ}
    {HomFin : Fin (n + 1) → Fin (n + 1) → Type v}
    (step : ∀ r : Fin n, HomFin r.castSucc r.succ)
    (r : Fin (n + 1)) : DependentArrowWalk HomFin 0 r :=
  Fin.induction
    (DependentArrowWalk.nil (Hom := HomFin) 0)
    (fun i walk => walk.append
      (DependentArrowWalk.cons (step i)
        (DependentArrowWalk.nil (Hom := HomFin) i.succ)))
    r

@[simp] theorem finSuccPrefix_zero {n : ℕ}
    {HomFin : Fin (n + 1) → Fin (n + 1) → Type v}
    (step : ∀ r : Fin n, HomFin r.castSucc r.succ) :
    finSuccPrefix step (0 : Fin (n + 1)) =
      DependentArrowWalk.nil (Hom := HomFin) 0 :=
  rfl

theorem finSuccPrefix_succ {n : ℕ}
    {HomFin : Fin (n + 1) → Fin (n + 1) → Type v}
    (step : ∀ r : Fin n, HomFin r.castSucc r.succ) (r : Fin n) :
    finSuccPrefix step r.succ =
      (finSuccPrefix step r.castSucc).append
        (DependentArrowWalk.cons (step r)
          (DependentArrowWalk.nil (Hom := HomFin) r.succ)) :=
  rfl

/-- The canonical full walk through all `n+1` indices. -/
def finSuccPath {n : ℕ}
    {HomFin : Fin (n + 1) → Fin (n + 1) → Type v}
    (step : ∀ r : Fin n, HomFin r.castSucc r.succ) :
    DependentArrowWalk HomFin 0 (Fin.last n) :=
  finSuccPrefix step (Fin.last n)

@[simp] theorem length_finSuccPrefix {n : ℕ}
    {HomFin : Fin (n + 1) → Fin (n + 1) → Type v}
    (step : ∀ r : Fin n, HomFin r.castSucc r.succ)
    (r : Fin (n + 1)) :
    (finSuccPrefix step r).length = r.val := by
  refine Fin.induction ?_ ?_ r
  · rfl
  · intro i ih
    rw [finSuccPrefix_succ, length_append]
    simp [length, ih]

@[simp] theorem length_finSuccPath {n : ℕ}
    {HomFin : Fin (n + 1) → Fin (n + 1) → Type v}
    (step : ∀ r : Fin n, HomFin r.castSucc r.succ) :
    (finSuccPath step).length = n := by
  simp [finSuccPath]

end DependentArrowWalk

end YangMills.RG
