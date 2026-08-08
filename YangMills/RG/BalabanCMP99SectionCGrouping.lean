/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.DependentArrowWalk

/-!
# Typed grouping grammar for CMP99 Section C factors

CMP99 pp. 411--413 first obtains an ordered word of localized operator atoms
after substituting the random-walk expansion into (3.95), then groups those
atoms into the factors denoted `R'_alpha(X)`.  A small atom is the anchor.
An `h' G' h'` atom is attached to the closest small atom on its right, while
an `h C h` atom is attached to the closest small atom on its left.  At worst
three non-small atoms are attached to one anchor.

This file formalizes that grouping without enumerating `alpha`.  Both atoms
and factors are dependent arrows, so different scale/carrier endpoints must
match definitionally.  The terminal theorem proves that evaluating the
flattened atom word is exactly evaluation of the grouped factor word.  It is
purely structural: the source-specific atom constructors, the parser from
(3.95), and the analytic proof of the three-attachment budget remain visible
downstream obligations.
-/

namespace YangMills.RG

universe u v

/-- Source role of an atom in the grouping argument on CMP99 pp. 411--413. -/
inductive CMP99SectionCAtomRole where
  /-- An `O(M^-1)` atom around which non-small atoms are grouped. -/
  | smallAnchor
  /-- An `h' G' h'`-type atom, attached to the closest anchor on its right. -/
  | attachToRightAnchor
  /-- An `h C h`-type atom, attached to the closest anchor on its left. -/
  | attachToLeftAnchor
  /-- A source term already declared to be one complete factor. -/
  | sealedAnchor
deriving DecidableEq

namespace DependentArrowWalk

variable {iota : Type u} {Hom : iota → iota → Type v}

/-- Every arrow in a dependent walk satisfies a dependent predicate. -/
def All (P : ∀ {r s}, Hom r s → Prop) {r s : iota} :
    DependentArrowWalk Hom r s → Prop
  | .nil _ => True
  | .cons head tail => P head ∧ tail.All P

@[simp] theorem all_nil (P : ∀ {r s}, Hom r s → Prop) (r : iota) :
    (DependentArrowWalk.nil (Hom := Hom) r).All P :=
  trivial

@[simp] theorem all_cons_iff (P : ∀ {r s}, Hom r s → Prop)
    {r s t : iota} (head : Hom r s) (tail : DependentArrowWalk Hom s t) :
    (DependentArrowWalk.cons head tail).All P ↔ P head ∧ tail.All P :=
  Iff.rfl

theorem all_append_iff (P : ∀ {r s}, Hom r s → Prop)
    {r s t : iota} (first : DependentArrowWalk Hom r s)
    (second : DependentArrowWalk Hom s t) :
    (first.append second).All P ↔ first.All P ∧ second.All P := by
  induction first with
  | nil => simp [DependentArrowWalk.append]
  | cons head tail ih => simp [DependentArrowWalk.append, ih, and_assoc]

end DependentArrowWalk

/-- One source-faithful grouped factor.  The pre-anchor word consists exactly
of atoms assigned to the closest small factor on their right; the post-anchor
word consists exactly of atoms assigned to the closest small factor on their
left. -/
structure CMP99SectionCGroupedFactor {iota : Type u}
    (Atom : iota → iota → Type v)
    (role : ∀ {r s}, Atom r s → CMP99SectionCAtomRole)
    (source target : iota) where
  preTarget : iota
  anchorTarget : iota
  pre : DependentArrowWalk Atom source preTarget
  anchor : Atom preTarget anchorTarget
  post : DependentArrowWalk Atom anchorTarget target
  pre_roles : pre.All fun atom => role atom = .attachToRightAnchor
  anchor_role : role anchor = .smallAnchor ∨ role anchor = .sealedAnchor
  post_roles : post.All fun atom => role atom = .attachToLeftAnchor
  attached_le_three : pre.length + post.length ≤ 3

namespace CMP99SectionCGroupedFactor

variable {iota : Type u} {Atom : iota → iota → Type v}
variable {role : ∀ {r s}, Atom r s → CMP99SectionCAtomRole}

/-- Forget the grouping boundaries and recover the literal atom word. -/
def atomWalk {source target : iota}
    (factor : CMP99SectionCGroupedFactor Atom role source target) :
    DependentArrowWalk Atom source target :=
  factor.pre.append (.cons factor.anchor factor.post)

@[simp] theorem atomWalk_length {source target : iota}
    (factor : CMP99SectionCGroupedFactor Atom role source target) :
    factor.atomWalk.length = factor.pre.length + 1 + factor.post.length := by
  rw [atomWalk, DependentArrowWalk.length_append]
  simp only [DependentArrowWalk.length]
  omega

/-- The complete atom word of a factor is nonempty because it contains its
distinguished small or sealed anchor. -/
theorem atomWalk_length_pos {source target : iota}
    (factor : CMP99SectionCGroupedFactor Atom role source target) :
    0 < factor.atomWalk.length := by
  rw [atomWalk_length]
  omega

/-- The source statement "at worst three attached operators" gives a factor
of at most four atoms once its anchor is included. -/
theorem atomWalk_length_le_four {source target : iota}
    (factor : CMP99SectionCGroupedFactor Atom role source target) :
    factor.atomWalk.length ≤ 4 := by
  rw [atomWalk_length]
  have h := factor.attached_le_three
  omega

/-- Evaluate one grouped factor by its literal ordered atom product. -/
def evaluate
    (identity : ∀ i, Atom i i)
    (compose : ∀ {i k l}, Atom k l → Atom i k → Atom i l)
    {source target : iota}
    (factor : CMP99SectionCGroupedFactor Atom role source target) :
    Atom source target :=
  factor.atomWalk.evaluate identity compose

end CMP99SectionCGroupedFactor

namespace CMP99SectionCGroupedWalk

variable {iota : Type u} {Atom : iota → iota → Type v}
variable {role : ∀ {r s}, Atom r s → CMP99SectionCAtomRole}

/-- Flatten every grouped factor in a dependent factor word. -/
def flatten {source target : iota} :
    DependentArrowWalk (CMP99SectionCGroupedFactor Atom role) source target →
      DependentArrowWalk Atom source target
  | .nil i => .nil i
  | .cons factor tail => factor.atomWalk.append (flatten tail)

/-- Total number of atoms stored in a grouped factor word. -/
def atomCount {source target : iota} :
    DependentArrowWalk (CMP99SectionCGroupedFactor Atom role) source target → ℕ
  | .nil _ => 0
  | .cons factor tail => factor.atomWalk.length + atomCount tail

/-- The number of atoms after flattening is the sum of the sizes of all
grouped factors. -/
theorem flatten_length {source target : iota}
    (walk : DependentArrowWalk (CMP99SectionCGroupedFactor Atom role)
      source target) :
    (flatten walk).length = atomCount walk := by
  induction walk with
  | nil => rfl
  | cons factor tail ih =>
      simp only [flatten, DependentArrowWalk.length_append,
        atomCount, ih]

/-- Evaluate a grouped word by evaluating every factor and composing in the
original source order. -/
def evaluate
    (identity : ∀ i, Atom i i)
    (compose : ∀ {i k l}, Atom k l → Atom i k → Atom i l)
    {source target : iota} :
    DependentArrowWalk (CMP99SectionCGroupedFactor Atom role) source target →
      Atom source target
  | .nil i => identity i
  | .cons factor tail =>
      compose (evaluate identity compose tail)
        (factor.evaluate identity compose)

/-- Exact semantic preservation of grouping.  No operator commutation occurs:
only associativity and the right identity are used to erase parentheses. -/
theorem evaluate_flatten
    (identity : ∀ i, Atom i i)
    (compose : ∀ {i k l}, Atom k l → Atom i k → Atom i l)
    (right_identity : ∀ {i k} (f : Atom i k), compose f (identity i) = f)
    (assoc : ∀ {i k l m} (f : Atom l m) (g : Atom k l) (h : Atom i k),
      compose f (compose g h) = compose (compose f g) h)
    {source target : iota}
    (walk : DependentArrowWalk (CMP99SectionCGroupedFactor Atom role)
      source target) :
    (flatten walk).evaluate identity compose =
      evaluate identity compose walk := by
  induction walk with
  | nil => rfl
  | cons factor tail ih =>
      rw [flatten, DependentArrowWalk.evaluate_append identity compose
        right_identity assoc factor.atomWalk (flatten tail), ih]
      rfl

end CMP99SectionCGroupedWalk

end YangMills.RG
