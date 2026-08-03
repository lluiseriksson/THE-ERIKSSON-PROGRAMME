/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma1DependentVisitedWalk
import YangMills.RG.BalabanCMP99SectionCGrouping

/-!
# Squarefree weakening through the CMP99 Section-C grouping

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

CMP99 pp. 411--413 groups ordered localized atoms around a small or sealed
anchor before calling the result one generalized factor `R'_alpha(X)`.  The
grouping module already proves that flattening those factors preserves the
ordered operator product.  This file proves the complementary localization
statement: flattening also preserves the union of the finite weakening
carriers of all atoms.

Consequently the squarefree monomial and its cardinality `m` are invariant
under the source grouping.  Repeated visits to one cube are still charged
once.  This is the dictionary needed to transport the printed L1 long-walk
split across the grouping step without replacing `m` by word length.

Honest scope: the source-specific parser of the exhaustive atoms from the
physical correction, the three-attachment estimate, and the exact CMP99
(3.107) reconstruction remain open.  No complete factor alphabet or physical
propagator is supplied here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

universe u v w

namespace DependentArrowWalk

variable {ι : Type u} {Hom : ι → ι → Type v}

/-- The active union of a concatenated typed walk is the union of the active
carriers of its two pieces. -/
theorem active_append {Delta : Type w} [DecidableEq Delta]
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    {i j k : ι} (first : DependentArrowWalk Hom i j)
    (second : DependentArrowWalk Hom j k) :
    (first.append second).active factorActive =
      first.active factorActive ∪ second.active factorActive := by
  induction first with
  | nil => simp [DependentArrowWalk.append]
  | cons head tail ih =>
      simp [DependentArrowWalk.append, ih, Finset.union_assoc]

end DependentArrowWalk

namespace CMP99SectionCGroupedWalk

variable {ι : Type u} {Atom : ι → ι → Type v}
variable {role : ∀ {i j}, Atom i j → CMP99SectionCAtomRole}

/-- Flattening the grouped factor word preserves exactly the union of all
atom weakening carriers. -/
theorem flatten_active {Delta : Type w} [DecidableEq Delta]
    (atomActive : ∀ {i j}, Atom i j → Finset Delta)
    {source target : ι}
    (walk : DependentArrowWalk (CMP99SectionCGroupedFactor Atom role)
      source target) :
    (flatten walk).active atomActive =
      walk.active (fun factor => factor.atomWalk.active atomActive) := by
  induction walk with
  | nil => rfl
  | cons factor tail ih =>
      simp [flatten, DependentArrowWalk.active_append, ih]

/-- The printed distinct-cube count `m` is unchanged by the Section-C
grouping boundaries. -/
theorem card_active_flatten {Delta : Type w} [DecidableEq Delta]
    (atomActive : ∀ {i j}, Atom i j → Finset Delta)
    {source target : ι}
    (walk : DependentArrowWalk (CMP99SectionCGroupedFactor Atom role)
      source target) :
    ((flatten walk).active atomActive).card =
      (walk.active (fun factor => factor.atomWalk.active atomActive)).card := by
  exact congrArg Finset.card (flatten_active atomActive walk)

/-- The squarefree weakening monomial is invariant under grouping the source
atom word into generalized factors. -/
theorem complexWeakeningMonomial_flatten {Delta : Type w}
    [DecidableEq Delta]
    (atomActive : ∀ {i j}, Atom i j → Finset Delta)
    (sigma : Delta → ℂ)
    {source target : ι}
    (walk : DependentArrowWalk (CMP99SectionCGroupedFactor Atom role)
      source target) :
    cmp116ComplexWeakeningMonomial
        ((flatten walk).active atomActive) sigma =
      cmp116ComplexWeakeningMonomial
        (walk.active (fun factor => factor.atomWalk.active atomActive)) sigma := by
  rw [flatten_active]

/-- Grouping preserves the complete weakened ordered term: both the
squarefree monomial and the noncommutative operator product agree with those
of the flattened atom word.  No factor commutation or idempotence of the
weakening coordinates is used. -/
theorem complexWeakenedEvaluate_flatten {Delta : Type w}
    [DecidableEq Delta] [∀ i j, SMul ℂ (Atom i j)]
    (atomActive : ∀ {i j}, Atom i j → Finset Delta)
    (sigma : Delta → ℂ)
    (identity : ∀ i, Atom i i)
    (compose : ∀ {i k l}, Atom k l → Atom i k → Atom i l)
    (right_identity : ∀ {i k} (f : Atom i k),
      compose f (identity i) = f)
    (assoc : ∀ {i k l m} (f : Atom l m) (g : Atom k l)
      (h : Atom i k), compose f (compose g h) = compose (compose f g) h)
    {source target : ι}
    (walk : DependentArrowWalk (CMP99SectionCGroupedFactor Atom role)
      source target) :
    cmp116ComplexWeakeningMonomial
        ((flatten walk).active atomActive) sigma •
        (flatten walk).evaluate identity compose =
      cmp116ComplexWeakeningMonomial
          (walk.active (fun factor => factor.atomWalk.active atomActive)) sigma •
        evaluate identity compose walk := by
  rw [flatten_active, evaluate_flatten identity compose right_identity assoc]

end CMP99SectionCGroupedWalk

end

end YangMills.RG
