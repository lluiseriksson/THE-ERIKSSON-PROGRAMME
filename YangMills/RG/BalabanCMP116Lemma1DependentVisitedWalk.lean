/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma1WeakenedPropagatorBound
import YangMills.RG.BalabanCMP116VisitedWeakeningFactorization
import YangMills.RG.DependentArrowWalk

/-!
# Dependent visited walks for the CMP116 Lemma-1 weakening

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

CMP99 printed page 413 states that the factors in its generalized random-walk
expansion generally act between different scales and that only type-correct
label sequences are admitted.  Equation (3.107) suppresses those intermediate
carriers in its displayed product because they do not affect the bounds.

This module keeps the carrier changes literal.  Each physical factor is an
arrow in a `DependentArrowWalk`; its localization domain contributes one
finite set of weakening coordinates, and the active carrier of the whole walk
is their union.  Consequently every coordinate is charged exactly once even
when several factors activate it.

The weakened family is constructed internally by generic L1 from the
dependent walk index, the squarefree carrier and the unweakened term.  A source
certificate may provide the per-walk CMP99 estimate and the single exact
full-coupling reconstruction `sum_walk term = physicalH`; it may not provide a
preselected family `s |-> H(s)`.

Honest scope: this file does not enumerate the complete CMP99 Section-C factor
alphabet hidden by the printed word "etc.", and it does not prove the physical
reconstruction (3.107).  Those remain one named source input.  It also does not
identify the already validated fixed-carrier auxiliary specialization with
this dependent one.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

universe u v w x

namespace DependentArrowWalk

variable {ι : Type u} {Hom : ι → ι → Type v}

/-- Ordered list of the finite weakening carriers attached to the arrows of a
typed walk.  The empty walk activates no coordinate. -/
def activeCarriers {Delta : Type w}
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    {i j : ι} : DependentArrowWalk Hom i j → List (Finset Delta)
  | .nil _ => []
  | .cons head tail => factorActive head :: tail.activeCarriers factorActive

/-- Squarefree active carrier of a typed walk. -/
def active {Delta : Type w} [DecidableEq Delta]
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    {i j : ι} (walk : DependentArrowWalk Hom i j) : Finset Delta :=
  (walk.activeCarriers factorActive).foldr (· ∪ ·) ∅

@[simp] theorem activeCarriers_nil {Delta : Type w}
    (factorActive : ∀ {i j}, Hom i j → Finset Delta) (i : ι) :
    (DependentArrowWalk.nil (Hom := Hom) i).activeCarriers factorActive = [] :=
  rfl

@[simp] theorem activeCarriers_cons {Delta : Type w}
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    {i j k : ι} (head : Hom i j) (tail : DependentArrowWalk Hom j k) :
    (DependentArrowWalk.cons head tail).activeCarriers factorActive =
      factorActive head :: tail.activeCarriers factorActive :=
  rfl

@[simp] theorem active_nil {Delta : Type w} [DecidableEq Delta]
    (factorActive : ∀ {i j}, Hom i j → Finset Delta) (i : ι) :
    (DependentArrowWalk.nil (Hom := Hom) i).active factorActive = ∅ :=
  rfl

@[simp] theorem active_cons {Delta : Type w} [DecidableEq Delta]
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    {i j k : ι} (head : Hom i j) (tail : DependentArrowWalk Hom j k) :
    (DependentArrowWalk.cons head tail).active factorActive =
      factorActive head ∪ tail.active factorActive :=
  rfl

/-- The weakening monomial of a typed walk is exactly the ordered product of
the genuinely new coordinates encountered along the walk. -/
theorem complexWeakeningMonomial_active_eq_visitedProduct
    {Delta : Type w} [DecidableEq Delta]
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    (sigma : Delta → ℂ) {i j : ι} (walk : DependentArrowWalk Hom i j) :
    cmp116ComplexWeakeningMonomial (walk.active factorActive) sigma =
      cmp116ComplexVisitedWeakeningProduct sigma ∅
        (walk.activeCarriers factorActive) := by
  exact (cmp116ComplexVisitedWeakeningProduct_empty sigma
    (walk.activeCarriers factorActive)).symm

end DependentArrowWalk

/-- One named source input for the dependent physical walk family.  The arrow
alphabet, endpoints, active carrier and term are parameters of the type, so
the certificate cannot hide a different weakened family. -/
structure CMP116Lemma1DependentWalkSourceCertificate
    {ι : Type u} {Hom : ι → ι → Type v} {Delta : Type w}
    {E : Type x} [DecidableEq Delta]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {source target : ι}
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    (term : DependentArrowWalk Hom source target → E)
    (physicalH : E)
    (treeLength : DependentArrowWalk Hom source target → ℕ)
    (baseWeight : DependentArrowWalk Hom source target → ℝ)
    (B0 delta0 delta1 M kappa1 : ℝ) : Prop where
  walkCertificate : CMP116Lemma1WeakenedPropagatorCertificate
    (fun walk => walk.active factorActive) term treeLength baseWeight
      B0 delta0 delta1 M kappa1
  fullCoupling_reconstruction :
    (∑' walk : DependentArrowWalk Hom source target, term walk) = physicalH

namespace CMP116Lemma1DependentWalkSourceCertificate

variable
    {ι : Type u} {Hom : ι → ι → Type v} {Delta : Type w}
    {E : Type x} [DecidableEq Delta]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {source target : ι}
    {factorActive : ∀ {i j}, Hom i j → Finset Delta}
    {term : DependentArrowWalk Hom source target → E}
    {physicalH : E}
    {treeLength : DependentArrowWalk Hom source target → ℕ}
    {baseWeight : DependentArrowWalk Hom source target → ℝ}
    {B0 delta0 delta1 M kappa1 : ℝ}
    (C : CMP116Lemma1DependentWalkSourceCertificate
      factorActive term physicalH treeLength baseWeight
      B0 delta0 delta1 M kappa1)

include C

/-- The squarefree weakened family assembled internally from the typed walk
terms. -/
noncomputable def propagator (sigma : Delta → ℂ) : E :=
  C.walkCertificate.propagator sigma

/-- At full coupling the internally assembled family is exactly the named
physical operator. -/
theorem propagator_one :
    C.propagator (fun _ => 1) = physicalH := by
  rw [propagator, C.walkCertificate.propagator_one]
  exact C.fullCoupling_reconstruction

/-- CMP116 equation (1.11) for the dependent walk family. -/
theorem norm_propagator_le
    (sigma : Delta → ℂ)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1) :
    ‖C.propagator sigma‖ ≤ B0 * Real.exp (16 * kappa1) := by
  exact C.walkCertificate.norm_propagator_le sigma hsigma

/-- Coordinatewise analyticity of the same internally assembled family. -/
theorem hasDerivAt_propagator_update
    (sigma : Delta → ℂ) (d : Delta)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1)
    (z : ℂ) :
    HasDerivAt
      (fun t => C.propagator (Function.update sigma d t))
      (cmp116ComplexWeakenedRandomWalkSeriesDerivative
        (fun walk => walk.active factorActive) term sigma d)
      z := by
  exact C.walkCertificate.hasDerivAt_propagator_update sigma d hsigma z

end CMP116Lemma1DependentWalkSourceCertificate

end

end YangMills.RG
