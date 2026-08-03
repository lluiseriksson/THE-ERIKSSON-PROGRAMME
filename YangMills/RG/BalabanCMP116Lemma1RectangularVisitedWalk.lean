/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma1WeakenedPropagatorBound
import YangMills.RG.BalabanCMP116VisitedWeakeningFactorization

/-!
# Rectangular visited walks for the printed CMP116 `H(s)`

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its results have not yet been verified by the Lean compiler.

CMP116 printed page 3 defines `H(s)` by weakening the linear generalized-walk
expansion (1.6), cited there to CMP99 (3.107).  Every distinct cube meeting the
union of the localization domains is charged exactly once.  The distinguished
head of an `H` walk is rectangular, while all continuation factors are square.

This module supplies that missing algebraic shape.  The weakened family is
constructed internally from the rectangular walk terms and their squarefree
active carriers.  A source certificate may provide the physical factors, the
entrywise CMP99 walk estimates and the exact reconstruction at `s = 1`; it may
not provide a preselected family `s |-> H(s)`.

Honest scope: no physical CMP99 rectangular factors are installed here.  In
particular this module does not identify the algebraic family
`C(s) Q* (Q C(s) Q*)^-1` with the printed `H(s)`.  A later physical module must
fix `R0`, `R`, `successors`, and `domainActive` to the source objects and prove
the full-coupling reconstruction.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

universe u v w x y

namespace CMP99GeneralizedWalk

variable {Label : Type u} {Domain : Type v}
variable {Output : Type w} {State : Type x}
variable [Fintype State] [DecidableEq State]

/-- The source product with one rectangular head and square continuation
factors.  Its order is literally `R0(X0) R_alpha1(X1) ... R_alphan(Xn)` from
CMP116 (1.6). -/
def rectangularTerm
    (R0 : Domain → Matrix Output State ℂ)
    (R : Label → Domain → Matrix State State ℂ)
    (walk : CMP99GeneralizedWalk Label Domain) :
    Matrix Output State ℂ :=
  R0 walk.head *
    (walk.tail.map fun step => R step.label step.domain).prod

@[simp]
theorem rectangularTerm_nil
    (R0 : Domain → Matrix Output State ℂ)
    (R : Label → Domain → Matrix State State ℂ)
    (X0 : Domain) :
    rectangularTerm R0 R ⟨X0, []⟩ = R0 X0 := by
  simp [rectangularTerm]

@[simp]
theorem rectangularTerm_cons
    (R0 : Domain → Matrix Output State ℂ)
    (R : Label → Domain → Matrix State State ℂ)
    (X0 : Domain) (step : CMP99WalkStep Label Domain)
    (tail : List (CMP99WalkStep Label Domain)) :
    rectangularTerm R0 R ⟨X0, step :: tail⟩ =
      rectangularTerm R0 R ⟨X0, []⟩ *
        (R step.label step.domain ::
          tail.map (fun next => R next.label next.domain)).prod := by
  simp [rectangularTerm]

end CMP99GeneralizedWalk

/-- All source walks generated from every possible head domain by one finite
successor family.  The outer head is retained, so the conversion below is the
literal walk of (1.6), not an arbitrary enumeration. -/
abbrev CMP99RectangularGeneratedWalk
    {Label : Type u} {Domain : Type v}
    [DecidableEq Label] [DecidableEq Domain]
    (successors : Domain → Finset (CMP99WalkStep Label Domain)) :=
  Σ X0 : Domain, CMP99AnchoredWalk successors X0

/-- Forget only the generation certificate and recover the source walk. -/
def CMP99RectangularGeneratedWalk.toGeneralizedWalk
    {Label : Type u} {Domain : Type v}
    [DecidableEq Label] [DecidableEq Domain]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    (walk : CMP99RectangularGeneratedWalk successors) :
    CMP99GeneralizedWalk Label Domain :=
  walk.2.toGeneralizedWalk

/-- The exact squarefree carrier: the union of the active cubes of every
localization domain in the generated source walk. -/
def cmp116Lemma1RectangularGeneratedWalkActive
    {Label : Type u} {Domain : Type v} {Delta : Type y}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    (domainActive : Domain → Finset Delta)
    (walk : CMP99RectangularGeneratedWalk successors) : Finset Delta :=
  walk.toGeneralizedWalk.active domainActive

/-- The sigma-independent rectangular term of one generated walk. -/
def cmp116Lemma1RectangularGeneratedWalkTerm
    {Label : Type u} {Domain : Type v}
    {Output : Type w} {State : Type x}
    [DecidableEq Label] [DecidableEq Domain]
    [Fintype State] [DecidableEq State]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    (R0 : Domain → Matrix Output State ℂ)
    (R : Label → Domain → Matrix State State ℂ)
    (walk : CMP99RectangularGeneratedWalk successors) :
    Matrix Output State ℂ :=
  walk.toGeneralizedWalk.rectangularTerm R0 R

/-- Scalar entry of the sigma-independent rectangular term. -/
def cmp116Lemma1RectangularGeneratedWalkEntryTerm
    {Label : Type u} {Domain : Type v}
    {Output : Type w} {State : Type x}
    [DecidableEq Label] [DecidableEq Domain]
    [Fintype State] [DecidableEq State]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    (R0 : Domain → Matrix Output State ℂ)
    (R : Label → Domain → Matrix State State ℂ)
    (row : Output) (col : State)
    (walk : CMP99RectangularGeneratedWalk successors) : ℂ :=
  cmp116Lemma1RectangularGeneratedWalkTerm R0 R walk row col

/-- The union monomial is exactly the ordered visited-state product.  A cube
activated at several steps is charged only on its first visit. -/
theorem cmp116Lemma1RectangularGeneratedWalkMonomial_eq_visited
    {Label : Type u} {Domain : Type v} {Delta : Type y}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    (domainActive : Domain → Finset Delta)
    (sigma : Delta → ℂ)
    (walk : CMP99RectangularGeneratedWalk successors) :
    cmp116ComplexWeakeningMonomial
        (cmp116Lemma1RectangularGeneratedWalkActive domainActive walk) sigma =
      cmp116ComplexVisitedWeakeningProduct sigma ∅
        (walk.toGeneralizedWalk.domains.map domainActive) := by
  exact
    walk.toGeneralizedWalk.complexWeakeningMonomial_active_eq_visitedProduct
      domainActive sigma

/-- The one named source input for a rectangular physical specialization.
All data before the proof fields are parameters of the type, so the
certificate cannot hide a different weakened family. -/
structure CMP116Lemma1RectangularWalkSourceCertificate
    {Label : Type u} {Domain : Type v} {Delta : Type y}
    {Output : Type w} {State : Type x}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    [Fintype Output] [DecidableEq Output]
    [Fintype State] [DecidableEq State]
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (domainActive : Domain → Finset Delta)
    (R0 : Domain → Matrix Output State ℂ)
    (R : Label → Domain → Matrix State State ℂ)
    (physicalH : Matrix Output State ℂ)
    (treeLength : CMP99RectangularGeneratedWalk successors → ℕ)
    (baseWeight : CMP99RectangularGeneratedWalk successors → ℝ)
    (B0 delta0 delta1 M kappa1 : ℝ) : Prop where
  entryCertificate : ∀ row col,
    CMP116Lemma1WeakenedPropagatorCertificate
      (cmp116Lemma1RectangularGeneratedWalkActive domainActive)
      (cmp116Lemma1RectangularGeneratedWalkEntryTerm R0 R row col)
      treeLength baseWeight B0 delta0 delta1 M kappa1
  fullCoupling_reconstruction : ∀ row col,
    (∑' walk : CMP99RectangularGeneratedWalk successors,
      cmp116Lemma1RectangularGeneratedWalkEntryTerm
        R0 R row col walk) = physicalH row col

namespace CMP116Lemma1RectangularWalkSourceCertificate

variable
    {Label : Type u} {Domain : Type v} {Delta : Type y}
    {Output : Type w} {State : Type x}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    [Fintype Output] [DecidableEq Output]
    [Fintype State] [DecidableEq State]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    {domainActive : Domain → Finset Delta}
    {R0 : Domain → Matrix Output State ℂ}
    {R : Label → Domain → Matrix State State ℂ}
    {physicalH : Matrix Output State ℂ}
    {treeLength : CMP99RectangularGeneratedWalk successors → ℕ}
    {baseWeight : CMP99RectangularGeneratedWalk successors → ℝ}
    {B0 delta0 delta1 M kappa1 : ℝ}
    (C : CMP116Lemma1RectangularWalkSourceCertificate
      successors domainActive R0 R physicalH treeLength baseWeight
      B0 delta0 delta1 M kappa1)

include C

/-- The printed squarefree weakened family, assembled entrywise from generic
L1.  It is constructed from the walk factors; it is not a certificate field. -/
noncomputable def propagator (sigma : Delta → ℂ) :
    Matrix Output State ℂ :=
  fun row col => (C.entryCertificate row col).propagator sigma

/-- At full coupling the internally constructed family is the physical
rectangular propagator named in the source certificate. -/
theorem propagator_one :
    C.propagator (fun _ => 1) = physicalH := by
  ext row col
  rw [propagator]
  rw [(C.entryCertificate row col).propagator_one]
  exact C.fullCoupling_reconstruction row col

/-- Entrywise form of CMP116 equation (1.11) for the rectangular walk
family.  No matrix norm or post-selected budget is introduced. -/
theorem norm_propagator_apply_le
    (sigma : Delta → ℂ)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1)
    (row : Output) (col : State) :
    ‖C.propagator sigma row col‖ ≤ B0 * Real.exp (16 * kappa1) := by
  exact (C.entryCertificate row col).norm_propagator_le sigma hsigma

end CMP116Lemma1RectangularWalkSourceCertificate

end

end YangMills.RG
