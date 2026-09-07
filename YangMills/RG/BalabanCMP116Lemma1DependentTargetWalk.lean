/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma1DependentVisitedWalk

/-!
# Target-total dependent walks for the CMP116 Lemma-1 weakening

VALIDATED: a fresh Colab Pro+ CPU/high-RAM clone at source SHA
`fe5bfdd288eacee5239bc458abb225bf1ce55209` completed the focal build
(`8458` jobs) and all four oracle declarations with exactly
`[propext, Classical.choice, Quot.sound]` on 2026-08-03.  The evidence archive
has SHA-256 `dd2037e8155eb64ea249d1e41d28646c1288b9b8da9be41ddca2fe4437939a24`.

CMP99 equation (3.107) suppresses the intermediate carrier types in its
displayed expansion of the square propagator `G`.  The rectangular minimizer
`H` is represented later by (3.126), and Theorem 3.12 transfers the random-walk
conclusions to it.  The reconstructed Section-C generator instead returns a
sigma type

`Sigma target, DependentArrowWalk Hom source target`.

This module makes that sigma type the literal index of the L1 random-walk
series.  Hence a physical specialization must keep the terminal carrier in
every summand and prove one total reconstruction over all targets.  It cannot
silently select a target, forget the readout, or replace the source statement
by a family of independently chosen fixed-target identities.

Honest scope: the complete CMP99 factor alphabet hidden by the printed word
"etc.", the physical endpoint readout, and the `H` reconstruction obtained
from the `G` series, (3.126), and Theorem 3.12 remain one named source input.
This module only fixes the type of that input.  It does not identify the
already reconstructed displayed subalphabet with the complete propagator and
it does not accept a free weakened family.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

universe u v w x

/-- A dependent walk with fixed source and an explicit, varying terminal
carrier.  The sigma package is the endpoint gate required by the physical
rectangular reconstruction. -/
abbrev CMP116Lemma1DependentTargetWalk
    {ι : Type u} (Hom : ι → ι → Type v) (source : ι) :=
  Σ target, DependentArrowWalk Hom source target

namespace CMP116Lemma1DependentTargetWalk

variable {ι : Type u} {Hom : ι → ι → Type v} {source : ι}

/-- Squarefree carrier of a target-total dependent walk. -/
def active {Delta : Type w} [DecidableEq Delta]
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    (walk : CMP116Lemma1DependentTargetWalk Hom source) : Finset Delta :=
  walk.2.active factorActive

@[simp] theorem active_mk {Delta : Type w} [DecidableEq Delta]
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    {target : ι} (walk : DependentArrowWalk Hom source target) :
    active factorActive ⟨target, walk⟩ = walk.active factorActive :=
  rfl

end CMP116Lemma1DependentTargetWalk

/-- One source input for the physical endpoint-total walk family.  The term is
indexed by both its terminal carrier and its typed walk.  The only physical
identification accepted is the total full-coupling reconstruction over this
same sigma type. -/
structure CMP116Lemma1DependentTargetWalkSourceCertificate
    {ι : Type u} {Hom : ι → ι → Type v} {Delta : Type w}
    {E : Type x} [DecidableEq Delta]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {source : ι}
    (factorActive : ∀ {i j}, Hom i j → Finset Delta)
    (term : CMP116Lemma1DependentTargetWalk Hom source → E)
    (physicalH : E)
    (treeLength : CMP116Lemma1DependentTargetWalk Hom source → ℕ)
    (baseWeight : CMP116Lemma1DependentTargetWalk Hom source → ℝ)
    (B0 delta0 delta1 M kappa1 : ℝ) : Prop where
  walkCertificate : CMP116Lemma1WeakenedPropagatorCertificate
    (CMP116Lemma1DependentTargetWalk.active factorActive)
    term treeLength baseWeight B0 delta0 delta1 M kappa1
  fullCoupling_reconstruction :
    (∑' walk : CMP116Lemma1DependentTargetWalk Hom source, term walk) =
      physicalH

namespace CMP116Lemma1DependentTargetWalkSourceCertificate

variable
    {ι : Type u} {Hom : ι → ι → Type v} {Delta : Type w}
    {E : Type x} [DecidableEq Delta]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {source : ι}
    {factorActive : ∀ {i j}, Hom i j → Finset Delta}
    {term : CMP116Lemma1DependentTargetWalk Hom source → E}
    {physicalH : E}
    {treeLength : CMP116Lemma1DependentTargetWalk Hom source → ℕ}
    {baseWeight : CMP116Lemma1DependentTargetWalk Hom source → ℝ}
    {B0 delta0 delta1 M kappa1 : ℝ}
    (C : CMP116Lemma1DependentTargetWalkSourceCertificate
      factorActive term physicalH treeLength baseWeight
      B0 delta0 delta1 M kappa1)

include C

/-- The endpoint-total squarefree weakened family, assembled internally from
the sigma-indexed physical terms. -/
noncomputable def propagator (sigma : Delta → ℂ) : E :=
  C.walkCertificate.propagator sigma

/-- At full coupling, summing every terminal readout recovers the named
physical operator.  No target is discarded. -/
theorem propagator_one :
    C.propagator (fun _ => 1) = physicalH := by
  rw [propagator, C.walkCertificate.propagator_one]
  exact C.fullCoupling_reconstruction

/-- CMP116 equation (1.11) for the endpoint-total dependent family. -/
theorem norm_propagator_le
    (sigma : Delta → ℂ)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1) :
    ‖C.propagator sigma‖ ≤ B0 * Real.exp (16 * kappa1) := by
  exact C.walkCertificate.norm_propagator_le sigma hsigma

/-- Coordinatewise analyticity of the same internally assembled total
family. -/
theorem hasDerivAt_propagator_update
    (sigma : Delta → ℂ) (d : Delta)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1)
    (z : ℂ) :
    HasDerivAt
      (fun t => C.propagator (Function.update sigma d t))
      (cmp116ComplexWeakenedRandomWalkSeriesDerivative
        (CMP116Lemma1DependentTargetWalk.active factorActive)
        term sigma d)
      z := by
  exact C.walkCertificate.hasDerivAt_propagator_update sigma d hsigma z

end CMP116Lemma1DependentTargetWalkSourceCertificate

end

end YangMills.RG
