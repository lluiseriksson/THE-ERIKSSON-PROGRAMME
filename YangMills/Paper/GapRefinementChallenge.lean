/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Positive gaps versus arbitrarily small excitations

This module isolates the quantifier obstruction behind regulator-uniform mass-gap
claims.

The elementary largest-natural-number contradiction answers a proposed maximum
`N` with `N + 1`.  For a positive spectral gap the order is reversed: a proposed
lower bound `Δ > 0` is defeated by one physical excitation with energy
`0 < E < Δ`.

For a regulator-indexed family, a positive gap at every fixed regulator,

`∀ r, ∃ Δᵣ > 0, ...`,

is strictly weaker than a single regulator-uniform gap,

`∃ Δ > 0, ∀ r, ...`.

The declarations below formalize that distinction and give an explicit
`Δ / 2` counterexample.

This is logical infrastructure only.  It does not construct the Yang--Mills
Hamiltonian, identify its physical spectrum, prove the model-specific activity
estimate `hRpoly`, remove a regulator, or establish the continuum Clay mass gap.

Oracle target: `[propext, Classical.choice, Quot.sound]` or purer.  No `sorry`,
no project axioms.
-/

namespace YangMills

/-- `excitation E` is understood to mean that `E` is the energy above the
vacuum of a physical non-vacuum excitation.  A positive energy gap is one
strictly positive lower bound for all such energies. -/
def HasPositiveEnergyGap (excitation : ℝ → Prop) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧ ∀ E : ℝ, excitation E → Δ ≤ E

/-- Every proposed positive lower bound is challenged by a smaller, still
strictly positive, excitation energy. -/
def HasArbitrarilySmallPositiveExcitations (excitation : ℝ → Prop) : Prop :=
  ∀ Δ : ℝ, 0 < Δ →
    ∃ E : ℝ, excitation E ∧ 0 < E ∧ E < Δ

/-- Arbitrarily small positive excitation energies rule out a positive gap. -/
theorem not_hasPositiveEnergyGap_of_arbitrarilySmallPositiveExcitations
    {excitation : ℝ → Prop}
    (hsmall : HasArbitrarilySmallPositiveExcitations excitation) :
    ¬ HasPositiveEnergyGap excitation := by
  rintro ⟨Δ, hΔ, hgap⟩
  obtain ⟨E, hE, _hEpos, hlt⟩ := hsmall Δ hΔ
  exact (not_lt_of_ge (hgap E hE)) hlt

/-- If every declared excitation has positive energy, failure of a positive
gap produces an excitation below every proposed positive lower bound. -/
theorem arbitrarilySmallPositiveExcitations_of_not_hasPositiveEnergyGap
    {excitation : ℝ → Prop}
    (hpositive : ∀ E : ℝ, excitation E → 0 < E)
    (hnogap : ¬ HasPositiveEnergyGap excitation) :
    HasArbitrarilySmallPositiveExcitations excitation := by
  intro Δ hΔ
  by_contra hnone
  apply hnogap
  refine ⟨Δ, hΔ, ?_⟩
  intro E hE
  exact le_of_not_gt fun hlt =>
    hnone ⟨E, hE, hpositive E hE, hlt⟩

/-- Under positivity of all declared excitations, having no positive gap is
equivalent to admitting arbitrarily small positive excitations. -/
theorem not_hasPositiveEnergyGap_iff_arbitrarilySmallPositiveExcitations
    {excitation : ℝ → Prop}
    (hpositive : ∀ E : ℝ, excitation E → 0 < E) :
    ¬ HasPositiveEnergyGap excitation ↔
      HasArbitrarilySmallPositiveExcitations excitation := by
  constructor
  · exact arbitrarilySmallPositiveExcitations_of_not_hasPositiveEnergyGap hpositive
  · exact not_hasPositiveEnergyGap_of_arbitrarilySmallPositiveExcitations

/-- Every fixed regulator has some positive lower bound, possibly depending on
the regulator. -/
def HasStagewisePositiveEnergyGap {Regulator : Type*}
    (excitation : Regulator → ℝ → Prop) : Prop :=
  ∀ r, HasPositiveEnergyGap (excitation r)

/-- One strictly positive lower bound works simultaneously for every regulator
and every declared excitation. -/
def HasUniformPositiveEnergyGap {Regulator : Type*}
    (excitation : Regulator → ℝ → Prop) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧
    ∀ r E, excitation r E → Δ ≤ E

/-- A regulator-uniform positive gap immediately gives a positive gap at each
fixed regulator, using the same lower bound at every stage. -/
theorem hasUniformPositiveEnergyGap_hasStagewisePositiveEnergyGap
    {Regulator : Type*} {excitation : Regulator → ℝ → Prop}
    (huniform : HasUniformPositiveEnergyGap excitation) :
    HasStagewisePositiveEnergyGap excitation := by
  rcases huniform with ⟨Δ, hΔ, hgap⟩
  intro r
  exact ⟨Δ, hΔ, fun E hE => hgap r E hE⟩

/-- **Exact uniform-gap criterion.**  Stagewise gaps promote to a regulator-
uniform gap exactly when their chosen lower bounds are themselves bounded below
by one positive constant independent of the regulator.

This is the continuum-limit quantifier that cannot be replaced by merely
knowing `∀ r, ∃ Δ_r > 0`. -/
theorem hasUniformPositiveEnergyGap_iff_exists_stagewise_gaps_boundedBelow
    {Regulator : Type*} {excitation : Regulator → ℝ → Prop} :
    HasUniformPositiveEnergyGap excitation ↔
      ∃ gap : Regulator → ℝ,
        (∀ r, 0 < gap r ∧ ∀ E : ℝ, excitation r E → gap r ≤ E) ∧
        ∃ Δ : ℝ, 0 < Δ ∧ ∀ r, Δ ≤ gap r := by
  constructor
  · rintro ⟨Δ, hΔ, hgap⟩
    refine ⟨fun _ => Δ, ?_, ⟨Δ, hΔ, fun _ => le_rfl⟩⟩
    intro r
    exact ⟨hΔ, fun E hE => hgap r E hE⟩
  · rintro ⟨gap, hstage, Δ, hΔ, hlower⟩
    refine ⟨Δ, hΔ, ?_⟩
    intro r E hE
    exact le_trans (hlower r) ((hstage r).2 E hE)

/-- Refinement can challenge every proposed regulator-uniform lower bound. -/
def RefinementsProduceArbitrarilySmallPositiveExcitations
    {Regulator : Type*} (excitation : Regulator → ℝ → Prop) : Prop :=
  ∀ Δ : ℝ, 0 < Δ →
    ∃ r E, excitation r E ∧ 0 < E ∧ E < Δ

/-- A refinement family producing arbitrarily small positive excitations
cannot have a regulator-uniform positive gap. -/
theorem
    not_hasUniformPositiveEnergyGap_of_refinementsProduceArbitrarilySmallPositiveExcitations
    {Regulator : Type*} {excitation : Regulator → ℝ → Prop}
    (hsmall :
      RefinementsProduceArbitrarilySmallPositiveExcitations excitation) :
    ¬ HasUniformPositiveEnergyGap excitation := by
  rintro ⟨Δ, hΔ, hgap⟩
  obtain ⟨r, E, hE, _hEpos, hlt⟩ := hsmall Δ hΔ
  exact (not_lt_of_ge (hgap r E hE)) hlt

/-- If every declared regulator-dependent excitation has positive energy, then
failure of a regulator-uniform positive gap produces arbitrarily small positive
excitations along the refinement family. -/
theorem
    refinementsProduceArbitrarilySmallPositiveExcitations_of_not_hasUniformPositiveEnergyGap
    {Regulator : Type*} {excitation : Regulator → ℝ → Prop}
    (hpositive : ∀ (r : Regulator) (E : ℝ), excitation r E → 0 < E)
    (hnogap : ¬ HasUniformPositiveEnergyGap excitation) :
    RefinementsProduceArbitrarilySmallPositiveExcitations excitation := by
  intro Δ hΔ
  by_contra hnone
  apply hnogap
  refine ⟨Δ, hΔ, ?_⟩
  intro r E hE
  exact le_of_not_gt fun hlt =>
    hnone ⟨r, E, hE, hpositive r E hE, hlt⟩

/-- Under positivity of all declared regulator-dependent excitations, failure
of a regulator-uniform positive gap is equivalent to the existence of
arbitrarily small positive excitation energies along the refinement family. -/
theorem
    not_hasUniformPositiveEnergyGap_iff_refinementsProduceArbitrarilySmallPositiveExcitations
    {Regulator : Type*} {excitation : Regulator → ℝ → Prop}
    (hpositive : ∀ (r : Regulator) (E : ℝ), excitation r E → 0 < E) :
    ¬ HasUniformPositiveEnergyGap excitation ↔
      RefinementsProduceArbitrarilySmallPositiveExcitations excitation := by
  constructor
  · exact
      refinementsProduceArbitrarilySmallPositiveExcitations_of_not_hasUniformPositiveEnergyGap
        hpositive
  · exact
      not_hasUniformPositiveEnergyGap_of_refinementsProduceArbitrarilySmallPositiveExcitations

/-- If refinements produce arbitrarily small positive excitation energies, then
no choice of stagewise positive lower bounds can itself be bounded below by one
positive regulator-independent constant. -/
theorem
    not_exists_stagewise_gaps_boundedBelow_of_refinementsProduceArbitrarilySmallPositiveExcitations
    {Regulator : Type*} {excitation : Regulator → ℝ → Prop}
    (hsmall :
      RefinementsProduceArbitrarilySmallPositiveExcitations excitation) :
    ¬ ∃ gap : Regulator → ℝ,
      (∀ r, 0 < gap r ∧ ∀ E : ℝ, excitation r E → gap r ≤ E) ∧
      ∃ Δ : ℝ, 0 < Δ ∧ ∀ r, Δ ≤ gap r := by
  intro hbounded
  exact not_hasUniformPositiveEnergyGap_of_refinementsProduceArbitrarilySmallPositiveExcitations
    hsmall ((hasUniformPositiveEnergyGap_iff_exists_stagewise_gaps_boundedBelow
      (excitation := excitation)).2 hbounded)

/-- Positive real scales used by the explicit quantifier counterexample. -/
abbrev PositiveGapScale := {δ : ℝ // 0 < δ}

/-- At scale `δ`, the sole declared excitation has energy `δ / 2`. -/
def halfScaleExcitation (δ : PositiveGapScale) (E : ℝ) : Prop :=
  E = δ.1 / 2

/-- Every individual scale in the `δ / 2` example has a positive gap. -/
theorem halfScaleExcitation_hasStagewisePositiveEnergyGap :
    HasStagewisePositiveEnergyGap halfScaleExcitation := by
  intro δ
  refine ⟨δ.1 / 2, div_pos δ.2 (by norm_num), ?_⟩
  intro E hE
  change E = δ.1 / 2 at hE
  subst E
  exact le_rfl

/-- Nevertheless, the `δ / 2` family challenges every proposed uniform gap. -/
theorem
    halfScaleExcitation_refinementsProduceArbitrarilySmallPositiveExcitations :
    RefinementsProduceArbitrarilySmallPositiveExcitations
      halfScaleExcitation := by
  intro Δ hΔ
  refine ⟨⟨Δ, hΔ⟩, Δ / 2, rfl, div_pos hΔ (by norm_num), ?_⟩
  linarith

/-- The explicit family has no regulator-uniform positive gap. -/
theorem halfScaleExcitation_not_hasUniformPositiveEnergyGap :
    ¬ HasUniformPositiveEnergyGap halfScaleExcitation :=
  not_hasUniformPositiveEnergyGap_of_refinementsProduceArbitrarilySmallPositiveExcitations
    halfScaleExcitation_refinementsProduceArbitrarilySmallPositiveExcitations

/-- Machine-checked separation of stagewise and uniform positive gaps. -/
theorem halfScaleExcitation_stagewise_but_not_uniform :
    HasStagewisePositiveEnergyGap halfScaleExcitation ∧
      ¬ HasUniformPositiveEnergyGap halfScaleExcitation :=
  ⟨halfScaleExcitation_hasStagewisePositiveEnergyGap,
    halfScaleExcitation_not_hasUniformPositiveEnergyGap⟩

/-- In the explicit `δ / 2` family, no choice of stagewise lower bounds has a
positive regulator-independent lower bound. -/
theorem halfScaleExcitation_no_stagewise_gaps_boundedBelow :
    ¬ ∃ gap : PositiveGapScale → ℝ,
      (∀ δ, 0 < gap δ ∧ ∀ E : ℝ, halfScaleExcitation δ E → gap δ ≤ E) ∧
      ∃ Δ : ℝ, 0 < Δ ∧ ∀ δ, Δ ≤ gap δ := by
  intro h
  exact halfScaleExcitation_not_hasUniformPositiveEnergyGap
    ((hasUniformPositiveEnergyGap_iff_exists_stagewise_gaps_boundedBelow
      (excitation := halfScaleExcitation)).2 h)

end YangMills
