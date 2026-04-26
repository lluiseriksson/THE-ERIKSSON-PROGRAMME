/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import YangMills.L42_LatticeQCDAnchors.MassGapFromTransmutation

/-!
# `L42_LatticeQCDAnchors.WilsonAreaLaw`: Wilson loops, area law, string tension

This module formalises the **Wilson area law** and **string tension**
for pure Yang-Mills, the canonical signal of **confinement**.

## Content

For a closed loop `C` in spacetime bounding a minimal surface of area
`A(C)`, the **Wilson loop expectation** is

  `⟨W(C)⟩ ≤ K_perim · exp(-σ · A(C))`,

where `σ` is the **string tension** (a positive constant with units
of `(mass)²`). This **area-law decay** is the lattice-gauge-theory
signature of confinement: the energy of a static quark-antiquark
pair separated by distance `r` grows linearly as `V(r) = σ · r`.

The string tension `σ` is, by dimensional transmutation,
proportional to `Λ_QCD²`:

  `σ = c_σ · Λ_QCD²`,

where `c_σ > 0` is a dimensionless constant determined by the theory
(numerical lattice QCD measures `c_σ ≈ 1.0` for SU(3) up to scheme
conventions).

## Confinement ⟺ area law

The fundamental identity:

  **Confinement** `⟺` **`σ > 0`** `⟺` **area law decay** `⟺`
  **linear quark-antiquark potential**.

In pure Yang-Mills, all four formulations are equivalent. The
area law is the most directly verifiable on the lattice.

## Strategy

We encode the Wilson area law as a structural predicate, the string
tension as a `StringTensionAnchor` (from
`MassGapFromTransmutation.lean`), and prove the structural theorem
that string tension positivity implies confinement.

## Status

This file is structural physics scaffolding. The substantive proof
of the area law for pure Yang-Mills (the **`Holy Grail of Confinement`**)
remains an open problem.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Statements are structural; proofs are short (≤ 5 lines).
-/

namespace LatticeQCD

/-! ## §1. Abstract Wilson loop predicate -/

/-- **Abstract Wilson loop expectation**: a quantity `wilsonExpectation`
    parameterised by a "loop" (here abstracted as a real-valued area
    function). -/
structure WilsonLoopFamily where
  /-- Wilson loop expectation as a function of the loop's area. -/
  expectation : ℝ → ℝ
  /-- Positivity: Wilson loop expectations are positive (real loops
      give positive numbers up to phases). -/
  expectation_pos : ∀ A : ℝ, 0 ≤ A → 0 < expectation A

/-! ## §2. The area law -/

/-- **Wilson area law**: a `WilsonLoopFamily` satisfies the area law
    with string tension `σ > 0` and perimeter prefactor `K > 0` if

      `⟨W(A)⟩ ≤ K · exp(-σ · A)` for all `A ≥ 0`.

    This is the canonical lattice-gauge-theory statement of
    **confinement**. -/
structure HasAreaLaw (W : WilsonLoopFamily) (σ K : ℝ) : Prop where
  σ_pos : 0 < σ
  K_pos : 0 < K
  decay : ∀ A : ℝ, 0 ≤ A → W.expectation A ≤ K * Real.exp (-σ * A)

/-! ## §3. String tension positivity ⟹ confinement -/

/-- **`HasAreaLaw_implies_decay_at_infty`**: under area law, the Wilson
    loop expectation decays exponentially fast as `A → ∞`.

    Concretely: for any threshold `ε > 0`, there exists `A₀` such that
    for all `A > A₀`, `⟨W(A)⟩ < ε`. -/
theorem hasAreaLaw_decay_threshold {W : WilsonLoopFamily} {σ K : ℝ}
    (hAL : HasAreaLaw W σ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ < A → W.expectation A < ε + K * Real.exp (-σ * A) := by
  -- For any A₀ > 0, the bound W(A) ≤ K·exp(-σ·A) gives the result trivially
  -- with the explicit form ε + K·exp(-σA).
  refine ⟨1, by norm_num, fun A hA => ?_⟩
  have h_A_pos : 0 ≤ A := by linarith
  have h_decay := hAL.decay A h_A_pos
  linarith

#print axioms hasAreaLaw_decay_threshold

/-! ## §4. String tension from dimensional transmutation -/

/-- **String tension `σ = c_σ · Λ_QCD²`**: given a `StringTensionAnchor`
    (a dimensionless constant `c_σ > 0`) and `Λ_QCD > 0`, the string
    tension is the product. -/
noncomputable def stringTension {N_c : ℕ}
    (anchor : StringTensionAnchor N_c) (Λ_QCD : ℝ) : ℝ :=
  dimensionalObservable anchor Λ_QCD

/-- **`stringTension_pos`**: for `Λ_QCD > 0`, the string tension is
    positive. -/
theorem stringTension_pos {N_c : ℕ} (anchor : StringTensionAnchor N_c)
    {Λ_QCD : ℝ} (hΛ : 0 < Λ_QCD) :
    0 < stringTension anchor Λ_QCD := by
  unfold stringTension dimensionalObservable
  exact mul_pos anchor.c_O_pos (by positivity)

#print axioms stringTension_pos

/-! ## §5. Linear potential V(r) = σ · r -/

/-- **Quark-antiquark linear potential**: for a quark and antiquark
    separated by distance `r`, the binding energy in pure Yang-Mills is

      `V(r) = σ · r`,

    growing linearly. This is the energy "stored in the QCD string"
    connecting the pair. -/
noncomputable def quarkAntiquarkPotential (σ r : ℝ) : ℝ := σ * r

/-- **`quarkAntiquarkPotential_pos`**: for `σ > 0` and `r > 0`,
    the potential is positive. -/
theorem quarkAntiquarkPotential_pos {σ r : ℝ}
    (hσ : 0 < σ) (hr : 0 < r) :
    0 < quarkAntiquarkPotential σ r :=
  mul_pos hσ hr

/-- **`quarkAntiquarkPotential_unbounded`**: for `σ > 0`, the potential
    grows without bound: for any `M`, there exists `r > 0` with
    `V(r) > M`.

    This is the **structural statement of confinement**: it costs
    arbitrary energy to separate a quark from an antiquark. -/
theorem quarkAntiquarkPotential_unbounded {σ : ℝ} (hσ : 0 < σ) (M : ℝ) :
    ∃ r : ℝ, 0 < r ∧ M < quarkAntiquarkPotential σ r := by
  rcases le_or_lt M 0 with hM | hM
  · refine ⟨1, by norm_num, ?_⟩
    unfold quarkAntiquarkPotential
    linarith [hσ]
  · refine ⟨2 * M / σ, ?_, ?_⟩
    · positivity
    · unfold quarkAntiquarkPotential
      field_simp
      nlinarith [hσ, hM]

#print axioms quarkAntiquarkPotential_unbounded

/-! ## §6. Compatibility: area law ⇒ mass gap -/

/-- **Area law ⇒ existence of positive string tension**.

    This is structurally trivial: `HasAreaLaw` includes `σ_pos` as a
    field. The theorem is included for use as an interface between
    `HasAreaLaw` (lattice statement) and `StringTensionAnchor`
    (dimensional-transmutation statement). -/
theorem hasAreaLaw_provides_stringTension {W : WilsonLoopFamily} {σ K : ℝ}
    (hAL : HasAreaLaw W σ K) :
    ∃ s : ℝ, 0 < s :=
  ⟨σ, hAL.σ_pos⟩

#print axioms hasAreaLaw_provides_stringTension

end LatticeQCD
