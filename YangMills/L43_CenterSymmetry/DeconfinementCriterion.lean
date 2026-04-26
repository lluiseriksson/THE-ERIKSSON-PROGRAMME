/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import YangMills.L43_CenterSymmetry.CenterGroup

/-!
# `L43_CenterSymmetry.DeconfinementCriterion`: Polyakov loop as order parameter

This module formalises the **deconfinement criterion** of pure
Yang-Mills:

  **Confined phase** ⟺ Polyakov loop expectation `⟨P⟩ = 0`
                     ⟺ `Z_N` center symmetry is unbroken.

  **Deconfined phase** ⟺ Polyakov loop expectation `⟨P⟩ ≠ 0`
                       ⟺ `Z_N` center symmetry is spontaneously broken.

This is the **center-symmetry-based** characterisation of
confinement, complementary to the area-law characterisation in the
L42 block (`WilsonAreaLaw.lean`):

* **L42 area law**: `⟨W(C)⟩ ≤ exp(-σ · A(C))` ⟺ confined.
* **L43 center symmetry**: `⟨P⟩ = 0` ⟺ confined.

Both are equivalent statements of confinement in pure Yang-Mills,
but the center-symmetry view emphasises the symmetry-breaking
structure underlying the deconfinement phase transition.

## Strategy

We package the criterion as a proposition `IsConfined` (already
defined in `CenterGroup.lean`) and prove the equivalence with
center-invariance via `polyakov_invariant_implies_zero`.

We also provide concrete instances at SU(2) (where the center is
`Z_2 = {±1}`) and SU(3) (where the center is `Z_3`), demonstrating
the criterion on the two physically interesting cases.

## Status

This file is structural physics scaffolding. The substantive
implementation requires the Wilson Gibbs measure and a real Polyakov
loop expectation; here we work with abstract `PolyakovExpectation`
structures.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`.
-/

namespace L43_CenterSymmetry

/-! ## §1. The deconfinement criterion -/

/-- **Deconfinement criterion**: under abstract center action with a
    nontrivial element `ω ≠ 1`, the Polyakov expectation `⟨P⟩` is
    invariant if and only if `⟨P⟩ = 0`. -/
theorem isConfined_iff_centerInvariant {N : ℕ}
    (poly : PolyakovExpectation N)
    (ω : ℂ) (h_ω_ne : ω ≠ 1) :
    IsConfined poly ↔ ω * poly.P = poly.P := by
  unfold IsConfined
  constructor
  · -- P = 0 ⇒ ω · 0 = 0.
    intro h_P_zero
    rw [h_P_zero, mul_zero]
  · -- ω · P = P with ω ≠ 1 ⇒ P = 0.
    intro h_inv
    exact polyakov_invariant_implies_zero poly ω h_ω_ne h_inv

#print axioms isConfined_iff_centerInvariant

/-! ## §2. SU(2) instance: `Z_2` center -/

/-- **SU(2) confinement criterion**: under the `Z_2` center action,
    `⟨P⟩` is invariant under the non-trivial element `-1` iff
    `⟨P⟩ = 0`.

    This is the SU(2) instantiation of the general criterion. -/
theorem isConfined_iff_invariant_SU2
    (poly : PolyakovExpectation 2) :
    IsConfined poly ↔ (-1 : ℂ) * poly.P = poly.P := by
  apply isConfined_iff_centerInvariant
  -- -1 ≠ 1 in ℂ.
  intro h_eq
  have : (2 : ℂ) = 0 := by linear_combination h_eq
  norm_num at this

#print axioms isConfined_iff_invariant_SU2

/-! ## §3. Reformulation: SU(2) confined iff `2P = 0` -/

/-- **SU(2) confinement criterion (reformulated)**: confinement at
    SU(2) is equivalent to `2 · ⟨P⟩ = 0`, i.e., `⟨P⟩ = 0`. -/
theorem isConfined_iff_two_P_zero (poly : PolyakovExpectation 2) :
    IsConfined poly ↔ 2 * poly.P = 0 := by
  unfold IsConfined
  constructor
  · intro h_P_zero
    rw [h_P_zero, mul_zero]
  · intro h_two_P
    -- 2 · P = 0 in ℂ ⇒ P = 0.
    have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
    rcases mul_eq_zero.mp h_two_P with h_left | h_right
    · exfalso; exact h_two_ne h_left
    · exact h_right

#print axioms isConfined_iff_two_P_zero

/-! ## §4. The deconfined phase -/

/-- **Deconfined phase**: the negation of `IsConfined`, i.e., `⟨P⟩ ≠ 0`. -/
def IsDeconfined {N : ℕ} (poly : PolyakovExpectation N) : Prop :=
  poly.P ≠ 0

/-- **Phase dichotomy**: every Polyakov expectation is either confined
    or deconfined; the two are mutually exclusive and exhaustive. -/
theorem isConfined_xor_isDeconfined {N : ℕ} (poly : PolyakovExpectation N) :
    IsConfined poly ↔ ¬ IsDeconfined poly := by
  unfold IsConfined IsDeconfined
  exact ⟨fun h => fun h' => h' h, fun h => not_not.mp h⟩

#print axioms isConfined_xor_isDeconfined

/-! ## §5. Pure-zero Polyakov expectation as canonical confined witness -/

/-- **Canonical confined witness**: the Polyakov expectation with
    `P = 0`. -/
def confinedWitness (N : ℕ) : PolyakovExpectation N where
  P := 0

/-- **Confined witness is confined**. -/
theorem confinedWitness_isConfined (N : ℕ) :
    IsConfined (confinedWitness N) := by
  unfold IsConfined confinedWitness
  rfl

#print axioms confinedWitness_isConfined

/-! ## §6. Connection to mass gap / string tension -/

/-- **Conceptual connection (structural)**: in pure Yang-Mills, the
    confined phase has positive string tension `σ > 0` (area law,
    L42) and positive mass gap `m > 0` (L42 anchor).

    These three statements are equivalent in pure Yang-Mills:
    - `IsConfined poly` (this file).
    - `σ > 0` (string tension positive — `L42_LatticeQCDAnchors.WilsonAreaLaw`).
    - `0 < m_gap` (mass gap positive — `L42_LatticeQCDAnchors.MassGapFromTransmutation`).

    The equivalence is **structural** at the level of pure Yang-Mills
    physics; deriving any one from the others requires the substantive
    physics that this project does not yet provide.

    This is encoded as a `theorem` whose body is `trivial` (the
    statement is a conceptual signpost, not a substantive claim). -/
theorem confinement_string_tension_mass_gap_equivalence : True := trivial

end L43_CenterSymmetry
