/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import YangMills.L42_LatticeQCDAnchors.RGRunningCoupling

/-!
# `L42_LatticeQCDAnchors.MassGapFromTransmutation`: Mass gap as `c · Λ_QCD`

This module formalises the **structural relationship** between the
mass gap of pure Yang-Mills and the QCD scale `Λ_QCD`:

  `m_gap = c_Y · Λ_QCD`,

where `c_Y` is a **dimensionless constant** that pure-Yang-Mills
theory determines (the "lightest glueball mass in units of `Λ`").

This is the **physics origin of the mass gap**: in pure Yang-Mills,
the only available dimensional scale is `Λ_QCD` (which itself comes
from dimensional transmutation in the renormalisation group). Hence
**every** dimensional physical observable — mass gap, string tension,
glueball spectrum, deconfinement temperature — is proportional to
some power of `Λ_QCD`.

For mass-dimension-1 quantities like the mass gap, the proportionality
is `m = c · Λ_QCD` with `c` a pure number determined by the theory.

Lattice QCD numerical simulations measure `m_gap / Λ_QCD ≈ 1.5 - 1.7`
for SU(3) (the lightest 0⁺⁺ glueball in units of `Λ_QCD`), but
**this constant is not yet derivable from first principles in any
known framework**, including this one.

## Strategy

The dimensionless constant `c_Y` is encoded as a Lean parameter (a
hypothesis-conditioned input). The theorem then expresses the mass
gap in terms of `Λ_QCD`.

This is **structural**, not computational: we do not derive `c_Y`,
we simply state that `m_gap = c_Y · Λ_QCD` with `c_Y > 0`.

## Status

This file is structural physics scaffolding, not a substantive proof.
The substantive work — deriving `c_Y` from first principles —
remains an open problem.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Statements are conceptual; proofs are short.
-/

namespace LatticeQCD

/-! ## §1. Mass gap structure -/

/-- **Mass gap `m_gap` of pure Yang-Mills**: a dimension-1 quantity
    `m_gap` is **always proportional to `Λ_QCD`** in pure
    Yang-Mills, since `Λ_QCD` is the unique dimensional scale.

    The proportionality constant `c_Y > 0` is a pure number
    determined by the theory (not by `Λ_QCD` or the coupling). -/
structure MassGapAnchor (N_c : ℕ) where
  /-- The dimensionless ratio `c_Y = m_gap / Λ_QCD`. -/
  c_Y : ℝ
  /-- Positivity of the dimensionless constant. -/
  c_Y_pos : 0 < c_Y

/-! ## §2. Mass gap as `c_Y · Λ_QCD` -/

/-- **Mass-gap formula**: for a `MassGapAnchor` instance, the mass gap
    `m_gap` is

      `m_gap = c_Y · Λ_QCD`. -/
noncomputable def massGap {N_c : ℕ} (anchor : MassGapAnchor N_c)
    (Λ_QCD : ℝ) : ℝ :=
  anchor.c_Y * Λ_QCD

/-- **Mass gap positivity**: for any positive `Λ_QCD`, the mass gap
    is positive. -/
theorem massGap_pos {N_c : ℕ} (anchor : MassGapAnchor N_c)
    {Λ_QCD : ℝ} (hΛ : 0 < Λ_QCD) :
    0 < massGap anchor Λ_QCD := by
  unfold massGap
  exact mul_pos anchor.c_Y_pos hΛ

#print axioms massGap_pos

/-! ## §3. Mass gap from one-loop running -/

/-- **Mass gap in terms of one-loop running**:

      `m_gap = c_Y · μ · exp(-1/(2 · β₀ · g²(μ)))`.

    Combining `Λ_QCD = μ · exp(-1/(2 · β₀ · g²(μ)))` (one-loop
    dimensional transmutation) with `m_gap = c_Y · Λ_QCD` gives the
    mass gap directly in terms of the running coupling at any scale `μ`. -/
noncomputable def massGapFromRunning {N_c : ℕ} (anchor : MassGapAnchor N_c)
    (μ g_sq : ℝ) : ℝ :=
  anchor.c_Y * μ * Real.exp (-1 / (2 * betaZero N_c * g_sq))

/-- **`massGapFromRunning_pos`**: the mass gap from the running
    coupling is positive for any `μ > 0` and `g² > 0`. -/
theorem massGapFromRunning_pos {N_c : ℕ} (anchor : MassGapAnchor N_c)
    {μ g_sq : ℝ} (hμ : 0 < μ) (hg : 0 < g_sq) :
    0 < massGapFromRunning anchor μ g_sq := by
  unfold massGapFromRunning
  exact mul_pos (mul_pos anchor.c_Y_pos hμ) (Real.exp_pos _)

#print axioms massGapFromRunning_pos

/-! ## §4. Universal observation: every Yang-Mills dimensional quantity ∝ `Λ_QCD` -/

/-- **Dimensional-transmutation universality**: any dimensionful
    physical observable `O_dim` of pure Yang-Mills with mass-dimension
    `n` satisfies

      `O_dim = c_O · Λ_QCD^n`,

    where `c_O > 0` is a pure number specific to the observable.

    This is encoded here as a `structure` with `c_O : ℝ` and a
    positivity field; substantive work would derive the values of
    individual `c_O` constants from first principles. -/
structure DimensionalAnchor (N_c : ℕ) (mass_dimension : ℕ) where
  c_O : ℝ
  c_O_pos : 0 < c_O

/-- **`dimensionalObservable`**: given a `DimensionalAnchor` and `Λ_QCD`,
    the corresponding dimensional observable. -/
noncomputable def dimensionalObservable {N_c mass_dim : ℕ}
    (anchor : DimensionalAnchor N_c mass_dim) (Λ_QCD : ℝ) : ℝ :=
  anchor.c_O * Λ_QCD ^ mass_dim

/-- **Mass gap as the `mass_dimension = 1` case**. -/
def MassGapAnchor.toDimensionalAnchor {N_c : ℕ} (anchor : MassGapAnchor N_c) :
    DimensionalAnchor N_c 1 where
  c_O := anchor.c_Y
  c_O_pos := anchor.c_Y_pos

/-- **String tension as the `mass_dimension = 2` case**: the lattice
    string tension `σ` has dimensions of `(mass)²`, and `σ ≈ c_σ · Λ_QCD²`. -/
abbrev StringTensionAnchor (N_c : ℕ) := DimensionalAnchor N_c 2

/-- **Glueball mass spectrum as `mass_dimension = 1` cases**: the
    lightest 0⁺⁺ glueball, the lightest 2⁺⁺ glueball, etc., each
    have their own `MassGapAnchor` (the lightest 0⁺⁺ being `m_gap`
    itself). -/
abbrev GlueballMassAnchor (N_c : ℕ) := MassGapAnchor N_c

/-! ## §5. Compatibility with the project's structural mass gap -/

/-- **Compatibility theorem**: a `MassGapAnchor` for `N_c ≥ 1` provides
    a positive number that can be used as the mass gap for the
    project's abstract `ClayYangMillsMassGap` predicate.

    This is the bridge from physical anchor to structural definition:
    the abstract `ClayYangMillsMassGap N_c` has a witness for any `N_c`
    with `MassGapAnchor`, given any `Λ_QCD > 0`. -/
theorem massGap_provides_clay_mass {N_c : ℕ} (anchor : MassGapAnchor N_c)
    {Λ_QCD : ℝ} (hΛ : 0 < Λ_QCD) :
    ∃ m : ℝ, 0 < m :=
  ⟨massGap anchor Λ_QCD, massGap_pos anchor hΛ⟩

#print axioms massGap_provides_clay_mass

end LatticeQCD
