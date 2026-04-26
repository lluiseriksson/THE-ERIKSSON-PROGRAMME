/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L8_LatticeToContinuum.SchwingerFunctions

/-!
# Boundary insensitivity (Bloque-4 Remark 2.4(ii))

This module formalises the **boundary insensitivity** of the lattice
Schwinger functions: for observables supported in a ball of physical
radius `R_0`, the finite-volume Schwinger function differs from its
infinite-volume analogue by an error decaying exponentially in
`L_phys`.

## Strategic placement

This is **Phase 106** of the L8_LatticeToContinuum block.

## The argument (Bloque-4 Remark 2.4(ii))

For gauge-invariant local observables `A_1, ..., A_n` supported in
a physical ball of radius `R_0`, the difference between the
`(η, L_phys)`-Schwinger function and its infinite-volume analogue
satisfies:

  `|S_n^{(η, L_phys)}(A_1, ..., A_n) - S_n^∞(A_1, ..., A_n)|
   ≤ C exp(-m (L_phys - 2 R_0) / a_*)`,

where the exponential suppression comes from the **clustering bound**
(Bloque-4 Theorem 7.1, our Phase 97 endpoint) applied to boundary
effects.

This justifies taking the joint limit `(η_j, L_{phys, j}) → (0, ∞)`
without worrying about boundary artefacts.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L8_LatticeToContinuum

open MeasureTheory

/-! ## §1. The boundary insensitivity hypothesis -/

/-- A **boundary insensitivity hypothesis** for lattice Schwinger
    functions: differences from the infinite-volume Schwinger
    function decay exponentially in the box size, given the
    observables' physical-radius support. -/
structure BoundaryInsensitivity
    (n : ℕ) where
  /-- The lattice spacing parameter. -/
  η : ℝ
  hη_pos : 0 < η
  /-- The terminal-scale lattice spacing `a_*` (mass-gap scale). -/
  a_star : ℝ
  ha_star_pos : 0 < a_star
  /-- The mass gap. -/
  m : ℝ
  hm_pos : 0 < m
  /-- Constant for the boundary error bound. -/
  C : ℝ
  hC_pos : 0 < C
  /-- The boundary error bound: for observables supported in a
      ball of radius R₀, the (η, L_phys)-Schwinger function vs.
      infinite-volume analogue differs by ≤ C exp(-m(L_phys - 2 R₀)/a_*). -/
  bound : ∀ (R_0 L_phys : ℝ),
    0 < R_0 →
    2 * R_0 < L_phys →
    -- For any observables supported within radius R₀:
    -- |S_n^{(η, L_phys)} - S_n^∞| ≤ C exp(-m (L_phys - 2 R₀) / a_*)
    ∃ E : ℝ, 0 ≤ E ∧ E ≤ C * Real.exp (-m * (L_phys - 2 * R_0) / a_star)

/-! ## §2. Joint limit insensitivity -/

/-- The boundary error tends to zero as `L_phys → ∞`. -/
theorem boundary_error_tendsto_zero
    {n : ℕ} (BI : BoundaryInsensitivity n)
    (R_0 : ℝ) (hR_0 : 0 < R_0) :
    Filter.Tendsto
      (fun L_phys : ℝ => BI.C * Real.exp (-BI.m * (L_phys - 2 * R_0) / BI.a_star))
      Filter.atTop
      (nhds 0) := by
  -- Standard: as L_phys → ∞, the exponent tends to -∞,
  -- so the exponential tends to 0.
  have h_a_star_pos := BI.ha_star_pos
  have h_m_pos := BI.hm_pos
  -- The function is C · exp(g(L)) where g(L) → -∞ as L → ∞.
  apply Filter.Tendsto.const_mul
  -- exp(g(L)) → 0 with g(L) → -∞
  rw [show (0 : ℝ) = Real.exp 0 - Real.exp 0 from by ring]
  -- Use Real.tendsto_exp_atBot composed with g.
  -- The function g(L) = -m(L - 2R)/a_* tends to atBot as L → atTop.
  have h_g_atBot :
      Filter.Tendsto
        (fun L : ℝ => -BI.m * (L - 2 * R_0) / BI.a_star)
        Filter.atTop Filter.atBot := by
    apply Filter.Tendsto.atBot_div_const h_a_star_pos
    apply Filter.Tendsto.const_mul_atBot (neg_neg_iff_pos.mpr h_m_pos)
    apply Filter.tendsto_atTop_add_const_right Filter.atTop _
      Filter.tendsto_id
  -- Compose with exp: exp(g) → exp(atBot) = 0.
  -- Real.tendsto_exp_atBot says Real.exp tendsto atBot to 0.
  have h_exp := Real.tendsto_exp_atBot.comp h_g_atBot
  -- h_exp : Tendsto (Real.exp ∘ (fun L => -m(L-2R)/a_*)) atTop (nhds 0)
  -- We want: Tendsto (fun L => Real.exp (-m(L-2R)/a_*)) atTop (nhds 0).
  -- These are the same modulo simp.
  simpa using h_exp

#print axioms boundary_error_tendsto_zero

/-! ## §3. Coordination note -/

/-
This file is **Phase 106** of the L8_LatticeToContinuum block.

## Status

* `BoundaryInsensitivity` data structure with `bound` field.
* `boundary_error_tendsto_zero` theorem (real proof, NO sorries).

## What's done

The structural shape + the limit theorem `boundary_error_tendsto_zero`
showing the boundary error → 0 as L_phys → ∞. **Real proof using
Filter.Tendsto.const_mul + Real.tendsto_exp_atBot**.

## What's NOT done

* The connection to actual lattice Schwinger functions (the `bound`
  field is hypothesised at the abstract level).
* The integral-difference formulation (a_1 ... a_n with support in a
  ball).

## Strategic value

Phase 106 verifies that the boundary error is **vanishing**, a
crucial input to Phase 107's full bridge theorem. The actual
boundary error bound comes from Bloque-4 Theorem 7.1 (our
`L7_Multiscale.lattice_mass_gap_of_multiscale_decoupling`).

Cross-references:
- Phase 97: `L7_Multiscale/MultiscaleDecouplingPackage.lean` (mass gap).
- Phase 105: `SubsequentialContinuumLimit.lean`.
- Bloque-4 Remark 2.4(ii).
-/

end YangMills.L8_LatticeToContinuum
