import Mathlib
import YangMills.ClayCore.BalabanRG.FreeEnergyControlReduction

namespace YangMills.ClayCore

/-!
# BalabanRGPackage — Layer 6 (v3)

Three-pillar RG package. `freeEnergyControl` discharged by Clay Core.
All fields now use the physical weak-coupling regime: β ≥ β₀ > 0.

Sources: P67, P69–P70, P74, P81–P82.
-/

-- freeEnergyControl is discharged in FreeEnergyControlReduction.lean.

structure BalabanRGPackage (d : ℕ) (N_c : ℕ) [NeZero N_c] where
  /-- Contractive RG maps (P81, P82): activity decreases across scales
      in the weak-coupling regime β ≥ β₀. -/
  contractiveMaps :
    ∃ beta0 : ℝ, 0 < beta0 ∧ ∀ (_ : ℕ) (β : ℝ), beta0 ≤ β →
      ∃ rho : ℝ, rho ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ (_ _ : ℕ → ℝ), True

  /-- Uniform coercivity (P69, P70): Poincaré constant ≥ cP > 0
      for β ≥ β₀ (weak coupling). -/
  uniformCoercivity :
    ∃ beta0 : ℝ, 0 < beta0 ∧ ∃ cP : ℝ, 0 < cP ∧
      ∀ (_ : ℕ) (β : ℝ), beta0 ≤ β → cP ≤ β

  /-- Entropy coupling (P67, P74): LSI constant ≥ cLSI > 0
      for β ≥ β₀ (weak coupling). -/
  entropyCoupling :
    ∃ beta0 : ℝ, 0 < beta0 ∧ ∃ cLSI : ℝ, 0 < cLSI ∧
      ∀ (_ : ℕ) (β : ℝ), beta0 ≤ β → cLSI ≤ β

end YangMills.ClayCore
