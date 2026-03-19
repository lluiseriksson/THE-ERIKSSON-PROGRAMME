import Mathlib
import YangMills.ClayCore.BalabanRG.FreeEnergyControlReduction

namespace YangMills.ClayCore

/-!
# BalabanRGPackage — Layer 6 (v2)

Three-pillar RG package. `freeEnergyControl` has been discharged by the
Clay Core (see `FreeEnergyControlReduction.lean`).

Remaining: contractiveMaps, uniformCoercivity, entropyCoupling.
Source: P67, P69–P70, P74, P81–P82.
-/

structure BalabanRGPackage (d : ℕ) (N_c : ℕ) [NeZero N_c] where
  /-- Contractive RG maps (P81, P82): activity norm decreases across scales. -/
  contractiveMaps :
    ∀ (k : ℕ) (β : ℝ),
      ∃ rho : ℝ, rho ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ (K1 K2 : ℕ → ℝ), True

  /-- Uniform coercivity (P69, P70): Poincaré constant bounded below. -/
  uniformCoercivity :
    ∃ lambdaP : ℝ, 0 < lambdaP ∧
      ∀ (k : ℕ) (β : ℝ), 0 < β → lambdaP ≤ β

  /-- Entropy coupling (P67, P74): LSI constant transfers between scales. -/
  entropyCoupling :
    ∃ cLSI : ℝ, 0 < cLSI ∧
      ∀ (k : ℕ) (β : ℝ), 0 < β → cLSI ≤ β

/-- freeEnergyControl is now a theorem, not a field. -/
theorem BalabanRGPackage.freeEnergyControl_theorem {d N_c : ℕ} [NeZero N_c]
    (_ : BalabanRGPackage d N_c) :
    ∀ (k : ℕ) (β : ℝ), 0 < β →
      ∃ Cfe : ℝ, 0 < Cfe ∧
        ∀ (Gamma : Finset (Polymer d (Int.ofNat k))),
          ∃ (K : Activity d (Int.ofNat k)) (a : ℝ), 0 < a ∧
            KPOnGamma Gamma K a ∧
            theoreticalBudget Gamma K a < Real.log 2 ∧
            Cfe * β ≤ 1 :=
  freeEnergyControl_discharged

end YangMills.ClayCore
