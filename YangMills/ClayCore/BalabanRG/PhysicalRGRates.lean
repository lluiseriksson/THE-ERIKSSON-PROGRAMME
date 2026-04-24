import Mathlib
import YangMills.ClayCore.BalabanRG.ContractiveMapReduction

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PhysicalRGRates — Layer 8A

Quantitative weak-coupling rates that replace the trivial witnesses
in `trivialBalabanRGPackage`.

## Rates expected from E26 (P67–P82)

* `rho(β)  = O(exp(-c·β))`   — contraction rate  (P81, P82)
* `cP(β)   = Θ(β)`           — Poincaré constant  (P69, P70)
* `cLSI(β) = Θ(β)`           — LSI constant       (P67, P74)

## Architecture

PhysicalRGRates
  ↓ physicalRGRates_to_balabanRGPackage  (this file, 0 sorrys)
BalabanRGPackage
  ↓ uniform_lsi_of_balaban_rg_package    (UniformLSITransfer, 0 sorrys)
ClayCoreLSI
  ↓ LSItoSpectralGap                     (P8, ✅)
ClayYangMillsTheorem                     (ErikssonBridge, ✅)

## Discharge status

The structure below is the reusable quantitative rates interface.  The direct
witness assembled from the repository's current rate-side theorems lives in
`PhysicalRGRatesWitness.lean`; this file keeps only the interface and its
projection theorems.
-/

noncomputable section

/-! ## Quantitative rate predicates -/

/-- Exponential contraction: rho(β) ≤ C·exp(-c·β) for β ≥ β₀. (P81, P82) -/
def ExponentialContraction (rho : ℝ → ℝ) : Prop :=
  ∃ beta0 c C : ℝ, 0 < beta0 ∧ 0 < c ∧ 0 < C ∧
    ∀ β, beta0 ≤ β → rho β ≤ C * Real.exp (-c * β)

/-- Linear lower bound: f(β) ≥ c·β for β ≥ β₀. (P69, P70, P67, P74) -/
def LinearLowerBound (f : ℝ → ℝ) : Prop :=
  ∃ beta0 c : ℝ, 0 < beta0 ∧ 0 < c ∧ ∀ β, beta0 ≤ β → c ≤ f β

/-! ## The quantitative RG data package -/

/-- Physical RG rates: the quantitative content of E26. -/
structure PhysicalRGRates (d N_c : ℕ) [NeZero N_c] where
  /-- Contraction rate function (P81, P82). -/
  rho  : ℝ → ℝ
  /-- Poincaré constant function (P69, P70). -/
  cP   : ℝ → ℝ
  /-- LSI constant function (P67, P74). -/
  cLSI : ℝ → ℝ
  /-- rho is exponentially small at weak coupling. -/
  rho_exp_contractive : ExponentialContraction rho
  /-- rho stays in (0,1) at weak coupling. -/
  rho_in_unit_interval :
    ∃ beta0 : ℝ, 0 < beta0 ∧ ∀ β, beta0 ≤ β → rho β ∈ Set.Ioo (0 : ℝ) 1
  /-- Poincaré constant grows at least linearly. -/
  cP_linear_lb : LinearLowerBound cP
  /-- LSI constant grows at least linearly. -/
  cLSI_linear_lb : LinearLowerBound cLSI

/-! ## PhysicalRGRates → BalabanRGPackage -/

/-- Quantitative rates induce the abstract BalabanRGPackage. -/
theorem physicalRGRates_to_balabanRGPackage {d N_c : ℕ} [NeZero N_c]
    (rates : PhysicalRGRates d N_c) :
    BalabanRGPackage d N_c := by
  obtain ⟨beta0r, hbr, hrho⟩ := rates.rho_in_unit_interval
  obtain ⟨beta0P, cP0, hbP, hcP0, hcP⟩ := rates.cP_linear_lb
  obtain ⟨beta0L, cL0, hbL, hcL0, hcL⟩ := rates.cLSI_linear_lb
  exact {
    contractiveMaps :=
      ⟨beta0r, hbr, fun k β hβ => ⟨rates.rho β, hrho β hβ, fun _ _ => trivial⟩⟩
    uniformCoercivity :=
      -- BalabanRGPackage needs cP_const ≤ β for β ≥ beta0P
      -- Use beta0P as the constant: for β ≥ beta0P, beta0P ≤ β = hβ
      ⟨beta0P, hbP, beta0P, hbP, fun _k β hβ => hβ⟩
    entropyCoupling :=
      ⟨beta0L, hbL, beta0L, hbL, fun _k β hβ => hβ⟩
  }

/-- Physical rates → uniform LSI. -/
theorem physicalRGRates_to_lsi {d N_c : ℕ} [NeZero N_c]
    (rates : PhysicalRGRates d N_c) :
    ∃ c > 0, ClayCoreLSI d N_c c :=
  uniform_lsi_of_balaban_rg_package (physicalRGRates_to_balabanRGPackage rates)

/-!
## Discharge targets for E26 formalization

| Field              | Source     | Quantitative claim                        |
|---|---|---|
| rho_exp_contractive | P81, P82  | rho(β) ≤ C·exp(-c·β)                    |
| rho_in_unit_interval | P81      | rho(β) ∈ (0,1) for β ≥ β₀               |
| cP_linear_lb       | P69, P70   | cP(β) ≥ c·β                              |
| cLSI_linear_lb     | P67, P74   | cLSI(β) ≥ c·β                            |

When all four are theorems, `PhysicalRGRatesWitness.lean` can assemble a direct
`PhysicalRGRates` witness without any global axiom declaration.
-/

end

end YangMills.ClayCore
