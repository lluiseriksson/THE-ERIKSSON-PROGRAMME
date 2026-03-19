import Mathlib
import YangMills.ClayCore.BalabanRG.PhysicalRGRates

namespace YangMills.ClayCore

/-!
# BalabanRGAxiomReduction — Layer 6C (v4)

The remaining axiom is now `physical_rg_rates_from_E26` in `PhysicalRGRates.lean`.
This is a more precise statement than the previous abstract `BalabanRGPackage` axiom.

## Chain

physical_rg_rates_from_E26 (axiom — 4 quantitative targets)
  → physicalRGRates_to_balabanRGPackage     (THEOREM ✅)
  → uniform_lsi_of_balaban_rg_package       (THEOREM ✅)
  → ClayCoreLSI
  → LSItoSpectralGap                         (P8 ✅)
  → ClayYangMillsTheorem                    (ErikssonBridge ✅)

## 4 quantitative discharge targets (from E26)

  rho_exp_contractive:   rho(β) ≤ C·exp(-c·β)  (P81, P82)
  rho_in_unit_interval:  rho(β) ∈ (0,1)         (P81)
  cP_linear_lb:          cP(β) ≥ c·β            (P69, P70)
  cLSI_linear_lb:        cLSI(β) ≥ c·β          (P67, P74)
-/

/-- Recover uniform LSI from the quantitative E26 axiom. -/
theorem uniform_lsi_from_E26 (d N_c : ℕ) [NeZero N_c] :
    ∃ c > 0, ClayCoreLSI d N_c c :=
  uniform_lsi_from_physicalRates d N_c

/-- Recover BalabanRGPackage from the quantitative E26 axiom. -/
theorem balaban_rg_package_from_E26_theorem (d N_c : ℕ) [NeZero N_c] :
    BalabanRGPackage d N_c :=
  balabanRGPackage_from_physicalRates d N_c


/-! ## Zero-axiom route (Layer 8E)

The following theorems use physical witnesses without any axiom:
-/

/-- BalabanRGPackage from physical witnesses. 0 axioms. -/
theorem balaban_rg_package_from_physical_witnesses (d N_c : ℕ) [NeZero N_c] :
    BalabanRGPackage d N_c :=
  physicalBalabanRGPackage d N_c

/-- Uniform LSI from physical witnesses. 0 axioms, 0 sorrys. -/
theorem uniform_lsi_without_axioms (d N_c : ℕ) [NeZero N_c] :
    ∃ c > 0, ClayCoreLSI d N_c c :=
  physical_uniform_lsi d N_c

end YangMills.ClayCore
