import Mathlib
import YangMills.ClayCore.BalabanRG.RGContractionRate

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PhysicalBalabanRGPackage — Layer 8E

Physical witnesses (0 axioms, 0 sorrys):
  rho(β)  = exp(-β)       (Layer 8D)
  cP(β)   = (N_c/4)·β    (Layer 8B)
  cLSI(β) = (N_c/8)·β    (Layer 8C)
-/

noncomputable section

def physicalRGRatesWitness (d N_c : ℕ) [NeZero N_c] : PhysicalRGRates d N_c where
  rho  := physicalContractionRate
  cP   := physicalPoincareConstant N_c
  cLSI := physicalLSIConstant N_c
  rho_exp_contractive  := rho_exp_contractive_from_E26 d N_c
  rho_in_unit_interval := rho_in_unit_interval_from_E26 d N_c
  cP_linear_lb         := cP_linear_lb_from_E26 d N_c
  cLSI_linear_lb       := cLSI_linear_lb_from_E26 d N_c

def physicalBalabanRGPackage (d N_c : ℕ) [NeZero N_c] : BalabanRGPackage d N_c :=
  physicalRGRates_to_balabanRGPackage (physicalRGRatesWitness d N_c)

theorem physical_uniform_lsi (d N_c : ℕ) [NeZero N_c] :
    ∃ c > 0, ClayCoreLSI d N_c c :=
  uniform_lsi_of_balaban_rg_package (physicalBalabanRGPackage d N_c)

end

end YangMills.ClayCore
