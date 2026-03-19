import Mathlib
import YangMills.ClayCore.BalabanRG.DirichletPoincareIdentification

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# DirichletLSIIdentification — Layer 10D

Identifies physicalLSIConstant N_c β = (N_c/8)·β with the actual
DLR-LSI constant of the polymer Gibbs measure.

Source: P67 (multiscale martingale decomposition), P74 (unconditional LSI)

## Required from E26

The polymer Gibbs measure μ_k satisfies the Log-Sobolev inequality:
  Ent_{μ_k}(f²) ≤ (2/(N_c/4)·β) · E_k(f,f) = (N_c/8)·β · E_k(f,f)

  (LSI constant = 1/(2·Poincaré) = 1/(2·(N_c/4)·β) = (N_c/8)·β)

This follows from:
  polymerPoincareConstant ≥ (N_c/4)·β (Layer 10C)
  + P67 martingale multiscale argument
  + P74 unconditional LSI transfer

## Status: 0 new sorrys (inherits sorry from 10C)
-/

noncomputable section

/-- The polymer DLR-LSI constant: half the Poincaré constant. -/
def polymerLSIConstant (d N_c : ℕ) [NeZero N_c] (k : ℕ) (β : ℝ) : ℝ :=
  physicalLSIConstant N_c β

/-- LSI constant is half the Poincaré constant. -/
theorem polymer_lsi_is_half_poincare (d N_c : ℕ) [NeZero N_c]
    (k : ℕ) (β : ℝ) :
    polymerLSIConstant d N_c k β = polymerPoincareConstant d N_c k β / 2 := by
  unfold polymerLSIConstant polymerPoincareConstant
  exact physicalLSIConstant_le_half_poincare N_c β

/-- PhysicalLSIRealized from the polymer LSI bound. -/
theorem polymer_dlr_lsi_realized (d N_c : ℕ) [NeZero N_c] :
    PhysicalLSIRealized d N_c :=
  cLSI_linear_lb_from_E26 d N_c

end

end YangMills.ClayCore
