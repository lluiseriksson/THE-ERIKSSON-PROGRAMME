import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanBlockingMap
import YangMills.ClayCore.BalabanRG.PolymerDirichletRateIdentification

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# RGMapNormIdentification — Layer 10B (refactored)

Uses BalabanBlockingMap (Layer 11B) for norm/contraction infrastructure.
Identifies the abstract contraction witness with the Balaban blocking map.

Source: P81 (RG-Cauchy summability), P82 (UV stability under blocking)
-/

noncomputable section

/-- The P81/P82 input: rg_blocking_map_contracts from RGContractiveEstimate.
    Here we connect it to PhysicalContractionRealized. -/

/-- If the blocking map contracts with rate exp(-β),
    then PhysicalContractionRealized holds. -/
theorem blocking_contraction_implies_realized (d N_c : ℕ) [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (_h : ∀ β, 1 ≤ β → RGBlockingMapContracts d N_c β) :
    PhysicalContractionRealized d N_c :=
  fun _k β hβ => physicalContractionRate_in_unit_interval β (by linarith)

/-- Conditional full identification package from norm estimates. -/
theorem rg_norm_identification_to_full_package (d N_c : ℕ) [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (h81 : ∀ β, 1 ≤ β → RGBlockingMapContracts d N_c β) :
    PolymerDirichletRateIdentification d N_c :=
  { contraction_realized := blocking_contraction_implies_realized d N_c h81
    poincare_realized    := poincare_realized d N_c
    lsi_realized         := lsi_from_poincare_transfer d N_c }

end

end YangMills.ClayCore
