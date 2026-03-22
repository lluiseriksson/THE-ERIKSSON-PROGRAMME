import Mathlib
import YangMills.ClayCore.BalabanRG.RGCauchyP81LiveTarget
import YangMills.ClayCore.BalabanRG.RGContractionRate

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

/-- Direct quantitative witness for the full `PhysicalRGRates` package,
assembled from the already-proved rate-side fields in the repository. -/
def physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] : PhysicalRGRates d N_c where
  rho := physicalContractionRate
  cP := physicalPoincareConstant N_c
  cLSI := physicalLSIConstant N_c
  rho_exp_contractive := rho_exp_contractive_from_E26 d N_c
  rho_in_unit_interval := rho_in_unit_interval_from_E26 d N_c
  cP_linear_lb := cP_linear_lb_from_E26 d N_c
  cLSI_linear_lb := cLSI_linear_lb_from_E26 d N_c

/-- The `rho` field of the direct witness is the physical contraction rate. -/
theorem rho_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    (physical_rg_rates_witness d N_c).rho = physicalContractionRate := by
  rfl

/-- The `cP` field of the direct witness is the physical Poincaré constant. -/
theorem cP_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    (physical_rg_rates_witness d N_c).cP = physicalPoincareConstant N_c := by
  rfl

/-- The `cLSI` field of the direct witness is the physical LSI constant. -/
theorem cLSI_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    (physical_rg_rates_witness d N_c).cLSI = physicalLSIConstant N_c := by
  rfl

/-- The `rho_exp_contractive` field of the direct witness is discharged canonically. -/
theorem rho_exp_contractive_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    ExponentialContraction (physical_rg_rates_witness d N_c).rho := by
  simpa [physical_rg_rates_witness] using rho_exp_contractive_from_E26 d N_c

/-- The `rho_in_unit_interval` field of the direct witness is discharged canonically. -/
theorem rho_in_unit_interval_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    ∃ beta0 : ℝ, 0 < beta0 ∧
      ∀ β, beta0 ≤ β → (physical_rg_rates_witness d N_c).rho β ∈ Set.Ioo (0 : ℝ) 1 := by
  simpa [physical_rg_rates_witness] using rho_in_unit_interval_from_E26 d N_c

/-- The `cP_linear_lb` field of the direct witness is discharged canonically. -/
theorem cP_linear_lb_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    LinearLowerBound (physical_rg_rates_witness d N_c).cP := by
  simpa [physical_rg_rates_witness] using cP_linear_lb_from_E26 d N_c

/-- The `cLSI_linear_lb` field of the direct witness is discharged canonically. -/
theorem cLSI_linear_lb_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    LinearLowerBound (physical_rg_rates_witness d N_c).cLSI := by
  simpa [physical_rg_rates_witness] using cLSI_linear_lb_from_E26 d N_c

/-- The direct quantitative witness yields a `BalabanRGPackage`
without using the legacy axiom entrypoint. -/
theorem balaban_rg_package_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    BalabanRGPackage d N_c := by
  exact physicalRGRates_to_balabanRGPackage (physical_rg_rates_witness d N_c)

/-- The direct quantitative witness yields uniform LSI
without using the legacy axiom entrypoint. -/
theorem uniform_lsi_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    ∃ c > 0, ClayCoreLSI d N_c c := by
  exact physicalRGRates_to_lsi (physical_rg_rates_witness d N_c)

/-- The theorem-side P81 live target remains the active theorem-side source
behind the current quantitative witness route. -/
theorem rg_cauchy_p81_live_target_of_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k] :
    RGCauchyP81LiveTarget d N_c := by
  exact rg_cauchy_p81_live_target_of_interface d N_c

/-- From an audit packet, the theorem-side live target yields the current P81 frontier
while the quantitative witness yields the package-side route. -/
theorem rg_cauchy_p81_frontier_of_audit_packet_and_physical_rg_rates_witness
    (d N_c : ℕ) [NeZero N_c] [∀ k, ActivityNorm d k]
    (audit : BalabanRGUniformLSIAuditPacket d N_c) :
    RGCauchyP81Frontier d N_c := by
  exact
    rg_cauchy_p81_frontier_of_audit_packet_and_live_target d N_c audit
      (rg_cauchy_p81_live_target_of_physical_rg_rates_witness d N_c)

end

end YangMills.ClayCore
