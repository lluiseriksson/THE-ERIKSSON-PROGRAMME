import Mathlib
import YangMills.ClayCore.BalabanRG.PhysicalRGRatesWitness

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

/-- Short public frontier for the direct quantitative route:
it packages the existence of a direct `PhysicalRGRates` witness. -/
structure PhysicalRGRatesFrontier
    (d N_c : ℕ) [NeZero N_c] : Prop where
  ratesWitness : ∃ _ : PhysicalRGRates d N_c, True

/-- Canonical frontier from an explicit `PhysicalRGRates` witness. -/
theorem physical_rg_rates_frontier_of_rates
    (d N_c : ℕ) [NeZero N_c]
    (rates : PhysicalRGRates d N_c) :
    PhysicalRGRatesFrontier d N_c := by
  exact ⟨⟨rates, trivial⟩⟩

/-- Canonical frontier from the direct quantitative witness already assembled in the repo. -/
theorem physical_rg_rates_frontier_of_witness
    (d N_c : ℕ) [NeZero N_c] :
    PhysicalRGRatesFrontier d N_c := by
  exact physical_rg_rates_frontier_of_rates d N_c (physical_rg_rates_witness d N_c)

/-- Projection to the rates-witness surface. -/
theorem rates_witness_of_physical_rg_rates_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : PhysicalRGRatesFrontier d N_c) :
    ∃ _ : PhysicalRGRates d N_c, True := by
  exact frontier.ratesWitness

/-- Recover a package-side witness from the quantitative frontier. -/
theorem balaban_rg_package_of_physical_rg_rates_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : PhysicalRGRatesFrontier d N_c) :
    BalabanRGPackage d N_c := by
  rcases frontier.ratesWitness with ⟨rates, _⟩
  exact physicalRGRates_to_balabanRGPackage rates

/-- Recover uniform LSI from the quantitative frontier. -/
theorem uniform_lsi_of_physical_rg_rates_frontier
    {d N_c : ℕ} [NeZero N_c]
    (frontier : PhysicalRGRatesFrontier d N_c) :
    ∃ c > 0, ClayCoreLSI d N_c c := by
  rcases frontier.ratesWitness with ⟨rates, _⟩
  exact physicalRGRates_to_lsi rates

/-- Logical normal form: the quantitative frontier is equivalent to the bare rates-witness surface. -/
theorem physical_rg_rates_frontier_iff_rates_witness
    (d N_c : ℕ) [NeZero N_c] :
    PhysicalRGRatesFrontier d N_c ↔
      (∃ _ : PhysicalRGRates d N_c, True) := by
  constructor
  · intro frontier
    exact frontier.ratesWitness
  · intro h
    exact ⟨h⟩

/-- Canonical coherence: the frontier is propositionally equal to the canonical one reconstructed
from its rates witness. -/
theorem physical_rg_rates_frontier_eq_canonical_of_rates_witness
    {d N_c : ℕ} [NeZero N_c]
    (frontier : PhysicalRGRatesFrontier d N_c) :
    frontier =
      physical_rg_rates_frontier_of_rates d N_c
        (Classical.choose frontier.ratesWitness) := by
  apply Subsingleton.elim

/-- Canonical coherence: the package-side output agrees propositionally with the one reconstructed
from the chosen rates witness. -/
theorem balaban_rg_package_of_physical_rg_rates_frontier_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (frontier : PhysicalRGRatesFrontier d N_c) :
    balaban_rg_package_of_physical_rg_rates_frontier frontier =
      physicalRGRates_to_balabanRGPackage
        (Classical.choose frontier.ratesWitness) := by
  rfl

/-- Canonical coherence: the uniform-LSI output agrees propositionally with the one reconstructed
from the chosen rates witness. -/
theorem uniform_lsi_of_physical_rg_rates_frontier_eq_canonical
    {d N_c : ℕ} [NeZero N_c]
    (frontier : PhysicalRGRatesFrontier d N_c) :
    uniform_lsi_of_physical_rg_rates_frontier frontier =
      physicalRGRates_to_lsi
        (Classical.choose frontier.ratesWitness) := by
  rfl

/-- The direct quantitative witness gives the preferred quantitative frontier. -/
theorem physical_rg_rates_frontier_eq_canonical_of_witness
    (d N_c : ℕ) [NeZero N_c] :
    physical_rg_rates_frontier_of_witness d N_c =
      physical_rg_rates_frontier_of_rates d N_c
        (physical_rg_rates_witness d N_c) := by
  rfl

end

end YangMills.ClayCore
