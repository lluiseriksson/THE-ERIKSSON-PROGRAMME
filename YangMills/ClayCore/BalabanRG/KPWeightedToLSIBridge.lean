import Mathlib
import YangMills.ClayCore.BalabanRG.KPWeightedBudgetToFreeEnergy

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPWeightedToLSIBridge — Layer 5W (weighted bridge)

Weighted-budget analogue of `KPToLSIBridge`.

Purpose:
* package the new weighted KP → free-energy theorems behind a compact interface,
* expose positivity of `Z`,
* expose one-sided and two-sided `log Z` bounds,
* provide a `log 2` threshold variant mirroring the native Clay-core bridge,
* specialize automatically to the exponential polymer-size weight.

This does **not** claim the full LSI argument is closed here.
It only raises the weighted finite-volume KP lane to the same
"ready for LSI / Dirichlet packaging" abstraction level.
-/

noncomputable section

/-- Weighted-budget analogue of the native free-energy interface:
positivity of the partition function together with an upper bound on `log Z`. -/
def WeightedFreeEnergyReadyAtScale
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ) : Prop :=
  0 < polymerPartitionFunction Gamma K ∧
    Real.log (polymerPartitionFunction Gamma K) ≤ B

/-- Two-sided weighted free-energy control, useful for LSI / Dirichlet readouts. -/
def WeightedFreeEnergyTwoSidedAtScale
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ) : Prop :=
  |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B

/-- A weighted induction-budget bound with `B < 1` forces positivity of `Z`. -/
theorem kpWeightedBudget_partition_function_pos
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_pos_of_kpWeightedBudget
    Gamma K w B hge hB hsmall

/-- A weighted induction-budget bound with `B < 1` yields the one-sided
free-energy control `log Z ≤ B`. -/
theorem kpWeightedBudget_log_free_energy_upper
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hsmall : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact log_polymerPartitionFunction_le_of_kpWeightedBudget
    Gamma K w B hge hB hsmall

/-- A weighted induction-budget bound with `B ≤ 1/2` yields the two-sided
bound `|log Z| ≤ 2B`. -/
theorem kpWeightedBudget_log_free_energy_bound
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hhalf : B ≤ 1 / 2) :
    WeightedFreeEnergyTwoSidedAtScale Gamma K w B := by
  dsimp [WeightedFreeEnergyTwoSidedAtScale]
  exact log_polymerPartitionFunction_abs_le_two_mul_of_kpWeightedBudget
    Gamma K w B hge hB hhalf

/-- Summary theorem: the weighted KP lane is already ready for the
LSI / Dirichlet packaging step once a weighted budget is available. -/
theorem weighted_clayCore_free_energy_ready
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hsmall : B < 1) :
    WeightedFreeEnergyReadyAtScale Gamma K w B := by
  dsimp [WeightedFreeEnergyReadyAtScale]
  exact weightedFreeEnergyReady_of_kpWeightedBudget
    Gamma K w B hge hB hsmall

/-- `log 2` threshold variant mirroring the native KP bridge:
if the weighted budget is bounded by `exp t - 1` with `t < log 2`,
then the Gibbs state is well-defined and `log Z ≤ exp t - 1`. -/
theorem weighted_clayCore_free_energy_ready_of_lt_log2
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (t : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ Real.exp t - 1)
    (ht : t < Real.log 2) :
    WeightedFreeEnergyReadyAtScale Gamma K w (Real.exp t - 1) := by
  have hsmall : Real.exp t - 1 < 1 := by
    have hlt2 : Real.exp t < 2 := by
      simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
        (Real.exp_lt_exp.mpr ht)
    linarith
  exact weighted_clayCore_free_energy_ready
    Gamma K w (Real.exp t - 1) hge hB hsmall

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Exponential size-weight budget implies positivity of `Z` when `B < 1`. -/
theorem kpWeightedBudget_partition_function_pos_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_pos_of_kpWeightedBudget_expSizeWeight
    Gamma K a B ha hB hsmall

/-- Exponential size-weight budget implies `log Z ≤ B` when `B < 1`. -/
theorem kpWeightedBudget_log_free_energy_upper_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hsmall : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact log_polymerPartitionFunction_le_of_kpWeightedBudget_expSizeWeight
    Gamma K a B ha hB hsmall

/-- Exponential size-weight budget implies `|log Z| ≤ 2B`
when `B ≤ 1/2`. -/
theorem kpWeightedBudget_log_free_energy_bound_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hhalf : B ≤ 1 / 2) :
    WeightedFreeEnergyTwoSidedAtScale Gamma K (kpExpSizeWeight a d L) B := by
  dsimp [WeightedFreeEnergyTwoSidedAtScale]
  exact log_polymerPartitionFunction_abs_le_two_mul_of_kpWeightedBudget_expSizeWeight
    Gamma K a B ha hB hhalf

/-- Exponential size-weight budget yields the weighted free-energy-ready interface. -/
theorem weighted_clayCore_free_energy_ready_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hsmall : B < 1) :
    WeightedFreeEnergyReadyAtScale Gamma K (kpExpSizeWeight a d L) B := by
  dsimp [WeightedFreeEnergyReadyAtScale]
  exact weightedFreeEnergyReady_of_kpWeightedBudget_expSizeWeight
    Gamma K a B ha hB hsmall

/-- `log 2` threshold variant for the exponential polymer-size route. -/
theorem weighted_clayCore_free_energy_ready_expSizeWeight_of_lt_log2
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (t : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L)
      ≤ Real.exp t - 1)
    (ht : t < Real.log 2) :
    WeightedFreeEnergyReadyAtScale Gamma K (kpExpSizeWeight a d L) (Real.exp t - 1) := by
  have hsmall : Real.exp t - 1 < 1 := by
    have hlt2 : Real.exp t < 2 := by
      simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
        (Real.exp_lt_exp.mpr ht)
    linarith
  exact weighted_clayCore_free_energy_ready_expSizeWeight
    Gamma K a (Real.exp t - 1) ha hB hsmall

end

end YangMills.ClayCore
