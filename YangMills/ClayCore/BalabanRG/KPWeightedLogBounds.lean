import Mathlib
import YangMills.ClayCore.BalabanRG.KPWeightedBudgetToPartition
import YangMills.ClayCore.BalabanRG.PolymerLogLowerBound

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPWeightedLogBounds — (v1.0.18-alpha)

Weighted free-energy consequences of the repaired KP weighted budget layer.

Starting from a weighted compatible-family majorant or induction budget, and the
explicit hypothesis `1 ≤ w(X)`, we recover:

* `|Z - 1| ≤ B`,
* `0 < Z` when `B < 1`,
* `log Z ≤ B`,
* `|log Z| ≤ 2B` when `B ≤ 1/2`.

Automatic specializations to the exponential polymer-size weight are included.
-/

noncomputable section

/-- Weighted majorant with `B < 1` implies positivity of the partition
function. -/
theorem polymerPartitionFunction_pos_of_kpWeightedMajorant_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B)
    (hBlt : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  have habs :
      |polymerPartitionFunction Gamma K - 1| ≤ B :=
    abs_Z_sub_one_le_of_kpWeightedMajorant Gamma K w B hge hB
  have hlt : |polymerPartitionFunction Gamma K - 1| < 1 :=
    lt_of_le_of_lt habs hBlt
  have hband := abs_lt.mp hlt
  linarith [hband.1]

/-- Weighted budget bound with `B < 1` implies positivity of the partition
function. -/
theorem polymerPartitionFunction_pos_of_kpWeightedBudget_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hBlt : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_pos_of_kpWeightedMajorant_lt_one
    Gamma K w B hge
    (by
      have hmajor :
          KPWeightedCompatibleFamilyMajorant Gamma K w
            (KPWeightedInductionBudget Gamma K w) :=
        kpWeightedInductionBudget_is_majorant Gamma K w
      exact le_trans hmajor hB)
    hBlt

/-- Weighted majorant with `B < 1` implies the upper free-energy bound
`log Z ≤ B`. -/
theorem log_polymerPartitionFunction_le_of_kpWeightedMajorant_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B)
    (hBlt : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  have hpos :
      0 < polymerPartitionFunction Gamma K :=
    polymerPartitionFunction_pos_of_kpWeightedMajorant_lt_one
      Gamma K w B hge hB hBlt
  have habs :
      |polymerPartitionFunction Gamma K - 1| ≤ B :=
    abs_Z_sub_one_le_of_kpWeightedMajorant Gamma K w B hge hB
  calc
    Real.log (polymerPartitionFunction Gamma K)
        ≤ polymerPartitionFunction Gamma K - 1 :=
      log_le_sub_one_of_pos _ hpos
    _ ≤ |polymerPartitionFunction Gamma K - 1| :=
      le_abs_self _
    _ ≤ B := habs

/-- Weighted budget bound with `B < 1` implies the upper free-energy bound
`log Z ≤ B`. -/
theorem log_polymerPartitionFunction_le_of_kpWeightedBudget_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hBlt : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact log_polymerPartitionFunction_le_of_kpWeightedMajorant_lt_one
    Gamma K w B hge
    (by
      have hmajor :
          KPWeightedCompatibleFamilyMajorant Gamma K w
            (KPWeightedInductionBudget Gamma K w) :=
        kpWeightedInductionBudget_is_majorant Gamma K w
      exact le_trans hmajor hB)
    hBlt

/-- Weighted majorant with `B ≤ 1/2` implies the two-sided free-energy bound
`|log Z| ≤ 2B`. -/
theorem log_polymerPartitionFunction_abs_le_of_kpWeightedMajorant_half
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B)
    (hBhalf : B ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B := by
  have habs :
      |polymerPartitionFunction Gamma K - 1| ≤ B :=
    abs_Z_sub_one_le_of_kpWeightedMajorant Gamma K w B hge hB
  have hB0 : 0 ≤ B := by
    exact le_trans (abs_nonneg (polymerPartitionFunction Gamma K - 1)) habs
  have hBlt : B < 1 := by
    linarith
  have hpos :
      0 < polymerPartitionFunction Gamma K :=
    polymerPartitionFunction_pos_of_kpWeightedMajorant_lt_one
      Gamma K w B hge hB hBlt
  have hub :
      Real.log (polymerPartitionFunction Gamma K) ≤ B :=
    log_polymerPartitionFunction_le_of_kpWeightedMajorant_lt_one
      Gamma K w B hge hB hBlt
  have hband := abs_le.mp habs
  have hZlb : 1 - B ≤ polymerPartitionFunction Gamma K := by
    linarith
  have h1mB_pos : 0 < 1 - B := by
    linarith
  have hlog_mono :
      Real.log (1 - B) ≤ Real.log (polymerPartitionFunction Gamma K) :=
    Real.log_le_log h1mB_pos hZlb
  have hlog_lb :
      -2 * B ≤ Real.log (1 - B) :=
    Real.log_one_sub_ge_neg_two hB0 hBhalf
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Weighted budget bound with `B ≤ 1/2` implies the two-sided free-energy
bound `|log Z| ≤ 2B`. -/
theorem log_polymerPartitionFunction_abs_le_of_kpWeightedBudget_half
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hBhalf : B ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B := by
  exact log_polymerPartitionFunction_abs_le_of_kpWeightedMajorant_half
    Gamma K w B hge
    (by
      have hmajor :
          KPWeightedCompatibleFamilyMajorant Gamma K w
            (KPWeightedInductionBudget Gamma K w) :=
        kpWeightedInductionBudget_is_majorant Gamma K w
      exact le_trans hmajor hB)
    hBhalf

/-- Summary package: weighted majorant gives positivity of `Z` and upper
free-energy control. -/
theorem weighted_free_energy_ready_of_kpWeightedMajorant_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B)
    (hBlt : B < 1) :
    0 < polymerPartitionFunction Gamma K ∧
      Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  constructor
  · exact polymerPartitionFunction_pos_of_kpWeightedMajorant_lt_one
      Gamma K w B hge hB hBlt
  · exact log_polymerPartitionFunction_le_of_kpWeightedMajorant_lt_one
      Gamma K w B hge hB hBlt

/-- Summary package: weighted budget gives positivity of `Z` and upper
free-energy control. -/
theorem weighted_free_energy_ready_of_kpWeightedBudget_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hBlt : B < 1) :
    0 < polymerPartitionFunction Gamma K ∧
      Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  constructor
  · exact polymerPartitionFunction_pos_of_kpWeightedBudget_lt_one
      Gamma K w B hge hB hBlt
  · exact log_polymerPartitionFunction_le_of_kpWeightedBudget_lt_one
      Gamma K w B hge hB hBlt

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Exponential polymer-size weighted majorant with `B < 1` implies positivity
of the partition function. -/
theorem polymerPartitionFunction_pos_of_kpWeightedMajorant_expSizeWeight_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B)
    (hBlt : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_pos_of_kpWeightedMajorant_lt_one
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hBlt

/-- Exponential polymer-size weighted budget with `B < 1` implies positivity of
the partition function. -/
theorem polymerPartitionFunction_pos_of_kpWeightedBudget_expSizeWeight_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hBlt : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_pos_of_kpWeightedBudget_lt_one
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hBlt

/-- Exponential polymer-size weighted majorant with `B < 1` implies
`log Z ≤ B`. -/
theorem log_polymerPartitionFunction_le_of_kpWeightedMajorant_expSizeWeight_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B)
    (hBlt : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact log_polymerPartitionFunction_le_of_kpWeightedMajorant_lt_one
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hBlt

/-- Exponential polymer-size weighted budget with `B < 1` implies `log Z ≤ B`.
-/
theorem log_polymerPartitionFunction_le_of_kpWeightedBudget_expSizeWeight_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hBlt : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact log_polymerPartitionFunction_le_of_kpWeightedBudget_lt_one
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hBlt

/-- Exponential polymer-size weighted majorant with `B ≤ 1/2` implies
`|log Z| ≤ 2B`. -/
theorem log_polymerPartitionFunction_abs_le_of_kpWeightedMajorant_expSizeWeight_half
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B)
    (hBhalf : B ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B := by
  exact log_polymerPartitionFunction_abs_le_of_kpWeightedMajorant_half
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hBhalf

/-- Exponential polymer-size weighted budget with `B ≤ 1/2` implies
`|log Z| ≤ 2B`. -/
theorem log_polymerPartitionFunction_abs_le_of_kpWeightedBudget_expSizeWeight_half
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hBhalf : B ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B := by
  exact log_polymerPartitionFunction_abs_le_of_kpWeightedBudget_half
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hBhalf

/-- Exponential polymer-size weighted budget gives the free-energy-ready pair
used downstream by the RG/LSI interface. -/
theorem weighted_free_energy_ready_of_kpWeightedBudget_expSizeWeight_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hBlt : B < 1) :
    0 < polymerPartitionFunction Gamma K ∧
      Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  constructor
  · exact polymerPartitionFunction_pos_of_kpWeightedBudget_expSizeWeight_lt_one
      Gamma K a B ha hB hBlt
  · exact log_polymerPartitionFunction_le_of_kpWeightedBudget_expSizeWeight_lt_one
      Gamma K a B ha hB hBlt

end

end YangMills.ClayCore
