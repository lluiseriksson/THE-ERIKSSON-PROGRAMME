import Mathlib
import YangMills.ClayCore.BalabanRG.KPWeightedBudgetToPartition
import YangMills.ClayCore.BalabanRG.PolymerLogLowerBound

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPWeightedBudgetToFreeEnergy — Layer 4D

Push the repaired weighted KP budget bridge one layer higher:

* `|Z - 1| ≤ B`
* `0 < Z` when `B < 1`
* `log Z ≤ B`
* `|log Z| ≤ 2 B` when `B ≤ 1/2`

This is the weighted-budget / exp-size-weight counterpart of the native
`KPConsequences` + `PolymerLogBound` + `PolymerLogLowerBound` lane.

Conservative design:
* first isolate generic consequences of any bound `|Z - 1| ≤ B`,
* then specialize them to weighted majorants / weighted budgets,
* then add automatic exponential-size-weight corollaries.
-/

noncomputable section

/-! ## Generic consequences of an absolute partition-function bound -/

/-- Any bound `|Z - 1| ≤ B` yields the lower bound `1 - B ≤ Z`. -/
theorem polymerPartitionFunction_lb_of_abs_Z_sub_one_le
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (B : ℝ)
    (hB : |polymerPartitionFunction Gamma K - 1| ≤ B) :
    1 - B ≤ polymerPartitionFunction Gamma K := by
  have hneg : -B ≤ polymerPartitionFunction Gamma K - 1 := by
    have habs : -|polymerPartitionFunction Gamma K - 1|
        ≤ polymerPartitionFunction Gamma K - 1 := by
      exact neg_abs_le (polymerPartitionFunction Gamma K - 1)
    linarith
  linarith

/-- Any bound `|Z - 1| ≤ B` with `B < 1` forces positivity of `Z`. -/
theorem polymerPartitionFunction_pos_of_abs_Z_sub_one_lt_one
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (B : ℝ)
    (hB : |polymerPartitionFunction Gamma K - 1| ≤ B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  have hlt : |polymerPartitionFunction Gamma K - 1| < 1 :=
    lt_of_le_of_lt hB hsmall
  have hx : -1 < polymerPartitionFunction Gamma K - 1 := (abs_lt.mp hlt).1
  linarith

/-- Any bound `|Z - 1| ≤ B` with `B < 1` yields the upper free-energy bound
`log Z ≤ B`. -/
theorem log_polymerPartitionFunction_le_of_abs_Z_sub_one_le
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (B : ℝ)
    (hB : |polymerPartitionFunction Gamma K - 1| ≤ B)
    (hsmall : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  have hpos :
      0 < polymerPartitionFunction Gamma K :=
    polymerPartitionFunction_pos_of_abs_Z_sub_one_lt_one Gamma K B hB hsmall
  calc
    Real.log (polymerPartitionFunction Gamma K)
        ≤ polymerPartitionFunction Gamma K - 1 :=
      log_le_sub_one_of_pos _ hpos
    _ ≤ |polymerPartitionFunction Gamma K - 1| := le_abs_self _
    _ ≤ B := hB

/-- Any bound `|Z - 1| ≤ B` with `B ≤ 1/2` yields the two-sided bound
`|log Z| ≤ 2B`. -/
theorem log_polymerPartitionFunction_abs_le_two_mul_of_abs_Z_sub_one_le
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (B : ℝ)
    (hB : |polymerPartitionFunction Gamma K - 1| ≤ B)
    (hhalf : B ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hB
  have hsmall : B < 1 := by linarith
  have hpos :
      0 < polymerPartitionFunction Gamma K :=
    polymerPartitionFunction_pos_of_abs_Z_sub_one_lt_one Gamma K B hB hsmall
  have hZlb :
      1 - B ≤ polymerPartitionFunction Gamma K :=
    polymerPartitionFunction_lb_of_abs_Z_sub_one_le Gamma K B hB
  have h1mBpos : 0 < 1 - B := by linarith
  have hlog_mono :
      Real.log (1 - B) ≤ Real.log (polymerPartitionFunction Gamma K) := by
    exact Real.log_le_log h1mBpos hZlb
  have hub :
      Real.log (polymerPartitionFunction Gamma K) ≤ B :=
    log_polymerPartitionFunction_le_of_abs_Z_sub_one_le Gamma K B hB hsmall
  have hlb :
      -2 * B ≤ Real.log (polymerPartitionFunction Gamma K) := by
    have hbase : -2 * B ≤ Real.log (1 - B) :=
      Real.log_one_sub_ge_neg_two hB0 hhalf
    linarith
  rw [abs_le]
  constructor <;> linarith

/-! ## Weighted majorant consequences -/

/-- Weighted compatible-family majorant implies `1 - B ≤ Z`
under `1 ≤ w(X)` pointwise. -/
theorem polymerPartitionFunction_lb_of_kpWeightedMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B) :
    1 - B ≤ polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_lb_of_abs_Z_sub_one_le
    Gamma K B
    (abs_Z_sub_one_le_of_kpWeightedMajorant Gamma K w B hge hB)

/-- Weighted compatible-family majorant implies `0 < Z`
under `1 ≤ w(X)` and `B < 1`. -/
theorem polymerPartitionFunction_pos_of_kpWeightedMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_pos_of_abs_Z_sub_one_lt_one
    Gamma K B
    (abs_Z_sub_one_le_of_kpWeightedMajorant Gamma K w B hge hB)
    hsmall

/-- Weighted compatible-family majorant implies `log Z ≤ B`
under `1 ≤ w(X)` and `B < 1`. -/
theorem log_polymerPartitionFunction_le_of_kpWeightedMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B)
    (hsmall : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact log_polymerPartitionFunction_le_of_abs_Z_sub_one_le
    Gamma K B
    (abs_Z_sub_one_le_of_kpWeightedMajorant Gamma K w B hge hB)
    hsmall

/-- Weighted compatible-family majorant implies `|log Z| ≤ 2B`
under `1 ≤ w(X)` and `B ≤ 1/2`. -/
theorem log_polymerPartitionFunction_abs_le_two_mul_of_kpWeightedMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B)
    (hhalf : B ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B := by
  exact log_polymerPartitionFunction_abs_le_two_mul_of_abs_Z_sub_one_le
    Gamma K B
    (abs_Z_sub_one_le_of_kpWeightedMajorant Gamma K w B hge hB)
    hhalf

/-- Weighted compatible-family majorant yields the free-energy-ready interface:
`0 < Z` and `log Z ≤ B`. -/
theorem weightedFreeEnergyReady_of_kpWeightedMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K ∧
      Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  constructor
  · exact polymerPartitionFunction_pos_of_kpWeightedMajorant
      Gamma K w B hge hB hsmall
  · exact log_polymerPartitionFunction_le_of_kpWeightedMajorant
      Gamma K w B hge hB hsmall

/-! ## Weighted budget consequences -/

/-- Weighted induction-budget bound implies `1 - B ≤ Z`
under `1 ≤ w(X)` pointwise. -/
theorem polymerPartitionFunction_lb_of_kpWeightedBudget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B) :
    1 - B ≤ polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_lb_of_abs_Z_sub_one_le
    Gamma K B
    (abs_Z_sub_one_le_of_kpWeightedBudget Gamma K w B hge hB)

/-- Weighted induction-budget bound implies `0 < Z`
under `1 ≤ w(X)` and `B < 1`. -/
theorem polymerPartitionFunction_pos_of_kpWeightedBudget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_pos_of_abs_Z_sub_one_lt_one
    Gamma K B
    (abs_Z_sub_one_le_of_kpWeightedBudget Gamma K w B hge hB)
    hsmall

/-- Weighted induction-budget bound implies `log Z ≤ B`
under `1 ≤ w(X)` and `B < 1`. -/
theorem log_polymerPartitionFunction_le_of_kpWeightedBudget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hsmall : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact log_polymerPartitionFunction_le_of_abs_Z_sub_one_le
    Gamma K B
    (abs_Z_sub_one_le_of_kpWeightedBudget Gamma K w B hge hB)
    hsmall

/-- Weighted induction-budget bound implies `|log Z| ≤ 2B`
under `1 ≤ w(X)` and `B ≤ 1/2`. -/
theorem log_polymerPartitionFunction_abs_le_two_mul_of_kpWeightedBudget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hhalf : B ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B := by
  exact log_polymerPartitionFunction_abs_le_two_mul_of_abs_Z_sub_one_le
    Gamma K B
    (abs_Z_sub_one_le_of_kpWeightedBudget Gamma K w B hge hB)
    hhalf

/-- Weighted induction-budget bound yields the free-energy-ready interface:
`0 < Z` and `log Z ≤ B`. -/
theorem weightedFreeEnergyReady_of_kpWeightedBudget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K ∧
      Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  constructor
  · exact polymerPartitionFunction_pos_of_kpWeightedBudget
      Gamma K w B hge hB hsmall
  · exact log_polymerPartitionFunction_le_of_kpWeightedBudget
      Gamma K w B hge hB hsmall

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Exponential size-weight majorant implies `1 - B ≤ Z`. -/
theorem polymerPartitionFunction_lb_of_kpWeightedMajorant_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B) :
    1 - B ≤ polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_lb_of_kpWeightedMajorant
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB

/-- Exponential size-weight majorant implies `0 < Z` when `B < 1`. -/
theorem polymerPartitionFunction_pos_of_kpWeightedMajorant_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_pos_of_kpWeightedMajorant
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hsmall

/-- Exponential size-weight majorant implies `log Z ≤ B` when `B < 1`. -/
theorem log_polymerPartitionFunction_le_of_kpWeightedMajorant_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B)
    (hsmall : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact log_polymerPartitionFunction_le_of_kpWeightedMajorant
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hsmall

/-- Exponential size-weight majorant implies `|log Z| ≤ 2B`
when `B ≤ 1/2`. -/
theorem log_polymerPartitionFunction_abs_le_two_mul_of_kpWeightedMajorant_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B)
    (hhalf : B ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B := by
  exact log_polymerPartitionFunction_abs_le_two_mul_of_kpWeightedMajorant
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hhalf

/-- Exponential size-weight budget implies `1 - B ≤ Z`. -/
theorem polymerPartitionFunction_lb_of_kpWeightedBudget_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B) :
    1 - B ≤ polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_lb_of_kpWeightedBudget
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB

/-- Exponential size-weight budget implies `0 < Z` when `B < 1`. -/
theorem polymerPartitionFunction_pos_of_kpWeightedBudget_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K := by
  exact polymerPartitionFunction_pos_of_kpWeightedBudget
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hsmall

/-- Exponential size-weight budget implies `log Z ≤ B` when `B < 1`. -/
theorem log_polymerPartitionFunction_le_of_kpWeightedBudget_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hsmall : B < 1) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact log_polymerPartitionFunction_le_of_kpWeightedBudget
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hsmall

/-- Exponential size-weight budget implies `|log Z| ≤ 2B`
when `B ≤ 1/2`. -/
theorem log_polymerPartitionFunction_abs_le_two_mul_of_kpWeightedBudget_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hhalf : B ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)| ≤ 2 * B := by
  exact log_polymerPartitionFunction_abs_le_two_mul_of_kpWeightedBudget
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hhalf

/-- Free-energy-ready interface for the exponential size-weight lane. -/
theorem weightedFreeEnergyReady_of_kpWeightedBudget_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hsmall : B < 1) :
    0 < polymerPartitionFunction Gamma K ∧
      Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact weightedFreeEnergyReady_of_kpWeightedBudget
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB hsmall

end

end YangMills.ClayCore
