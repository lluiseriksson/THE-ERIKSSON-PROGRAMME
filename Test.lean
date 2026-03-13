import Mathlib
import YangMills.L2_Balaban.SmallLargeDecomposition
import YangMills.L1_GibbsMeasure.GibbsMeasure

open YangMills MeasureTheory Set

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

-- Test 1: measurability of gaugeConfigEquiv.symm
example : Measurable (gaugeConfigEquiv (d:=d) (N:=N) (G:=G)).symm := by
  apply Measurable.of_comap_le
  simp [instMeasurableSpaceGaugeConfig]

-- Test 2: MeasurableSet {U | f U ≤ κ}
example (f : GaugeConfig d N G → ℝ) (hf : Measurable f) (κ : ℝ) :
    MeasurableSet {U | f U ≤ κ} :=
  measurableSet_le hf measurable_const

-- Test 3: evaluation of positive edge is measurable
example (e : PosEdge d N) :
    Measurable (fun U : GaugeConfig d N G => U.toFun e.val) := by
  have h_symm : Measurable (gaugeConfigEquiv (d:=d) (N:=N) (G:=G)).symm :=
    Measurable.of_comap_le (by simp [instMeasurableSpaceGaugeConfig])
  have h_eq : (fun U : GaugeConfig d N G => U.toFun e.val) =
      (fun f : PosEdge d N → G => f e) ∘ gaugeConfigEquiv.symm := by
    ext U; simp [gaugeConfigEquiv, configToPos]
  rw [h_eq]
  exact (measurable_pi_apply e).comp h_symm
