import Mathlib
import YangMills.ClayCore.BalabanRG.P91FiniteFullSmallConstantsToDirectBudgetInterface
import YangMills.ClayCore.BalabanRG.P91FiniteFullSmallConstantsFinalGapWitness

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Filter

/-!
# P91FiniteFullSmallConstantsLaneSymmetry — Layer 22W-symmetry

Small registry file sealing the symmetry between the two currently honest
finite-full terminal lanes:

1. **direct-budget lane**
   `small constants -> direct budget -> ClayYangMillsTheorem`,
2. **native-target lane**
   `small constants -> native target envelope -> final gap witness
    -> ClayYangMillsTheorem`.

This file adds no new mathematics.
It only presents the two terminal closures side by side under a common
consumer-facing interface.
-/

noncomputable section

/-- Consumer-facing registry: both honest finite-full terminal lanes, written
with matching fields. -/
structure P91FiniteFullSmallConstantsSymmetryRegistry
    {d : ℕ} (N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ) where
  directLane :
    P91FiniteFullSmallConstantToDirectBudgetPackage (d := d) N_c K β r
  nativeLane :
    P91FiniteFullSmallConstantsFinalGapWitness (d := d) N_c β r

/-- Direct-budget lane: AF decay plus terminal Clay closure. -/
theorem direct_lane_rate_and_clay
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (reg : P91FiniteFullSmallConstantsSymmetryRegistry (d := d) N_c K β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  exact p91_rate_and_clay_of_p91FiniteFullSmallConstantToDirectBudgetPackage
    (d := d) K β r reg.directLane

/-- Native-target lane: AF decay plus terminal Clay closure. -/
theorem native_lane_rate_and_clay
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (reg : P91FiniteFullSmallConstantsSymmetryRegistry (d := d) N_c K β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  exact p91_rate_and_clay_of_p91FiniteFullSmallConstantsFinalGapWitness
    (d := d) β r reg.nativeLane

/-- Both honest finite-full terminal lanes now expose the same end product:
AF-side rate decay and `ClayYangMillsTheorem`. -/
theorem p91_finiteFull_smallConstants_lane_symmetry
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (reg : P91FiniteFullSmallConstantsSymmetryRegistry (d := d) N_c K β r) :
    (Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem) ∧
    (Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem) := by
  constructor
  · exact direct_lane_rate_and_clay (d := d) K β r reg
  · exact native_lane_rate_and_clay (d := d) K β r reg

/-- Convenience theorem exposing only the common terminal consequence, choosing
the direct lane. -/
theorem clayTheorem_of_p91FiniteFullSmallConstantsSymmetryRegistry_via_direct
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (reg : P91FiniteFullSmallConstantsSymmetryRegistry (d := d) N_c K β r) :
    YangMills.ClayYangMillsTheorem := by
  exact (direct_lane_rate_and_clay (d := d) K β r reg).2

/-- Convenience theorem exposing only the common terminal consequence, choosing
the native-target lane. -/
theorem clayTheorem_of_p91FiniteFullSmallConstantsSymmetryRegistry_via_native
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (reg : P91FiniteFullSmallConstantsSymmetryRegistry (d := d) N_c K β r) :
    YangMills.ClayYangMillsTheorem := by
  exact (native_lane_rate_and_clay (d := d) K β r reg).2

end

end YangMills.ClayCore
