import Mathlib
import YangMills.ClayCore.BalabanRG.P91FiniteFullSmallConstantsNativeTargetEnvelope
import YangMills.ClayCore.BalabanRG.WeightedFinalGapWitness

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Filter

/-!
# P91FiniteFullSmallConstantsFinalGapWitness — Layer 22W-final

Final native-target witness for the honest finite-full small-constants lane.

This file does **not** invent a new finite-full transfer.
It only packages the native-target envelope together with:

* the P91 / AF recursion data,
* a chosen physical terminal scale parameter `β_final`,
* the final transfer `ClayCoreLSIToSUNDLRTransfer d N_c`.

With these data the native-target finite-full lane reaches the existing
terminal consumer theorem `ClayYangMillsTheorem`.
-/

noncomputable section

/-- Final witness for the honest finite-full small-constants native-target
lane. -/
structure P91FiniteFullSmallConstantsFinalGapWitness
    {d : ℕ} (N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ) where
  nativeEnvelope :
    P91FiniteFullSmallConstantNativeTargetEnvelopePackage (d := d) N_c β r
  β_final : ℝ
  hN_c : 2 ≤ N_c
  hβ :
    (expSizeWeightMassGapReadyPackage
      N_c
      nativeEnvelope.envelope.pkg.polys
      nativeEnvelope.envelope.K
      nativeEnvelope.envelope.pkg.a
      nativeEnvelope.envelope.pkg.a
      nativeEnvelope.envelope.pkg.ha
      (le_trans nativeEnvelope.envelope.hbudget nativeEnvelope.envelope.hfit)
      nativeEnvelope.envelope.htarget).lsiConst ≤ β_final
  transfer : ClayCoreLSIToSUNDLRTransfer d N_c

/-- The final witness canonically produces the already existing weighted final
gap witness. -/
def P91FiniteFullSmallConstantsFinalGapWitness.toWeightedFinalGapWitness
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    {β : ℕ → ℝ} {r : ℕ → ℝ}
    (wit : P91FiniteFullSmallConstantsFinalGapWitness (d := d) N_c β r) :
    WeightedFinalGapWitness
      N_c
      wit.nativeEnvelope.envelope.pkg.polys
      wit.nativeEnvelope.envelope.K
      wit.nativeEnvelope.envelope.pkg.a :=
  expSizeWeightFinalGapWitness
    N_c
    wit.nativeEnvelope.envelope.pkg.polys
    wit.nativeEnvelope.envelope.K
    wit.nativeEnvelope.envelope.pkg.a
    wit.nativeEnvelope.envelope.pkg.a
    wit.β_final
    wit.nativeEnvelope.envelope.pkg.ha
    (le_trans wit.nativeEnvelope.envelope.hbudget wit.nativeEnvelope.envelope.hfit)
    wit.nativeEnvelope.envelope.htarget
    wit.hN_c
    wit.hβ
    wit.transfer

/-- The P91 half still gives decay of the physical contraction rate. -/
theorem rate_to_zero_of_p91FiniteFullSmallConstantsFinalGapWitness
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (wit : P91FiniteFullSmallConstantsFinalGapWitness (d := d) N_c β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact rate_to_zero_of_p91FiniteFullSmallConstantNativeTargetEnvelopePackage
    (d := d) β r wit.nativeEnvelope

/-- The final witness also exposes the concrete P8 DLR-LSI consumer output. -/
theorem sun_dlr_lsi_of_p91FiniteFullSmallConstantsFinalGapWitness
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (wit : P91FiniteFullSmallConstantsFinalGapWitness (d := d) N_c β r) :
    ∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI
        (YangMills.sunGibbsFamily d N_c wit.β_final)
        (YangMills.sunDirichletForm N_c)
        α_star := by
  exact sun_dlr_lsi_of_weightedFinalGapWitness
    wit.nativeEnvelope.envelope.pkg.polys
    wit.nativeEnvelope.envelope.K
    wit.nativeEnvelope.envelope.pkg.a
    wit.toWeightedFinalGapWitness

/-- Final native-target closure of the honest finite-full small-constants lane.
-/
theorem clayTheorem_of_p91FiniteFullSmallConstantsFinalGapWitness
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (wit : P91FiniteFullSmallConstantsFinalGapWitness (d := d) N_c β r) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_weightedFinalGapWitness
    wit.nativeEnvelope.envelope.pkg.polys
    wit.nativeEnvelope.envelope.K
    wit.nativeEnvelope.envelope.pkg.a
    wit.toWeightedFinalGapWitness

/-- Summary theorem: P91 data still supplies AF-side rate decay, and the final
native-target witness closes `ClayYangMillsTheorem`. -/
theorem p91_rate_and_clay_of_p91FiniteFullSmallConstantsFinalGapWitness
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (wit : P91FiniteFullSmallConstantsFinalGapWitness (d := d) N_c β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  constructor
  · exact rate_to_zero_of_p91FiniteFullSmallConstantsFinalGapWitness
      (d := d) β r wit
  · exact clayTheorem_of_p91FiniteFullSmallConstantsFinalGapWitness
      (d := d) β r wit

/-- Convenience constructor from the native-target envelope package plus the
terminal physical scale / transfer data. -/
def p91FiniteFullSmallConstantsFinalGapWitness_mk
    {d : ℕ} (N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (nativeEnvelope :
      P91FiniteFullSmallConstantNativeTargetEnvelopePackage (d := d) N_c β r)
    (β_final : ℝ)
    (hN_c : 2 ≤ N_c)
    (hβ :
      (expSizeWeightMassGapReadyPackage
        N_c
        nativeEnvelope.envelope.pkg.polys
        nativeEnvelope.envelope.K
        nativeEnvelope.envelope.pkg.a
        nativeEnvelope.envelope.pkg.a
        nativeEnvelope.envelope.pkg.ha
        (le_trans nativeEnvelope.envelope.hbudget nativeEnvelope.envelope.hfit)
        nativeEnvelope.envelope.htarget).lsiConst ≤ β_final)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    P91FiniteFullSmallConstantsFinalGapWitness (d := d) N_c β r := by
  refine
    { nativeEnvelope := nativeEnvelope
      β_final := β_final
      hN_c := hN_c
      hβ := hβ
      transfer := tr }

end

end YangMills.ClayCore
