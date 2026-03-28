import Mathlib
import YangMills.ClayCore.BalabanRG.P91FiniteFullSmallConstantsToDirectBudgetInterface
import YangMills.ClayCore.BalabanRG.WeightedNativeTargetWitness
import YangMills.ClayCore.BalabanRG.WeightedToMassGapReadyPackage

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Filter

/-!
# P91FiniteFullSmallConstantsNativeTargetEnvelope — Layer 22W-native

Honest terminal witness layer for the finite-full small-constants route at the
native target budget.

This file does **not** prove the missing finite-full direct-budget transfer.
Instead it isolates a weaker reusable target:

* produce a scalar witness `B`,
* prove
  `KPWeightedInductionBudget ... ≤ B`,
* prove
  `B ≤ exp(theoreticalBudget ...) - 1`,
* conclude the native free-energy interface,
* export the standard mass-gap-ready package already used upstairs.

So the remaining gap is now reduced to a concrete native-target envelope
witness, without pretending to derive the direct-budget fit.
-/

noncomputable section

/-- Honest terminal witness for the finite-full exp-size-weight route at the
native target budget. -/
structure ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
    (d N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))] where
  _ : ExpSizeWeightFiniteFullSmallConstantPackage d N_c
  K : Activity d (Int.ofNat 0)
  B : ℝ
  hbudget :
    KPWeightedInductionBudget pkg.polys K
      (kpExpSizeWeight pkg.a d (Int.ofNat 0)) ≤ B
  hfit :
    B ≤ Real.exp (theoreticalBudget pkg.polys K pkg.a) - 1
  htarget :
    theoreticalBudget pkg.polys K pkg.a < Real.log 2

/-- The native-target inequality extracted from the envelope. -/
theorem nativeTarget_of_expSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (env : ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c) :
    KPWeightedInductionBudget env.pkg.polys env.K
      (kpExpSizeWeight env.pkg.a d (Int.ofNat 0))
      ≤ Real.exp (theoreticalBudget env.pkg.polys env.K env.pkg.a) - 1 := by
  exact le_trans env.hbudget env.hfit

/-- The envelope yields the canonical native-target witness object. -/
def ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope.toWitness
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (env : ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c) :
    WeightedNativeTargetWitness env.pkg.polys env.K env.pkg.a :=
  expSizeWeightNativeTargetWitness
    env.pkg.polys env.K env.pkg.a env.pkg.a env.pkg.ha
    (nativeTarget_of_expSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
      (d := d) env)

/-- The honest native-target envelope discharges the native free-energy control
interface. -/
theorem freeEnergyControlAtScale_of_expSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (env : ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c) :
    FreeEnergyControlAtScale env.pkg.polys env.K env.pkg.a := by
  exact freeEnergyControlAtScale_of_weightedNativeTargetWitness
    env.pkg.polys env.K env.pkg.a
    (env.toWitness) env.htarget

/-- The honest native-target envelope canonically exports the standard
mass-gap-ready package. -/
def ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope.toMassGapReadyPackage
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (env : ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c) :
    MassGapReadyPackage N_c env.pkg.polys env.K env.pkg.a :=
  expSizeWeightMassGapReadyPackage
    N_c env.pkg.polys env.K env.pkg.a env.pkg.a env.pkg.ha
    (nativeTarget_of_expSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
      (d := d) env)
    env.htarget

/-- The exported mass-gap-ready package carries exactly the upstairs pair:
native free-energy control plus an explicit positive LSI witness. -/
theorem massGapReadyPackage_ready_of_expSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (env : ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c) :
    FreeEnergyControlAtScale env.pkg.polys env.K env.pkg.a ∧
      ClayCoreLSI d N_c (env.toMassGapReadyPackage.lsiConst) := by
  exact massGapReadyPackage_ready
    env.pkg.polys env.K env.pkg.a
    (env.toMassGapReadyPackage)

/-- Existential consumer-facing export from the honest native-target envelope. -/
theorem exists_massGapReadyPackage_of_expSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (env : ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c) :
    ∃ pkgM : MassGapReadyPackage N_c env.pkg.polys env.K env.pkg.a,
      FreeEnergyControlAtScale env.pkg.polys env.K env.pkg.a ∧
        ClayCoreLSI d N_c pkgM.lsiConst := by
  refine ⟨env.toMassGapReadyPackage, ?_⟩
  exact massGapReadyPackage_ready_of_expSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
    (d := d) env

/-- Combined package: P91 recursion data plus an honest finite-full
native-target envelope witness. -/
structure P91FiniteFullSmallConstantNativeTargetEnvelopePackage
    {d : ℕ} (N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ) where
  data : P91RecursionData N_c
  hβ0 : 1 ≤ β 0
  hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)
  hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2
  hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c
  envelope : ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c

/-- The P91 half still gives decay of the physical contraction rate. -/
theorem rate_to_zero_of_p91FiniteFullSmallConstantNativeTargetEnvelopePackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantNativeTargetEnvelopePackage (d := d) N_c β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact rate_to_zero_from_af
    N_c pkg.data β r pkg.hβ0 pkg.hstep pkg.hr pkg.hβ_upper

/-- Canonical mass-gap-ready package exported from the combined P91 native-target
envelope package. -/
def massGapReadyPackage_of_p91FiniteFullSmallConstantNativeTargetEnvelopePackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantNativeTargetEnvelopePackage (d := d) N_c β r) :
    MassGapReadyPackage N_c pkg.envelope.pkg.polys pkg.envelope.K pkg.envelope.pkg.a :=
  pkg.envelope.toMassGapReadyPackage

/-- The native-target envelope half exports the standard upstairs-ready package.
-/
theorem exists_massGapReadyPackage_of_p91FiniteFullSmallConstantNativeTargetEnvelopePackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantNativeTargetEnvelopePackage (d := d) N_c β r) :
    ∃ pkgM : MassGapReadyPackage N_c pkg.envelope.pkg.polys pkg.envelope.K pkg.envelope.pkg.a,
      FreeEnergyControlAtScale pkg.envelope.pkg.polys pkg.envelope.K pkg.envelope.pkg.a ∧
        ClayCoreLSI d N_c pkgM.lsiConst := by
  exact
    exists_massGapReadyPackage_of_expSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
      (d := d) pkg.envelope

/-- Summary theorem: P91 data supplies rate decay, and the honest finite-full
native-target envelope supplies the standard mass-gap-ready package. -/
theorem p91_rate_and_massGapReady_of_p91FiniteFullSmallConstantNativeTargetEnvelopePackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantNativeTargetEnvelopePackage (d := d) N_c β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      ∃ pkgM : MassGapReadyPackage N_c pkg.envelope.pkg.polys pkg.envelope.K pkg.envelope.pkg.a,
        FreeEnergyControlAtScale pkg.envelope.pkg.polys pkg.envelope.K pkg.envelope.pkg.a ∧
          ClayCoreLSI d N_c pkgM.lsiConst := by
  constructor
  · exact rate_to_zero_of_p91FiniteFullSmallConstantNativeTargetEnvelopePackage
      (d := d) β r pkg
  · exact exists_massGapReadyPackage_of_p91FiniteFullSmallConstantNativeTargetEnvelopePackage
      (d := d) β r pkg

/-! ## Singleton specialization -/

/-- Singleton specialization of the honest finite-full native-target envelope. -/
structure SingletonExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
    (d N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))] where
  X : Polymer d (Int.ofNat 0)
  env : ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c
  hpolys : env.pkg.polys = ({X} : Finset (Polymer d (Int.ofNat 0)))

/-- Singleton honest finite-full native-target envelope exports the standard
upstairs-ready package. -/
theorem exists_massGapReadyPackage_of_singletonExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (senv : SingletonExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c) :
    ∃ pkgM : MassGapReadyPackage N_c senv.env.pkg.polys senv.env.K senv.env.pkg.a,
      FreeEnergyControlAtScale senv.env.pkg.polys senv.env.K senv.env.pkg.a ∧
        ClayCoreLSI d N_c pkgM.lsiConst := by
  exact
    exists_massGapReadyPackage_of_expSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
      senv.env

/-- Convenience constructor from a raw native-target envelope witness `B`. -/
def mkExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (pkg : ExpSizeWeightFiniteFullSmallConstantPackage d N_c)
    (K : Activity d (Int.ofNat 0))
    (B : ℝ)
    (hbudget :
      KPWeightedInductionBudget pkg.polys K
        (kpExpSizeWeight pkg.a d (Int.ofNat 0)) ≤ B)
    (hfit :
      B ≤ Real.exp (theoreticalBudget pkg.polys K pkg.a) - 1)
    (htarget :
      theoreticalBudget pkg.polys K pkg.a < Real.log 2) :
    ExpSizeWeightFiniteFullSmallConstantNativeTargetEnvelope d N_c := by
  refine
    { _ := pkg
      K := K
      B := B
      hbudget := hbudget
      hfit := hfit
      htarget := htarget }

end

end YangMills.ClayCore
