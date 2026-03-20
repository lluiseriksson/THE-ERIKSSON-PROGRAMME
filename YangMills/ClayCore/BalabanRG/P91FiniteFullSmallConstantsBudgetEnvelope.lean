import Mathlib
import YangMills.ClayCore.BalabanRG.P91FiniteFullSmallConstantsToDirectBudgetInterface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Filter

/-!
# P91FiniteFullSmallConstantsBudgetEnvelope — Layer 22W-envelope

Honest terminal witness layer for the finite-full small-constants route.

This file does **not** prove the missing finite-full transfer. Instead it isolates
the next concrete target:

* produce a budget witness `B`,
* prove
  `KPWeightedInductionBudget ... ≤ B`,
* prove
  `B ≤ theoreticalBudget ...`,
* conclude `ClayYangMillsTheorem`.

So the remaining mathematical gap is reduced from a full direct-budget transfer
schema to a concrete budget-envelope witness.
-/

noncomputable section

/-- Honest terminal witness for the finite-full exp-size-weight route. -/
structure ExpSizeWeightFiniteFullSmallConstantBudgetEnvelope
    (d N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))] where
  pkg : ExpSizeWeightFiniteFullSmallConstantPackage d N_c
  K : Activity d (Int.ofNat 0)
  B : ℝ
  hbudget :
    KPWeightedInductionBudget pkg.polys K
      (kpExpSizeWeight pkg.a d (Int.ofNat 0)) ≤ B
  hfit :
    B ≤ theoreticalBudget pkg.polys K pkg.a
  htarget :
    theoreticalBudget pkg.polys K pkg.a < Real.log 2
  hN_c : 2 ≤ N_c

/-- The direct-budget inequality extracted from the budget envelope. -/
theorem directBudget_of_expSizeWeightFiniteFullSmallConstantBudgetEnvelope
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (env : ExpSizeWeightFiniteFullSmallConstantBudgetEnvelope d N_c) :
    KPWeightedInductionBudget env.pkg.polys env.K
      (kpExpSizeWeight env.pkg.a d (Int.ofNat 0))
      ≤ theoreticalBudget env.pkg.polys env.K env.pkg.a := by
  exact le_trans env.hbudget env.hfit

/-- The honest budget-envelope witness closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_expSizeWeightFiniteFullSmallConstantBudgetEnvelope
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (env : ExpSizeWeightFiniteFullSmallConstantBudgetEnvelope d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_kpExpSizeWeightDirectBudget
    env.pkg.polys env.K env.pkg.a env.pkg.ha
    (directBudget_of_expSizeWeightFiniteFullSmallConstantBudgetEnvelope env)
    env.htarget env.hN_c

/-- Combined package: P91 recursion data plus an honest finite-full
budget-envelope witness. -/
structure P91FiniteFullSmallConstantBudgetEnvelopePackage
    {d : ℕ} (N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ) where
  data : P91RecursionData N_c
  hβ0 : 1 ≤ β 0
  hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)
  hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2
  hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c
  envelope : ExpSizeWeightFiniteFullSmallConstantBudgetEnvelope d N_c

/-- The P91 half still gives decay of the physical contraction rate. -/
theorem rate_to_zero_of_p91FiniteFullSmallConstantBudgetEnvelopePackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantBudgetEnvelopePackage (d := d) N_c β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact rate_to_zero_from_af
    N_c pkg.data β r pkg.hβ0 pkg.hstep pkg.hr pkg.hβ_upper

/-- The honest finite-full budget-envelope witness closes
`ClayYangMillsTheorem`. -/
theorem clayTheorem_of_p91FiniteFullSmallConstantBudgetEnvelopePackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantBudgetEnvelopePackage (d := d) N_c β r) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_expSizeWeightFiniteFullSmallConstantBudgetEnvelope
    pkg.envelope

/-- Summary theorem: P91 data supplies rate decay, and the honest finite-full
budget-envelope witness supplies terminal closure. -/
theorem p91_rate_and_clay_of_p91FiniteFullSmallConstantBudgetEnvelopePackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantBudgetEnvelopePackage (d := d) N_c β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  constructor
  · exact rate_to_zero_of_p91FiniteFullSmallConstantBudgetEnvelopePackage (d := d) β r pkg
  · exact clayTheorem_of_p91FiniteFullSmallConstantBudgetEnvelopePackage (d := d) β r pkg

/-! ## Singleton specialization -/

/-- Singleton specialization of the honest finite-full budget envelope. -/
structure SingletonExpSizeWeightFiniteFullSmallConstantBudgetEnvelope
    (d N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))] where
  X : Polymer d (Int.ofNat 0)
  env : ExpSizeWeightFiniteFullSmallConstantBudgetEnvelope d N_c
  hpolys : env.pkg.polys = ({X} : Finset (Polymer d (Int.ofNat 0)))

/-- Singleton honest finite-full budget envelope closes `ClayYangMillsTheorem`.
-/
theorem clayTheorem_of_singletonExpSizeWeightFiniteFullSmallConstantBudgetEnvelope
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (senv : SingletonExpSizeWeightFiniteFullSmallConstantBudgetEnvelope d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_expSizeWeightFiniteFullSmallConstantBudgetEnvelope senv.env

/-- Convenience constructor from a raw budget witness `B`. -/
def mkExpSizeWeightFiniteFullSmallConstantBudgetEnvelope
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
      B ≤ theoreticalBudget pkg.polys K pkg.a)
    (htarget :
      theoreticalBudget pkg.polys K pkg.a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    ExpSizeWeightFiniteFullSmallConstantBudgetEnvelope d N_c := by
  refine
    { pkg := pkg
      K := K
      B := B
      hbudget := hbudget
      hfit := hfit
      htarget := htarget
      hN_c := hN_c }

end

end YangMills.ClayCore
