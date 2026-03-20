import Mathlib
import YangMills.ClayCore.BalabanRG.P91DataToDirectBudgetClay
import YangMills.ClayCore.BalabanRG.CauchyDecayFromAF

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91FiniteFullBridgeToDirectBudgetInterface — Layer 22W

This file isolates the next genuinely mathematical bridge.

What is already available:
* P91 data gives `physicalContractionRate (β_k) → 0`,
* the exp-size-weight finite-full bridge gives concrete sitewise bounds of the form
  `|fieldOfActivity K x| ≤ exp(-β_k) * dist K 0`
  and
  `|fieldOfActivity K₁ x - fieldOfActivity K₂ x|
      ≤ physicalContractionRate β_k * dist K₁ K₂`,
* the terminal KP exp-size-weight route already closes `ClayYangMillsTheorem`
  once we have the direct fit
  `KPWeightedInductionBudget ... ≤ theoreticalBudget ...`.

What is still missing:
* an actual derivation from those finite-full exp-size-weight bridge estimates
  to the direct weighted budget fit.

This file does not fake that derivation.
It packages the exact missing conversion as an explicit transfer interface.
-/

noncomputable section

/-- Exact missing conversion:
finite-full exp-size-weight bridge hypotheses at scale `0`
must eventually imply the direct budget fit needed by the terminal KP closure. -/
structure ExpSizeWeightFiniteFullToDirectBudgetTransfer
    (d N_c : ℕ) [NeZero N_c] where
  transfer :
    ∀ (a : ℝ),
      0 ≤ a →
      ∀ (β_k : ℝ),
        (1 : ℝ) ≤ Real.exp (-β_k) →
        (1 : ℝ) ≤ physicalContractionRate β_k →
        ∀ (polys : Finset (Polymer d (Int.ofNat 0)))
          (K : Activity d (Int.ofNat 0)),
          KPWeightedInductionBudget polys K (kpExpSizeWeight a d (Int.ofNat 0))
            ≤ theoreticalBudget polys K a

/-- Once the explicit finite-full → direct-budget transfer is supplied,
the concrete exp-size-weight bridge lane closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_expSizeWeightFiniteFullTransfer
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    (a : ℝ)
    (ha : 0 ≤ a)
    (β_k : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β_k))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β_k)
    (polys : Finset (Polymer d (Int.ofNat 0)))
    (K : Activity d (Int.ofNat 0))
    (htarget : theoreticalBudget polys K a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : ExpSizeWeightFiniteFullToDirectBudgetTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_kpExpSizeWeightDirectBudget
    polys K a ha
    (tr.transfer a ha β_k hlargeA hcauchyA polys K)
    htarget
    hN_c

/-- Combined package:
P91 recursion data together with the explicit finite-full → direct-budget
transfer target and the scalar hypotheses needed to apply it. -/
structure P91FiniteFullBridgeToDirectBudgetPackage
    {d : ℕ}
    (N_c : ℕ) [NeZero N_c]
    (K : Activity d (Int.ofNat 0))
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ) where
  data : P91RecursionData N_c
  hβ0 : 1 ≤ β 0
  hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)
  hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2
  hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c

  β_k : ℝ
  hlargeA : (1 : ℝ) ≤ Real.exp (-β_k)
  hcauchyA : (1 : ℝ) ≤ physicalContractionRate β_k

  polys : Finset (Polymer d (Int.ofNat 0))
  a_nonneg : 0 ≤ a
  target_lt_log2 : theoreticalBudget polys K a < Real.log 2
  rank_ok : 2 ≤ N_c

  directBudgetTransfer : ExpSizeWeightFiniteFullToDirectBudgetTransfer d N_c

/-- The P91 half still gives decay of the physical contraction rate. -/
theorem rate_to_zero_of_p91FiniteFullBridgeToDirectBudgetPackage
    {d : ℕ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d (Int.ofNat 0))
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91FiniteFullBridgeToDirectBudgetPackage N_c K a β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact rate_to_zero_from_af
    N_c pkg.data β r pkg.hβ0 pkg.hstep pkg.hr pkg.hβ_upper

/-- The transfer half closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_p91FiniteFullBridgeToDirectBudgetPackage
    {d : ℕ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d (Int.ofNat 0))
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91FiniteFullBridgeToDirectBudgetPackage N_c K a β r) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_expSizeWeightFiniteFullTransfer
    a pkg.a_nonneg
    pkg.β_k pkg.hlargeA pkg.hcauchyA
    pkg.polys K
    pkg.target_lt_log2
    pkg.rank_ok
    pkg.directBudgetTransfer

/-- Summary theorem:
P91 data supplies rate decay, and the explicit finite-full → direct-budget
transfer supplies terminal closure. -/
theorem p91_rate_and_clay_of_p91FiniteFullBridgeToDirectBudgetPackage
    {d : ℕ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d (Int.ofNat 0))
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91FiniteFullBridgeToDirectBudgetPackage N_c K a β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  constructor
  · exact rate_to_zero_of_p91FiniteFullBridgeToDirectBudgetPackage
      K a β r pkg
  · exact clayTheorem_of_p91FiniteFullBridgeToDirectBudgetPackage
      K a β r pkg

/-- Convenience constructor from raw ingredients. -/
def p91FiniteFullBridgeToDirectBudgetPackage_mk
    {d : ℕ}
    (N_c : ℕ) [NeZero N_c]
    (K : Activity d (Int.ofNat 0))
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (data : P91RecursionData N_c)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (β_k : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β_k))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β_k)
    (polys : Finset (Polymer d (Int.ofNat 0)))
    (ha : 0 ≤ a)
    (htarget : theoreticalBudget polys K a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : ExpSizeWeightFiniteFullToDirectBudgetTransfer d N_c) :
    P91FiniteFullBridgeToDirectBudgetPackage N_c K a β r where
  data := data
  hβ0 := hβ0
  hstep := hstep
  hr := hr
  hβ_upper := hβ_upper
  β_k := β_k
  hlargeA := hlargeA
  hcauchyA := hcauchyA
  polys := polys
  a_nonneg := ha
  target_lt_log2 := htarget
  rank_ok := hN_c
  directBudgetTransfer := tr

/-! ## Singleton specialization -/

/-- Singleton specialization of the exact missing transfer. -/
abbrev SingletonExpSizeWeightFiniteFullToDirectBudgetTransfer
    (d N_c : ℕ) [NeZero N_c] :=
  ExpSizeWeightFiniteFullToDirectBudgetTransfer d N_c

/-- Singleton consumer theorem:
once the finite-full exp-size-weight bridge is upgraded all the way to the
direct budget fit, the singleton scale-0 route closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_singletonExpSizeWeightFiniteFullTransfer
    {d : ℕ}
    {N_c : ℕ} [NeZero N_c]
    (a : ℝ)
    (ha : 0 ≤ a)
    (β_k : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β_k))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β_k)
    (X : Polymer d (Int.ofNat 0))
    (K : Activity d (Int.ofNat 0))
    (htarget :
      theoreticalBudget ({X} : Finset (Polymer d (Int.ofNat 0))) K a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : SingletonExpSizeWeightFiniteFullToDirectBudgetTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_expSizeWeightFiniteFullTransfer
    a ha β_k hlargeA hcauchyA
    ({X} : Finset (Polymer d (Int.ofNat 0))) K
    htarget hN_c tr

end

end YangMills.ClayCore
