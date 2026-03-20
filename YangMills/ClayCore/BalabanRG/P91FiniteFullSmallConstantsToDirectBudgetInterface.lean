import Mathlib
import YangMills.ClayCore.BalabanRG.P91DataToDirectBudgetClay
import YangMills.ClayCore.BalabanRG.ExpPolymerSizeWeight
import YangMills.ClayCore.BalabanRG.FullLargeFieldSuppressionFinite
import YangMills.ClayCore.BalabanRG.CauchyDecayViaBridgeFiniteFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Filter

/-!
# P91FiniteFullSmallConstantsToDirectBudgetInterface — Layer 22W-honest

This file records the honest finite-full gap:

* finite-full exp-size-weight control should first produce genuine small
  constants `A_large`, `A_cauchy`,
* those constants must refine to
  `A_large ≤ exp(-β_k)` and `A_cauchy ≤ physicalContractionRate β_k`,
* only then can one hope to derive the direct weighted budget fit needed by the
  terminal KP closure.

Nothing here fakes that derivation. It packages it explicitly.
-/

noncomputable section

/-- Honest scale-0 exp-size-weight finite-full small-constants package. -/
structure ExpSizeWeightFiniteFullSmallConstantPackage
    (d N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))] where
  a : ℝ
  ha : 0 ≤ a
  β_k : ℝ
  polys : Finset (Polymer d (Int.ofNat 0))
  A_large : ℝ
  A_cauchy : ℝ
  hlarge :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) a ha
    ∀ (K : ActivityFamily d (0 : ℕ)) (x : BalabanFiniteSite d 0),
      |(canonicalGeometricBridgeFull polys).fieldOfActivity K x|
        ≤ A_large * ActivityNorm.dist K (fun _ => 0)
  hlargeA : A_large ≤ Real.exp (-β_k)
  hcauchy :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) a ha
    ∀ (K₁ K₂ : ActivityFamily d (0 : ℕ)) (x : BalabanFiniteSite d 0),
      |(canonicalGeometricBridgeFull polys).fieldOfActivity K₁ x -
        (canonicalGeometricBridgeFull polys).fieldOfActivity K₂ x|
        ≤ A_cauchy * ActivityNorm.dist K₁ K₂
  hcauchyA : A_cauchy ≤ physicalContractionRate β_k

/-- The honest small-constants package upgrades to the standard finite-full
control package. -/
def ExpSizeWeightFiniteFullSmallConstantPackage.toControl
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (pkg : ExpSizeWeightFiniteFullSmallConstantPackage d N_c) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) pkg.a pkg.ha
    RGViaBridgeControlFull d N_c 0 pkg.β_k := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromExpSizeWeight (d := d) pkg.a pkg.ha
  exact finiteCanonicalGeometricBridgeControlFull
    (d := d) (N_c := N_c) 0 pkg.β_k pkg.polys
    (by
      intro K x
      exact le_trans (pkg.hlarge K x)
        (mul_le_mul_of_nonneg_right pkg.hlargeA
          (ActivityNorm.dist_nonneg K (fun _ => 0))))
    (by
      intro K₁ K₂ x
      exact le_trans (pkg.hcauchy K₁ K₂ x)
        (mul_le_mul_of_nonneg_right pkg.hcauchyA
          (ActivityNorm.dist_nonneg K₁ K₂)))

/-- High-level consumer from the honest exp-size-weight finite-full
small-constants package. -/
theorem cauchy_decay_of_expSizeWeightFiniteFullSmallConstantPackage
    {d N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (pkg : ExpSizeWeightFiniteFullSmallConstantPackage d N_c)
    (K₁ K₂ : ActivityFamily d (0 : ℕ))
    (x : BalabanFiniteSite d 0) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) pkg.a pkg.ha
    let ctrl := pkg.toControl
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-pkg.β_k) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate pkg.β_k * ActivityNorm.dist K₁ K₂) := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromExpSizeWeight (d := d) pkg.a pkg.ha
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

/-- Exact remaining conversion: honest exp-size-weight finite-full small
constants must imply the direct weighted budget fit. -/
structure ExpSizeWeightFiniteFullSmallConstantToDirectBudgetTransfer
    (d N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))] where
  transfer :
    ∀ (pkg : ExpSizeWeightFiniteFullSmallConstantPackage d N_c)
      (K : Activity d (Int.ofNat 0)),
      KPWeightedInductionBudget pkg.polys K (kpExpSizeWeight pkg.a d (Int.ofNat 0))
        ≤ theoreticalBudget pkg.polys K pkg.a

/-- Once the honest small-constants → direct-budget transfer is supplied, the
exp-size-weight finite-full lane closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_expSizeWeightFiniteFullSmallConstantTransfer
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (pkg : ExpSizeWeightFiniteFullSmallConstantPackage d N_c)
    (K : Activity d (Int.ofNat 0))
    (htarget : theoreticalBudget pkg.polys K pkg.a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : ExpSizeWeightFiniteFullSmallConstantToDirectBudgetTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_kpExpSizeWeightDirectBudget
    pkg.polys K pkg.a pkg.ha
    (tr.transfer pkg K) htarget hN_c

/-- Combined package: P91 recursion data plus the honest finite-full
small-constants witness and the explicit direct-budget transfer target. -/
structure P91FiniteFullSmallConstantToDirectBudgetPackage
    {d : ℕ} (N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0)) (β : ℕ → ℝ) (r : ℕ → ℝ) where
  data : P91RecursionData N_c
  hβ0 : 1 ≤ β 0
  hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)
  hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2
  hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c
  smallConstants : ExpSizeWeightFiniteFullSmallConstantPackage d N_c
  target_lt_log2 :
    theoreticalBudget smallConstants.polys K smallConstants.a < Real.log 2
  rank_ok : 2 ≤ N_c
  directBudgetTransfer :
    ExpSizeWeightFiniteFullSmallConstantToDirectBudgetTransfer d N_c

/-- The P91 half still gives decay of the physical contraction rate. -/
theorem rate_to_zero_of_p91FiniteFullSmallConstantToDirectBudgetPackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantToDirectBudgetPackage N_c K β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact rate_to_zero_from_af
    N_c pkg.data β r pkg.hβ0 pkg.hstep pkg.hr pkg.hβ_upper

/-- The transfer half closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_p91FiniteFullSmallConstantToDirectBudgetPackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantToDirectBudgetPackage N_c K β r) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_expSizeWeightFiniteFullSmallConstantTransfer
    pkg.smallConstants K pkg.target_lt_log2 pkg.rank_ok pkg.directBudgetTransfer

/-- Summary theorem: P91 data supplies rate decay, and the honest finite-full
small-constants → direct-budget transfer supplies terminal closure. -/
theorem p91_rate_and_clay_of_p91FiniteFullSmallConstantToDirectBudgetPackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullSmallConstantToDirectBudgetPackage N_c K β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  constructor
  · exact rate_to_zero_of_p91FiniteFullSmallConstantToDirectBudgetPackage K β r pkg
  · exact clayTheorem_of_p91FiniteFullSmallConstantToDirectBudgetPackage K β r pkg

end

end YangMills.ClayCore
