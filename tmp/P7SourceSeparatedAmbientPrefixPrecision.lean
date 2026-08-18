import tmp.P5PhysicalGreenScaleDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

# Exact CMP85 prefix precision on the separated CMP89 ambient carrier

This file supplies the precision-side companion of the P5 Green dictionary.
It fixes the bare physical mass to zero, uses the literal flowing CMP85
coefficient `a_j`, transports the resulting precision through the same
full-site equivalence as P5, and transports its generated coercivity without
loss.  The two inverse laws identify this one precision with the one P5 Green.

No Green, inverse identity, coercivity witness, regional action estimate or
window-15 inequality is accepted from the caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The final positive prefix at generated depth `depth+1` carries exactly
source coefficient index `depth`; the `j-1` shift is not inferred later. -/
theorem scratch_cmp85LastPositivePrefix_succ_sourceIndex (depth : ℕ) :
    (scratch_cmp85LastPositivePrefix (depth + 1)
      (Nat.succ_pos depth)).1.val - 1 = depth := by
  simp [scratch_cmp85LastPositivePrefix]

/-- Final positive-prefix precision before the separated-carrier reindexing.
The bare physical mass is fixed to zero inside the definition. -/
noncomputable def scratch_cmp89SourceSeparatedFinePrefixPrecision
    (hL : 2 ≤ L) (depth : ℕ) (spacing epsilon a : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :=
  scratch_cmp85SourceGeneratedPrefixPrecision
    (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
    (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    spacing epsilon 0 a background budget.toRadiusChain fineSmall
    (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))

/-- Exact robust coercivity floor generated for that same final prefix. -/
noncomputable def scratch_cmp89SourceSeparatedPrefixCoercivity
    (hL : 2 ≤ L) (depth : ℕ) (spacing epsilon a : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) : ℝ :=
  scratch_cmp85SourceGeneratedPrefixCoercivity
    (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
    (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    spacing epsilon a background budget.toRadiusChain fineSmall
    (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))

/-- The generated final-prefix coercivity floor is strictly positive under
the one visible Poincare absorption wall. -/
theorem scratch_cmp89SourceSeparatedPrefixCoercivity_pos
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :
    0 < scratch_cmp89SourceSeparatedPrefixCoercivity hL depth
      spacing epsilon a background budget fineSmall := by
  exact scratch_cmp85SourceGeneratedPrefixCoercivity_pos
    (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
    (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    hspacing ha background budget.toRadiusChain fineSmall hsmall
    (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))

/-- The exact CMP85 prefix precision on the separated ambient carrier. -/
noncomputable def scratch_cmp89SourceSeparatedAmbientPrefixPrecision
    (hL : 2 ≤ L) (depth : ℕ) (spacing epsilon a : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :=
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  finitePiLpTypedKernelReindex e e
    (scratch_cmp89SourceSeparatedFinePrefixPrecision hL depth
      spacing epsilon a background budget fineSmall)

/-- Square isometric reindexing preserves the exact generated coercivity
constant; no separately chosen regional coercivity witness occurs. -/
theorem scratch_isCoerciveCLM_cmp89SourceSeparatedAmbientPrefixPrecision
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :
    IsCoerciveCLM
      (scratch_cmp89SourceSeparatedAmbientPrefixPrecision hL depth
        spacing epsilon a background budget fineSmall)
      (scratch_cmp89SourceSeparatedPrefixCoercivity hL depth
        spacing epsilon a background budget fineSmall) := by
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  apply isCoerciveCLM_finitePiLpTypedKernelReindex e
  exact scratch_isCoerciveCLM_cmp85SourceGeneratedPrefixPrecision
    (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
    (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    hspacing ha 0 background budget.toRadiusChain fineSmall hsmall
    (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))

/-- The exact separated ambient precision followed by the P5 Green is the
identity. -/
theorem scratch_cmp89SourceSeparatedAmbientPrefixPrecision_comp_green
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :
    (scratch_cmp89SourceSeparatedAmbientPrefixPrecision hL depth
      spacing epsilon a background budget fineSmall).comp
        (scratch_cmp89SourceSeparatedAmbientPrefixGreen hL depth
          hspacing ha background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
          (SUNLieCoord Nc)) := by
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  exact finitePiLpTypedKernelReindex_comp_eq_id e
    (scratch_cmp89SourceSeparatedFinePrefixPrecision hL depth
      spacing epsilon a background budget fineSmall)
    (scratch_cmp89SourceSeparatedFinePrefixGreen hL depth hspacing ha
      background budget fineSmall hsmall)
    (scratch_cmp85SourceGeneratedPrefixPrecision_comp_green
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
      hspacing ha 0 background budget.toRadiusChain fineSmall hsmall
      (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)))

/-- The P5 Green followed by the same exact separated ambient precision is
the identity. -/
theorem scratch_cmp89SourceSeparatedAmbientPrefixGreen_comp_precision
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :
    (scratch_cmp89SourceSeparatedAmbientPrefixGreen hL depth
      hspacing ha background budget fineSmall hsmall).comp
        (scratch_cmp89SourceSeparatedAmbientPrefixPrecision hL depth
          spacing epsilon a background budget fineSmall) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
          (SUNLieCoord Nc)) := by
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  exact finitePiLpTypedKernelReindex_comp_eq_id e
    (scratch_cmp89SourceSeparatedFinePrefixGreen hL depth hspacing ha
      background budget fineSmall hsmall)
    (scratch_cmp89SourceSeparatedFinePrefixPrecision hL depth
      spacing epsilon a background budget fineSmall)
    (scratch_cmp85SourceGeneratedPrefixGreen_comp_precision
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
      hspacing ha 0 background budget.toRadiusChain fineSmall hsmall
      (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)))

end

end YangMills.RG
