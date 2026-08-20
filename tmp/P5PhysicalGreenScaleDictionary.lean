import tmp.P4bFiniteTelescoping
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary
import YangMills.RG.FinitePiLpTypedKernelReindexAlgebra

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only carrier and scale dictionary from CMP85 (2.43) to the regional
CMP89 (2.34) presentation.

The RG ratio `L` and the independent regional large-block factor `K` remain
different parameters.  The prefix Green chain is generated on the full
coarse carrier `2*(K*Q)` with `M := L`; only after the source identity is
proved is the whole fine-carrier operator reindexed through the already
constructed full-site equivalence.  The hRpoly endpoint fixes the bare mass
to zero internally.  This file is not compiler evidence and is not imported
by the tracked tree.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u

/-! ## Exact algebra of the square carrier reindexing -/

theorem scratch_finitePiLpTypedKernelReindex_add
    {ι ι' : Type u} {g : Type*}
    [Fintype ι] [Fintype ι']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (e : ι ≃ ι')
    (A B : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    finitePiLpTypedKernelReindex e e (A + B) =
      finitePiLpTypedKernelReindex e e A +
        finitePiLpTypedKernelReindex e e B := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [finitePiLpTypedKernelReindex]

theorem scratch_finitePiLpTypedKernelReindex_fintype_sum
    {ι ι' : Type u} {α : Type*} {g : Type*}
    [Fintype ι] [Fintype ι'] [Fintype α]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (e : ι ≃ ι')
    (A : α → FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    finitePiLpTypedKernelReindex e e (∑ j, A j) =
      ∑ j, finitePiLpTypedKernelReindex e e (A j) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [finitePiLpTypedKernelReindex]

/-! ## One generated separated-scale source chain -/

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The unique source tower used by the separated regional endpoint. -/
noncomputable def scratch_cmp89SourceSeparatedPrefixTower
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :=
  scratch_cmp85SourceGeneratedPrefixTower (d := 4) (M := L)
    (N := 2 * (K * Q)) (Nc := Nc) (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    spacing epsilon background budget.toRadiusChain fineSmall

/-- Every retained spacing is exactly the printed RG spacing
`L^j * spacing`; `K` does not occur. -/
theorem scratch_cmp89SourceSeparatedPrefixTower_terminalSpacing
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (r : Fin (depth + 2)) :
    ((scratch_cmp89SourceSeparatedPrefixTower (spacing := spacing)
      (epsilon := epsilon) hL depth background budget fineSmall).towerAt r).terminalSpacing =
        (L : ℝ) ^ r.val * spacing := by
  exact (scratch_cmp89SourceSeparatedPrefixTower (spacing := spacing)
    (epsilon := epsilon) hL depth background budget fineSmall).towerAt_terminalSpacing r

/-- The regional large-block side is independent `K` times the final RG
spacing factor. -/
theorem scratch_cmp89SourceSeparatedLargeBlockSide_eq
    (L K depth : ℕ) :
    cmp99SourceSeparatedLargeBlockSide L K depth =
      K * L ^ (depth + 1) := rfl

/-! ## Fine and ambient forms of the exact finite source identity -/

/-- Literal final mass-zero prefix Green on the generated full active
carrier, before regional reindexing. -/
noncomputable def scratch_cmp89SourceSeparatedFinePrefixGreen
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :=
  scratch_cmp85SourceGeneratedPrefixGreen (d := 4) (M := L)
    (N := 2 * (K * Q)) (Nc := Nc) (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    hspacing ha 0 background budget.toRadiusChain fineSmall hsmall
    (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))

/-- Literal independently generated mass-zero base covariance. -/
noncomputable def scratch_cmp89SourceSeparatedFineBaseCovariance
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :=
  scratch_cmp85SourceGeneratedBaseCovariance (d := 4) (M := L)
    (N := 2 * (K * Q)) (Nc := Nc) (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    (Nat.succ_pos depth) hspacing ha 0 background budget.toRadiusChain
    fineSmall hsmall

/-- Literal mass-zero `j`-th source correction before regional reindexing. -/
noncomputable def scratch_cmp89SourceSeparatedFineGreenIncrement
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (j : ScratchCMP85PositiveCoarseStep (depth + 1)) :=
  scratch_cmp85SourceGeneratedGreenIncrement (d := 4) (M := L)
    (N := 2 * (K * Q)) (Nc := Nc) (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    hspacing ha 0 background budget.toRadiusChain fineSmall hsmall j

/-- Regional ambient final Green, obtained only by the canonical full-site
equivalence. -/
noncomputable def scratch_cmp89SourceSeparatedAmbientPrefixGreen
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :=
  finitePiLpTypedKernelReindex
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (scratch_cmp89SourceSeparatedFinePrefixGreen hL depth hspacing ha
      background budget fineSmall hsmall)

noncomputable def scratch_cmp89SourceSeparatedAmbientBaseCovariance
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :=
  finitePiLpTypedKernelReindex
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (scratch_cmp89SourceSeparatedFineBaseCovariance hL depth hspacing ha
      background budget fineSmall hsmall)

noncomputable def scratch_cmp89SourceSeparatedAmbientGreenIncrement
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (j : ScratchCMP85PositiveCoarseStep (depth + 1)) :=
  finitePiLpTypedKernelReindex
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (scratch_cmp89SourceSeparatedFineGreenIncrement hL depth hspacing ha
      background budget fineSmall hsmall j)

/-- CMP89 (2.34) on the separated ambient carrier.  The equality is the
image of the internally proved CMP85 (2.43); no regional equality or Green
family is accepted from the caller. -/
theorem scratch_cmp89SourceSeparatedAmbientGreenScaleSum_eq234
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
    scratch_cmp89SourceSeparatedAmbientPrefixGreen hL depth hspacing ha
        background budget fineSmall hsmall =
      scratch_cmp89SourceSeparatedAmbientBaseCovariance hL depth hspacing ha
          background budget fineSmall hsmall +
        ∑ j : ScratchCMP85PositiveCoarseStep (depth + 1),
          scratch_cmp89SourceSeparatedAmbientGreenIncrement hL depth
            hspacing ha background budget fineSmall hsmall j := by
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  have hfine := scratch_cmp85SourceGeneratedGreenScaleSum_eq243
    (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
    (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    (Nat.succ_pos depth) hspacing ha 0 background budget.toRadiusChain
    fineSmall hsmall
  have htransport := congrArg (finitePiLpTypedKernelReindex e e) hfine
  rw [scratch_finitePiLpTypedKernelReindex_add,
    scratch_finitePiLpTypedKernelReindex_fintype_sum] at htransport
  exact htransport

/-- CMP89 (2.34) with the printed coefficient and operator order visible in
the public conclusion.  The preceding theorem is a convenient technical
summation through the named increment; this theorem is the source-facing
endpoint and does not hide `a_j^2 * spacing_j^(-4)` in that abbreviation. -/
theorem scratch_cmp89SourceSeparatedAmbientGreenScaleSum_eq234_literal
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
    let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
    scratch_cmp89SourceSeparatedAmbientPrefixGreen hL depth hspacing ha
        background budget fineSmall hsmall =
      scratch_cmp89SourceSeparatedAmbientBaseCovariance hL depth hspacing ha
          background budget fineSmall hsmall +
        ∑ j : ScratchCMP85PositiveCoarseStep (depth + 1),
          let T := scratch_cmp85SourceGeneratedPrefixTower
            (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
            (by norm_num) hL
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1) spacing epsilon background budget.toRadiusChain
            fineSmall
          let r := j.currentPrefix
          let Qj := (T.towerAt r.1).Qprime
          let Qjdag := (T.towerAt r.1).weightedAdjoint
          let Gj := scratch_cmp85SourceGeneratedPrefixGreen
            (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
            (by norm_num) hL
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1) hspacing ha 0 background budget.toRadiusChain
            fineSmall hsmall r
          let Cj := scratch_cmp85SourceGeneratedCoarseCovariance
            (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
            (by norm_num) hL
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1) hspacing ha 0 background budget.toRadiusChain
            fineSmall hsmall j
          finitePiLpTypedKernelReindex e e
            (((cmp99SourceMassParameter a (L : ℝ) (r.1.val - 1)) ^ 2 *
                (T.towerAt r.1).terminalSpacing⁻¹ ^ 4) •
              Gj.comp (Qjdag.comp (Cj.comp (Qj.comp Gj)))) := by
  dsimp only
  simpa only [scratch_cmp89SourceSeparatedAmbientGreenIncrement,
    scratch_cmp89SourceSeparatedFineGreenIncrement,
    scratch_cmp85SourceGeneratedGreenIncrement,
    scratch_cmp85SourcePrefixA] using
      scratch_cmp89SourceSeparatedAmbientGreenScaleSum_eq234
        hL depth hspacing ha background budget fineSmall hsmall

end

end YangMills.RG
