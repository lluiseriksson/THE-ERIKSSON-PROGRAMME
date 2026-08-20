import YangMills.RG.BalabanCMP85Eq243PhysicalGreenScaleSum
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary
import YangMills.RG.FinitePiLpTypedKernelReindexAlgebra
/-!
carrier and scale dictionary from CMP85 (2.43) to the regional CMP89 (2.34) presentation.

The RG ratio `L` and the independent regional large-block factor `K` remain different parameters. The prefix Green chain is generated on the full coarse carrier `2*(K*Q)` with `M := L`; only after the source identity is proved is the whole fine-carrier operator reindexed through the already constructed full-site equivalence. The hRpoly endpoint fixes the bare mass to zero internally.

PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u

/-! ## Exact algebra of the square carrier reindexing -/

theorem finitePiLpTypedKernelReindex_add
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

theorem finitePiLpTypedKernelReindex_fintype_sum
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
noncomputable def cmp89SourceSeparatedPrefixTower
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    CMP99SourceRetainedPhysicalTower (matrixSUNAdjointModel Nc)
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1))
      L spacing background (depth + 1) :=
  cmp85SourceGeneratedPrefixTower (d := 4) (M := L)
    (N := 2 * (K * Q)) (Nc := Nc) (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    spacing epsilon background budget.toRadiusChain fineSmall

/-- Every retained spacing is exactly the printed RG spacing
`L^j * spacing`; `K` does not occur. -/
theorem cmp89SourceSeparatedPrefixTower_terminalSpacing
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (r : Fin (depth + 2)) :
    ((cmp89SourceSeparatedPrefixTower (spacing := spacing)
      (epsilon := epsilon) hL depth background budget fineSmall).towerAt r).terminalSpacing =
        (L : ℝ) ^ r.val * spacing := by
  exact (cmp89SourceSeparatedPrefixTower (spacing := spacing)
    (epsilon := epsilon) hL depth background budget fineSmall).towerAt_terminalSpacing r

/-- The regional large-block side is independent `K` times the final RG
spacing factor. -/
theorem cmp89SourceSeparatedLargeBlockSide_eq
    (L K depth : ℕ) :
    cmp99SourceSeparatedLargeBlockSide L K depth =
      K * L ^ (depth + 1) := rfl

/-! ## Fine and ambient forms of the exact finite source identity -/

/-- Literal final mass-zero prefix Green on the generated full active
carrier, before regional reindexing. -/
noncomputable def cmp89SourceSeparatedFinePrefixGreen
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
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1))
        (SUNLieCoord Nc) :=
  cmp85SourceGeneratedPrefixGreen (d := 4) (M := L)
    (N := 2 * (K * Q)) (Nc := Nc) (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    hspacing ha 0 background budget.toRadiusChain fineSmall hsmall
    (cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))

/-- Literal independently generated mass-zero base covariance. -/
noncomputable def cmp89SourceSeparatedFineBaseCovariance
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
  cmp85SourceGeneratedBaseCovariance (d := 4) (M := L)
    (N := 2 * (K * Q)) (Nc := Nc) (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    (Nat.succ_pos depth) hspacing ha 0 background budget.toRadiusChain
    fineSmall hsmall

/-- Literal mass-zero `j`-th source correction before regional reindexing. -/
noncomputable def cmp89SourceSeparatedFineGreenIncrement
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
    (j : CMP85PositiveCoarseStep (depth + 1)) :=
  cmp85SourceGeneratedGreenIncrement (d := 4) (M := L)
    (N := 2 * (K * Q)) (Nc := Nc) (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    hspacing ha 0 background budget.toRadiusChain fineSmall hsmall j

/-- Regional ambient final Green, obtained only by the canonical full-site
equivalence. -/
noncomputable def cmp89SourceSeparatedAmbientPrefixGreen
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
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  finitePiLpTypedKernelReindex
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp89SourceSeparatedFinePrefixGreen hL depth hspacing ha
      background budget fineSmall hsmall)

noncomputable def cmp89SourceSeparatedAmbientBaseCovariance
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
    (cmp89SourceSeparatedFineBaseCovariance hL depth hspacing ha
      background budget fineSmall hsmall)

noncomputable def cmp89SourceSeparatedAmbientGreenIncrement
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
    (j : CMP85PositiveCoarseStep (depth + 1)) :=
  finitePiLpTypedKernelReindex
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp89SourceSeparatedFineGreenIncrement hL depth hspacing ha
      background budget fineSmall hsmall j)

/-- CMP89 (2.34) on the separated ambient carrier.  The equality is the
image of the internally proved CMP85 (2.43); no regional equality or Green
family is accepted from the caller. -/
theorem cmp89SourceSeparatedAmbientGreenScaleSum_eq234
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
    cmp89SourceSeparatedAmbientPrefixGreen hL depth hspacing ha
        background budget fineSmall hsmall =
      cmp89SourceSeparatedAmbientBaseCovariance hL depth hspacing ha
          background budget fineSmall hsmall +
        ∑ j : CMP85PositiveCoarseStep (depth + 1),
          cmp89SourceSeparatedAmbientGreenIncrement hL depth
            hspacing ha background budget fineSmall hsmall j := by
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  have hfine := cmp85SourceGeneratedGreenScaleSum_eq243
    (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
    (by norm_num) hL
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
    (Nat.succ_pos depth) hspacing ha 0 background budget.toRadiusChain
    fineSmall hsmall
  have hfineNamed :
      cmp89SourceSeparatedFinePrefixGreen hL depth hspacing ha
          background budget fineSmall hsmall =
        cmp89SourceSeparatedFineBaseCovariance hL depth hspacing ha
            background budget fineSmall hsmall +
          ∑ j : CMP85PositiveCoarseStep (depth + 1),
            cmp89SourceSeparatedFineGreenIncrement hL depth
              hspacing ha background budget fineSmall hsmall j := by
    calc
      cmp89SourceSeparatedFinePrefixGreen hL depth hspacing ha
          background budget fineSmall hsmall =
        cmp85SourceGeneratedPrefixGreen
          (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
          (by norm_num) hL
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1) hspacing ha 0 background budget.toRadiusChain
          fineSmall hsmall
          (cmp85LastPositivePrefix (depth + 1)
            (Nat.succ_pos depth)) := by rfl
      _ = _ := hfine
      _ = cmp89SourceSeparatedFineBaseCovariance hL depth hspacing ha
            background budget fineSmall hsmall +
          ∑ j : CMP85PositiveCoarseStep (depth + 1),
            cmp89SourceSeparatedFineGreenIncrement hL depth
              hspacing ha background budget fineSmall hsmall j := by
        apply congrArg₂ (fun A B => A + B)
        · rfl
        · apply Finset.sum_congr rfl
          intro j hj
          rfl
  have htransport := congrArg (finitePiLpTypedKernelReindex e e) hfineNamed
  rw [finitePiLpTypedKernelReindex_add,
    finitePiLpTypedKernelReindex_fintype_sum] at htransport
  unfold cmp89SourceSeparatedAmbientPrefixGreen
    cmp89SourceSeparatedAmbientBaseCovariance
    cmp89SourceSeparatedAmbientGreenIncrement
  exact htransport

/-- One transported CMP85 increment with the printed CMP89 coefficient and
operator order exposed before taking the finite sum.  Keeping this conversion
pointwise prevents the elaborator from reducing the entire transported sum. -/
theorem cmp89SourceSeparatedAmbientGreenIncrement_eq_literal
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
    (j : CMP85PositiveCoarseStep (depth + 1)) :
    let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
    let T := cmp85SourceGeneratedPrefixTower
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
    let r := j.currentPrefix
    let Qj := (T.towerAt r.1).Qprime
    let Qjdag := (T.towerAt r.1).weightedAdjoint
    let Gj := cmp85SourceGeneratedPrefixGreen
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1) hspacing ha 0 background budget.toRadiusChain
      fineSmall hsmall r
    let Cj := cmp85SourceGeneratedCoarseCovariance
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1) hspacing ha 0 background budget.toRadiusChain
      fineSmall hsmall j
    cmp89SourceSeparatedAmbientGreenIncrement hL depth hspacing ha
        background budget fineSmall hsmall j =
      finitePiLpTypedKernelReindex e e
        (((cmp99SourceMassParameter a (L : ℝ) (r.1.val - 1)) ^ 2 *
            (T.towerAt r.1).terminalSpacing⁻¹ ^ 4) •
          Gj.comp (Qjdag.comp (Cj.comp (Qj.comp Gj)))) := by
  dsimp only
  unfold cmp89SourceSeparatedAmbientGreenIncrement
  apply congrArg
  simp only [cmp89SourceSeparatedFineGreenIncrement,
    cmp85SourceGeneratedGreenIncrement,
    cmp85SourcePrefixA]

/-- CMP89 (2.34) with the printed coefficient and operator order visible in
the public conclusion.  The preceding theorem is a convenient technical
summation through the named increment; this theorem is the source-facing
endpoint and does not hide `a_j^2 * spacing_j^(-4)` in that abbreviation. -/
theorem cmp89SourceSeparatedAmbientGreenScaleSum_eq234_literal
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
    cmp89SourceSeparatedAmbientPrefixGreen hL depth hspacing ha
        background budget fineSmall hsmall =
      cmp89SourceSeparatedAmbientBaseCovariance hL depth hspacing ha
          background budget fineSmall hsmall +
        ∑ j : CMP85PositiveCoarseStep (depth + 1),
          let T := cmp85SourceGeneratedPrefixTower
            (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
            (by norm_num) hL
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1) spacing epsilon background budget.toRadiusChain
            fineSmall
          let r := j.currentPrefix
          let Qj := (T.towerAt r.1).Qprime
          let Qjdag := (T.towerAt r.1).weightedAdjoint
          let Gj := cmp85SourceGeneratedPrefixGreen
            (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
            (by norm_num) hL
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1) hspacing ha 0 background budget.toRadiusChain
            fineSmall hsmall r
          let Cj := cmp85SourceGeneratedCoarseCovariance
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
  rw [cmp89SourceSeparatedAmbientGreenScaleSum_eq234
    hL depth hspacing ha background budget fineSmall hsmall]
  apply congrArg (fun z =>
    cmp89SourceSeparatedAmbientBaseCovariance hL depth hspacing ha
      background budget fineSmall hsmall + z)
  apply Finset.sum_congr rfl
  intro j hj
  exact cmp89SourceSeparatedAmbientGreenIncrement_eq_literal
    hL depth hspacing ha background budget fineSmall hsmall j

end

end YangMills.RG
