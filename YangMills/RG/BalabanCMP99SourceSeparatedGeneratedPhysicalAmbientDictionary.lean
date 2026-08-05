/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalLargeBlockCutoff

/-!
# PRE-VALIDATION: separated-scale generated physical ambient dictionary

The source below is present, but its `.olean` has not yet been materialized
and its results have not yet been verified by the Lean compiler.

This realizes the generated precision with RG ratio `L` on the literal
regional carrier whose large-block parameter is `K`.  The ambient operator,
its coercivity, the cutoff and the commutator are all transported through one
explicit equivalence.  The final commutator identity is proved; no equality
between two independently supplied precisions is accepted from the caller.

No regional Green or defect operator is constructed here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Full coarse region on the separated `2 * (K*Q)` carrier. -/
def cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion (K Q : ℕ) :
    ActiveGaugeRegion 4 (2 * (K * Q)) :=
  ActiveGaugeRegion.mk Finset.univ

private theorem separated_dependent_cast_cancel_of_opposite_equalities
    {I : Sort*} {F : I → Sort*} {i j : I}
    (hij : i = j) (hji : j = i) (x : F j) :
    hij ▸ (hji ▸ x) = x := by
  cases hij
  rfl

/-- Explicit equivalence between the full generated active carrier with RG
ratio `L` and the ambient separated large-block carrier. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1)) ≃
      FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  let hsize :=
    cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  { toFun := fun x => hsize ▸ x.1
    invFun := fun x =>
      ⟨hsize.symm ▸ x, by
        rw [cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion,
          cmp99IteratedLiftActiveRegion_full_sites_eq_univ]
        exact Finset.mem_univ _⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact separated_dependent_cast_cancel_of_opposite_equalities
        hsize.symm hsize x.1
    right_inv := by
      intro x
      exact separated_dependent_cast_cancel_of_opposite_equalities
        hsize hsize.symm x }

/-- The separated full-site equivalence preserves periodic distance. -/
theorem finBoxDist_cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_symm
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    finBoxDist
        ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth).symm x).1
        ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth).symm y).1 =
      finBoxDist x y := by
  let hsize :=
    cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  change finBoxDist (hsize.symm ▸ x) (hsize.symm ▸ y) = finBoxDist x y
  exact finBoxDist_cast_size hsize.symm x y

/-- Generated physical precision with ratio `L`, realized on the separated
ambient carrier. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  finitePiLpTypedKernelReindex e e
    (cmp99SourceGeneratedPhysicalPrecision
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL Omega depth
      spacing epsilon background budget fineSmall)

/-- The separated ambient realization retains the generated coercivity with
its dependence on `L` and no dependence on `K`. -/
theorem isCoerciveCLM_cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :
    IsCoerciveCLM
      (cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        (spacing := spacing) (epsilon := epsilon)
        hL depth background budget fineSmall)
      (cmp99SourceGeneratedCoercivity 4 L (depth + 1)
        spacing epsilon) := by
  exact isCoerciveCLM_finitePiLpTypedKernelReindex
    (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
    (cmp99SourceGeneratedPhysicalPrecision
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      depth spacing epsilon background budget fineSmall)
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      depth hspacing background budget fineSmall hsmall)

/-- Pulling the separated active cutoff through the full-site equivalence is
exactly the literal separated regional cutoff. -/
theorem
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff_fullSiteEquiv_symm
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff P
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        depth cell
        ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth).symm x) =
      (cmp99SourceSeparatedLargeBlockSquarePartition
        (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x := by
  let hsize :=
    cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  change
    (cmp99SourceSeparatedLargeBlockSquarePartition
      (L := L) (K := K) (Q := Q) (depth := depth) P).value cell
        (hsize ▸ (hsize.symm ▸ x)) = _
  rw [separated_dependent_cast_cancel_of_opposite_equalities
    hsize hsize.symm x]

/-- Exact separated ambient/regional commutator dictionary. -/
theorem cmp99SourceSeparatedRegionalLargeBlockPrecisionCommutator_eq_reindex
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L)
    (depth : ℕ) {spacing epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q) :
    cmp99RegionalSquarePrecisionCommutator
        (M := cmp99SourceSeparatedLargeBlockSide L K depth)
        (Q := Q) (g := SUNLieCoord Nc)
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P) cell
        (cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          (spacing := spacing) (epsilon := epsilon)
          hL depth background budget fineSmall) =
      finitePiLpTypedKernelReindex
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
        (finitePiLpScalarCommutator
          (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff P
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            depth cell)
          (cmp99SourceGeneratedPhysicalPrecision
            (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
            (by norm_num) hL
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            depth spacing epsilon background budget fineSmall)) := by
  rw [finitePiLpTypedKernelReindex_scalarCommutator]
  change finitePiLpScalarCommutator
      (fun x =>
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x)
      (cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        (spacing := spacing) (epsilon := epsilon)
        hL depth background budget fineSmall) =
    finitePiLpScalarCommutator
      (fun x => cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff P
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        depth cell
        ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth).symm x))
      (cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        (spacing := spacing) (epsilon := epsilon)
        hL depth background budget fineSmall)
  apply congrArg (fun h => finitePiLpScalarCommutator h
    (cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      (spacing := spacing) (epsilon := epsilon)
      hL depth background budget fineSmall))
  funext x
  exact
    (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoff_fullSiteEquiv_symm
      P depth cell x).symm

/-- The separated physical commutator estimate on the regional ambient
carrier. -/
theorem
    cmp99SourceSeparatedRegionalLargeBlockPrecisionCommutator_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L)
    (depth : ℕ) {spacing epsilon rate : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q) :
    FinitePiLpTypedExponentialKernelBound
      (cmp99RegionalSquarePrecisionCommutator
        (M := cmp99SourceSeparatedLargeBlockSide L K depth)
        (Q := Q) (g := SUNLieCoord Nc)
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P) cell
        (cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          (spacing := spacing) (epsilon := epsilon)
          hL depth background budget fineSmall))
      (fun target source : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) =>
        finBoxDist target source)
      (cmp99SourceSeparatedGeneratedPhysicalLargeBlockCutoffBudget
        P L K depth spacing epsilon rate) rate := by
  rw [cmp99SourceSeparatedRegionalLargeBlockPrecisionCommutator_eq_reindex]
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  have hactive :=
    cmp99SourceSeparatedGeneratedPhysicalPrecision_largeBlockCutoff_exponentialKernelBound
      (L := L) (K := K) (Q := Q) (Nc := Nc) P hL
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      depth hspacing hrate background budget fineSmall cell
  have hreindexed :=
    finitePiLpTypedExponentialKernelBound_reindex e e _ _ hactive
  have hdist :
      (fun target source : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) =>
        finBoxDist (e.symm target).1 (e.symm source).1) =
      (fun target source : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) =>
        finBoxDist target source) := by
    funext target source
    exact finBoxDist_cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_symm
      L K Q depth target source
  rw [hdist] at hreindexed
  exact hreindexed

end

end YangMills.RG
