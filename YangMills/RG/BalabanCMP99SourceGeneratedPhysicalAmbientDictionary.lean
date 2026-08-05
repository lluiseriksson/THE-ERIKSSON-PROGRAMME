/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalLargeBlockCutoff
import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann
import YangMills.RG.FinitePiLpTypedKernelReindex

/-!
# PRE-VALIDATION: generated physical precision on the regional ambient carrier

The source of this module is present, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

CMP99 (3.87)--(3.90) needs one ambient precision whose supported
compressions generate all local Dirichlet Green operators.  The generated
Section-C precision is initially indexed by the active sites of a recursively
lifted region.  This file chooses the literal full coarse region, proves that
all its lifts remain full, and reindexes the generated precision onto the
ordinary ambient `FinBox` carrier by an explicit finite equivalence.

The same equivalence transports the source large-block cutoff and its
commutator estimate exactly.  No regional Green is composed here, and no
defect contraction or terminal-field producer is claimed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u

/-- Complete-block lifting preserves the full region at every depth. -/
theorem cmp99IteratedLiftActiveRegion_full_sites_eq_univ
    {d M N : ℕ} [NeZero M] [NeZero N] (k : ℕ) :
    (cmp99IteratedLiftActiveRegion (M := M)
      (ActiveGaugeRegion.mk (Finset.univ : Finset (FinBox d N))) k).sites =
        Finset.univ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [cmp99IteratedLiftActiveRegion_succ]
      apply Finset.eq_univ_iff_forall.mpr
      intro x
      rw [mem_cmp99LiftActiveRegion_sites_iff, ih]
      exact Finset.mem_univ _

/-- Reindexing both legs of a square operator commutes exactly with taking a
scalar commutator. -/
theorem finitePiLpTypedKernelReindex_scalarCommutator
    {ι ι' : Type u} {g : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (e : ι ≃ ι') (h : ι → ℝ)
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    finitePiLpTypedKernelReindex e e (finitePiLpScalarCommutator h A) =
      finitePiLpScalarCommutator (fun x => h (e.symm x))
        (finitePiLpTypedKernelReindex e e A) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [finitePiLpTypedKernelReindex, finitePiLpScalarCommutator,
    ContinuousLinearMap.comp_apply, finitePiLpScalarMultiplier_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- Square isometric reindexing preserves a coercivity constant exactly. -/
theorem isCoerciveCLM_finitePiLpTypedKernelReindex
    {ι ι' : Type u} {g : Type*}
    [Fintype ι] [Fintype ι']
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    (e : ι ≃ ι')
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    {c : ℝ} (hA : IsCoerciveCLM A c) :
    IsCoerciveCLM (finitePiLpTypedKernelReindex e e A) c := by
  intro phi
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℝ g e
  have h := hA (U.symm phi)
  calc
    c * ‖phi‖ ^ 2 = c * ‖U.symm phi‖ ^ 2 := by
      rw [U.symm.norm_map]
    _ ≤ inner ℝ (U.symm phi) (A (U.symm phi)) := h
    _ = inner ℝ phi
        (finitePiLpTypedKernelReindex e e A phi) := by
      rw [← U.inner_map_map]
      simp [U, finitePiLpTypedKernelReindex,
        LinearIsometryEquiv.piLpCongrLeft_symm]

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

/-- The full coarse region whose generated lift supplies the single ambient
precision used by all source large-block Dirichlet regions. -/
def cmp99SourceGeneratedPhysicalFullCoarseRegion (M Q : ℕ) :
    ActiveGaugeRegion 4 (2 * (M * Q)) :=
  ActiveGaugeRegion.mk Finset.univ

/-- Explicit equivalence between the full generated active carrier and the
factored ambient carrier of the source large-block partition. -/
noncomputable def cmp99SourceGeneratedPhysicalFullSiteEquiv
    (M Q depth : ℕ) [NeZero M] [NeZero Q] :
    ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M)
          (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) (depth + 1)) ≃
      FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) :=
  let hsize := cmp99RegionalLatticeSize_sourceLargeBlockCarrier M Q depth
  { toFun := fun x => hsize ▸ x.1
    invFun := fun x =>
      ⟨hsize.symm ▸ x, by
        rw [cmp99SourceGeneratedPhysicalFullCoarseRegion,
          cmp99IteratedLiftActiveRegion_full_sites_eq_univ]
        exact Finset.mem_univ _⟩
    left_inv := fun x => Subtype.ext
      (cast_cancel_of_opposite_equalities hsize.symm hsize x.1)
    right_inv := fun x =>
      cast_cancel_of_opposite_equalities hsize hsize.symm x }

/-- The full-site equivalence preserves the literal periodic distance. -/
theorem finBoxDist_cmp99SourceGeneratedPhysicalFullSiteEquiv_symm
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x y : FinBox 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))) :
    finBoxDist
        ((cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth).symm x).1
        ((cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth).symm y).1 =
      finBoxDist x y := by
  let hsize := cmp99RegionalLatticeSize_sourceLargeBlockCarrier M Q depth
  change finBoxDist (hsize.symm ▸ x) (hsize.symm ▸ y) = finBoxDist x y
  exact finBoxDist_cast_size hsize.symm x y

/-- The literal generated physical precision, isometrically realized on the
one ambient fine carrier used by the regional Green construction. -/
noncomputable def cmp99SourceGeneratedPhysicalAmbientPrecision
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) :=
  let Omega := cmp99SourceGeneratedPhysicalFullCoarseRegion M Q
  let e := cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth
  finitePiLpTypedKernelReindex e e
    (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM Omega depth
      spacing epsilon background budget fineSmall)

/-- The ambient realization retains the exact source-generated coercivity
constant. -/
theorem isCoerciveCLM_cmp99SourceGeneratedPhysicalAmbientPrecision
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    IsCoerciveCLM
      (cmp99SourceGeneratedPhysicalAmbientPrecision hM depth background
        budget fineSmall)
      (cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon) := by
  exact isCoerciveCLM_finitePiLpTypedKernelReindex
    (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth)
    (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth spacing epsilon
      background budget fineSmall)
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth hspacing
      background budget fineSmall hsmall)

/-- Pulling the active cutoff through the full-site equivalence gives the
literal source regional cutoff, with no comparison constant. -/
theorem cmp99SourceGeneratedPhysicalLargeBlockCutoff_fullSiteEquiv_symm
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))) :
    cmp99SourceGeneratedPhysicalLargeBlockCutoff P
        (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth cell
        ((cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth).symm x) =
      (cmp99SourceRegionalLargeBlockSquarePartition
        (M := M) (Q := Q) (depth := depth) P).value cell x := by
  let hsize := cmp99RegionalLatticeSize_sourceLargeBlockCarrier M Q depth
  change
    (cmp99SourceRegionalLargeBlockSquarePartition
      (M := M) (Q := Q) (depth := depth) P).value cell
        (hsize ▸ (hsize.symm ▸ x)) = _
  rw [cast_cancel_of_opposite_equalities hsize hsize.symm x]

/-- Exact dictionary: the regional square commutator of the one ambient
precision is the isometric reindexing of the already bounded active
commutator. -/
theorem cmp99SourceRegionalLargeBlockPrecisionCommutator_eq_reindex
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (depth : ℕ) {spacing epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q) :
    cmp99RegionalSquarePrecisionCommutator
        (M := cmp99SourceRegionalLargeBlockSide M depth)
        (Q := Q) (g := SUNLieCoord Nc)
        (cmp99SourceRegionalLargeBlockSquarePartition
          (M := M) (Q := Q) (depth := depth) P) cell
        (cmp99SourceGeneratedPhysicalAmbientPrecision hM depth background
          budget fineSmall) =
      finitePiLpTypedKernelReindex
        (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth)
        (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth)
        (finitePiLpScalarCommutator
          (cmp99SourceGeneratedPhysicalLargeBlockCutoff P
            (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth cell)
          (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
            (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth
            spacing epsilon background budget fineSmall)) := by
  rw [finitePiLpTypedKernelReindex_scalarCommutator]
  change finitePiLpScalarCommutator
      (fun x =>
        (cmp99SourceRegionalLargeBlockSquarePartition
          (M := M) (Q := Q) (depth := depth) P).value cell x)
      (cmp99SourceGeneratedPhysicalAmbientPrecision hM depth background
        budget fineSmall) =
    finitePiLpScalarCommutator
      (fun x => cmp99SourceGeneratedPhysicalLargeBlockCutoff P
        (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth cell
        ((cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth).symm x))
      (cmp99SourceGeneratedPhysicalAmbientPrecision hM depth background
        budget fineSmall)
  apply congrArg (fun h => finitePiLpScalarCommutator h
    (cmp99SourceGeneratedPhysicalAmbientPrecision hM depth background
      budget fineSmall))
  funext x
  exact (cmp99SourceGeneratedPhysicalLargeBlockCutoff_fullSiteEquiv_symm
    P depth cell x).symm

/-- The physical commutator estimate is now stated on the literal ambient
carrier consumed by the regional Dirichlet Green algebra. -/
theorem
    cmp99SourceRegionalLargeBlockPrecisionCommutator_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (depth : ℕ) {spacing epsilon rate : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q) :
    FinitePiLpTypedExponentialKernelBound
      (cmp99RegionalSquarePrecisionCommutator
        (M := cmp99SourceRegionalLargeBlockSide M depth)
        (Q := Q) (g := SUNLieCoord Nc)
        (cmp99SourceRegionalLargeBlockSquarePartition
          (M := M) (Q := Q) (depth := depth) P) cell
        (cmp99SourceGeneratedPhysicalAmbientPrecision hM depth background
          budget fineSmall))
      (fun target source : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) =>
        finBoxDist target source)
      (cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
        P M depth spacing epsilon rate) rate := by
  rw [cmp99SourceRegionalLargeBlockPrecisionCommutator_eq_reindex]
  let e := cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth
  have hactive :=
    cmp99SourceGeneratedPhysicalPrecision_largeBlockCutoff_exponentialKernelBound
      P hM (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth
      hspacing hrate background budget fineSmall cell
  have hreindexed := finitePiLpTypedExponentialKernelBound_reindex e e _ _
    hactive
  have hdist :
      (fun target source : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) =>
        finBoxDist (e.symm target).1 (e.symm source).1) =
      (fun target source : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) =>
        finBoxDist target source) := by
    funext target source
    exact finBoxDist_cmp99SourceGeneratedPhysicalFullSiteEquiv_symm
      M Q depth target source
  rw [hdist] at hreindexed
  exact hreindexed

end

end YangMills.RG
