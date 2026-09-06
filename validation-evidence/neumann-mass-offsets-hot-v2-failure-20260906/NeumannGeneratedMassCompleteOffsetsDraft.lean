import YangMills.RG.NeumannGeneratedCompleteFibre
import YangMills.RG.NeumannGeneratedAverageFieldAction
import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel

/-!
PRE-VALIDATION: source present; .olean not materialized and compiler verdict
pending. R2d.2b finite field-action endpoint, not a regional inverse or B0.

The coarse owner of an actual fine output is constructed from recursive
lift membership. Dependent terminal-owner equality is transported by its
sealed iff, not by a cast of terminal-site types. The source-weighted mass
keeps weight^depth and the counting-adjoint mass keeps weight^(2*depth).
Integer image transport is pointwise on arbitrary functions; it neither
asserts a global l2 extension nor interchanges an infinite series.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- An actual fine output supplies its active coarse owner internally. -/
def neumannGeneratedActiveCoarseOwner
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)) :
    ActiveGaugeRegion.Site Omega :=
  ⟨cmp99GeneratedTerminalBlockSite M N depth target.1,
    (neumann_mem_iteratedLift_iff_terminalOwner Omega depth target.1).mp target.2⟩

/-- The actual dependent-owner sum is a complete offset sum. There is no
additional fibre-cardinality coefficient and no supplied fibre bijection. -/
theorem sum_neumannGeneratedTerminalOwner_eq_completeOffsets
    {V : Type*} [AddCommMonoid V]
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
    (f : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth) → V) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    (∑ source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth),
      if regions.terminalSiteOfFine target = regions.terminalSiteOfFine source
      then f source else 0) =
      ∑ r : FinBox d (M ^ depth),
        f (neumannGeneratedCompleteFibreOffsetEquiv Omega depth
          (neumannGeneratedActiveCoarseOwner Omega depth target) r).1 := by
  classical
  dsimp only
  calc
    _ = ∑ source : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth),
        if cmp99GeneratedTerminalBlockSite M N depth source.1 =
            (neumannGeneratedActiveCoarseOwner Omega depth target).1
        then f source else 0 := by
      apply Finset.sum_congr rfl
      intro source _
      apply if_congr _ rfl rfl
      exact (cmp99SourceIteratedLift_terminalOwner_eq_iff_generatedTerminalBlockSite_eq
        (M := M) Omega depth target source).trans eq_comm
    _ = _ := sum_neumannGeneratedOwnerIndicator_eq_offsets Omega depth
      (neumannGeneratedActiveCoarseOwner Omega depth target) f

/-- Literal source-weighted generated mass on a complete field, weight once. -/
theorem neumannGeneratedWeightedMass_apply_eq_completeOffsets
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
    ∀ (f : ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth) (SUNLieCoord Nc))
      (target : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth)),
      ((regions.flatExplicitWeightedAdjoint (Nc := Nc)).comp
        (regions.flatExplicitQprime (Nc := Nc))) f target =
        (cmp99SourceBlockAverageWeight M d) ^ depth •
          (∑ r : FinBox d (M ^ depth),
            f (neumannGeneratedCompleteFibreOffsetEquiv Omega depth
              (neumannGeneratedActiveCoarseOwner Omega depth target) r).1) := by
  dsimp only
  intro f target
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
  rw [regions.flatExplicitWeightedMass_apply_eq_terminalFibreSum]
  exact congrArg (fun z : SUNLieCoord Nc =>
    (cmp99SourceBlockAverageWeight M d) ^ depth • z)
    (sum_neumannGeneratedTerminalOwner_eq_completeOffsets Omega depth target
      (fun source => f source))

/-- Literal counting-adjoint mass, retaining the square of the averaging
coefficient. This is not identified with the source-weighted adjoint. -/
theorem neumannGeneratedCountingMass_apply_eq_completeOffsets
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
    ∀ (f : ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth) (SUNLieCoord Nc))
      (target : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth)),
      ((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
        (regions.flatExplicitQprime (Nc := Nc))) f target =
        (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) •
          (∑ r : FinBox d (M ^ depth),
            f (neumannGeneratedCompleteFibreOffsetEquiv Omega depth
              (neumannGeneratedActiveCoarseOwner Omega depth target) r).1) := by
  dsimp only
  intro f target
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
  rw [regions.flatExplicitCountingMass_apply_eq_terminalFibreSum]
  exact congrArg (fun z : SUNLieCoord Nc =>
    (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) • z)
    (sum_neumannGeneratedTerminalOwner_eq_completeOffsets Omega depth target
      (fun source => f source))

/-- Specialize the same actual owner sum to the literal integer coordinates.
No global square-summability assumption is made about the integer field. -/
theorem sum_neumannGeneratedTerminalOwner_integerField_eq_completeOffsets
    {V : Type*} [AddCommMonoid V]
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
    (F : (Fin d → ℤ) → V) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    (∑ source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth),
      if regions.terminalSiteOfFine target = regions.terminalSiteOfFine source
      then F (neumannFiniteSiteIntegerCoordinates source.1) else 0) =
      ∑ r : FinBox d (M ^ depth), F (neumannIntegerFineBlockPoint
        (neumannFiniteSiteIntegerCoordinates
          (neumannGeneratedActiveCoarseOwner Omega depth target).1) r) := by
  dsimp only
  rw [sum_neumannGeneratedTerminalOwner_eq_completeOffsets]
  apply Finset.sum_congr rfl
  intro r _
  exact congrArg F
    (neumannGeneratedCompleteFibreOffsetEquiv_integerCoordinates Omega depth
      (neumannGeneratedActiveCoarseOwner Omega depth target) r)

/-- A common printed image transports that SAME finite owner sum. Translation
and parity are shared across its complete fibre; no B^d factor is added. -/
theorem sum_neumannGeneratedTerminalOwner_commonImage_eq_completeOffsets
    {V : Type*} [AddCommMonoid V]
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
    (m k : Fin d → ℤ) (branch : CMP89NeumannReflectionBranch d)
    (F : (Fin d → ℤ) → V) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    (∑ source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth),
      if regions.terminalSiteOfFine target = regions.terminalSiteOfFine source
      then F (cmp89NeumannReflectionImage
        (fun mu => ((M ^ depth : ℕ) : ℤ) * m mu)
        (neumannFiniteSiteIntegerCoordinates source.1) k branch) else 0) =
      ∑ r : FinBox d (M ^ depth), F (neumannIntegerFineBlockPoint
        (cmp89NeumannReflectionImage m
          (neumannFiniteSiteIntegerCoordinates
            (neumannGeneratedActiveCoarseOwner Omega depth target).1) k branch) r) := by
  dsimp only
  rw [sum_neumannGeneratedTerminalOwner_integerField_eq_completeOffsets]
  exact sum_neumannIntegerImage_fineBlockPoint m
    (neumannFiniteSiteIntegerCoordinates
      (neumannGeneratedActiveCoarseOwner Omega depth target).1) k branch F

#print axioms neumannGeneratedActiveCoarseOwner
#print axioms sum_neumannGeneratedTerminalOwner_eq_completeOffsets
#print axioms neumannGeneratedWeightedMass_apply_eq_completeOffsets
#print axioms neumannGeneratedCountingMass_apply_eq_completeOffsets
#print axioms sum_neumannGeneratedTerminalOwner_integerField_eq_completeOffsets
#print axioms sum_neumannGeneratedTerminalOwner_commonImage_eq_completeOffsets

end
end YangMills.RG
