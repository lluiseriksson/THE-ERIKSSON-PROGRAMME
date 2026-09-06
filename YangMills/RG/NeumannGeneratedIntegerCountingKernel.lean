import YangMills.RG.NeumannIntegerImageCountingKernel
import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel

/-!
Cold-verified at source af35fbb8c75bf2347543034b3abf27f0217b1bbf;
production focal and exact four-name audit passed in a fresh clone.
Archive and outputs independently verified; see ledger1140.
The earlier HOT diagnostic remains separately preserved in ledger1136.

R2 finite-to-integer dictionary. The finite representative is constructed,
not supplied. The terminal owner uses block side M^depth in fine-site units.
The actual explicit counting-adjoint mass keeps (M^-d)^(2*depth), not the
source-weighted (M^-d)^depth. No image of a finite site is asserted to stay
inside its original rectangle. No Laplacian, inverse or B0 is identified.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

/-- Canonical nonnegative integer coordinates of a finite site, with no wrap
or clipping of a subsequently constructed integer image. -/
def neumannFiniteSiteIntegerCoordinates {d N : ℕ} (x : FinBox d N) : Fin d → ℤ :=
  fun mu => ((x mu).val : ℤ)

theorem neumannFiniteSiteIntegerCoordinates_injective {d N : ℕ} :
    Function.Injective (neumannFiniteSiteIntegerCoordinates (d := d) (N := N)) := by
  intro x y h
  funext mu
  apply Fin.ext
  have he := congrFun h mu
  change ((x mu).val : ℤ) = ((y mu).val : ℤ) at he
  exact_mod_cast he

theorem neumannGeneratedTerminalOwner_integerCoordinates
    {d M N : ℕ} [NeZero M] [NeZero N] (depth : ℕ)
    (x : FinBox d (cmp99RegionalLatticeSize M N depth)) :
    neumannFiniteSiteIntegerCoordinates (cmp99GeneratedTerminalBlockSite M N depth x) =
      neumannIntegerBlockOwner ((M ^ depth : ℕ) : ℤ)
        (neumannFiniteSiteIntegerCoordinates x) := by
  funext mu
  exact Int.natCast_ediv ((x mu).val) (M ^ depth)

theorem neumannGeneratedTerminalOwner_eq_iff_integerCoordinates
    {d M N : ℕ} [NeZero M] [NeZero N] (depth : ℕ)
    (x y : FinBox d (cmp99RegionalLatticeSize M N depth)) :
    cmp99GeneratedTerminalBlockSite M N depth x = cmp99GeneratedTerminalBlockSite M N depth y ↔
      neumannIntegerBlockOwner ((M ^ depth : ℕ) : ℤ) (neumannFiniteSiteIntegerCoordinates x) =
        neumannIntegerBlockOwner ((M ^ depth : ℕ) : ℤ) (neumannFiniteSiteIntegerCoordinates y) := by
  rw [← neumannGeneratedTerminalOwner_integerCoordinates,
    ← neumannGeneratedTerminalOwner_integerCoordinates]
  exact (neumannFiniteSiteIntegerCoordinates_injective (d := d) (N := N)).eq_iff.symm

/-- Exact integer owner-indicator form of the generated counting mass.
The region is arbitrary, and no full-fibre cardinality assumption is used. -/
theorem neumannGeneratedFlatCountingMass_integerOwner
    {d M N Nc : ℕ} [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
    letI : NeZero (cmp99RegionalLatticeSize M N depth) := regions.neZero
    ∀ (source target : ActiveGaugeRegion.Site (cmp99IteratedLiftActiveRegion (M := M) Omega depth))
      (v : SUNLieCoord Nc),
      ((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
          (regions.flatExplicitQprime (Nc := Nc))) (singleFinitePiLp source v) target =
        if neumannIntegerBlockOwner ((M ^ depth : ℕ) : ℤ) (neumannFiniteSiteIntegerCoordinates target.1) =
            neumannIntegerBlockOwner ((M ^ depth : ℕ) : ℤ) (neumannFiniteSiteIntegerCoordinates source.1)
          then (cmp99SourceBlockAverageWeight M d) ^ (2 * depth) • v else 0 := by
  dsimp only
  intro source target v
  rw [cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply]
  exact if_congr
    (neumannGeneratedTerminalOwner_eq_iff_integerCoordinates depth target.1 source.1) rfl rfl

end
end YangMills.RG
