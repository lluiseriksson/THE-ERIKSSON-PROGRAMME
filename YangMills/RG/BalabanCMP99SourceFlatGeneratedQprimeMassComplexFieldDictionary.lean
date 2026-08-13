/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeMassComplexCoordinateDictionary

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

# Field dictionary for the generated flat `Q'^*Q'` mass

The sealed coordinate dictionary is summed over the literal generated active
carrier.  On the full box the corresponding complex field is an explicit sum
of coordinate deltas, hence zero away from the transported active carrier.

The result remains restricted to complexifications of real generated fields
and to transported active targets.  It does not identify the generated
carrier with the full box, transport the Laplacian, identify full precisions,
construct an inverse or produce a regional Green bound.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Explicit zero extension of a complexified generated terminal field to
the one-block full box.  The definition is a finite sum of ordinary full-box
coordinate deltas, so no inverse carrier map or free support predicate is
introduced. -/
def cmp99SourceGeneratedTerminalComplexZeroExtension
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (eta : PiLp 2 (fun _ : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
        SUNLieCoord Nc)) :
    FinBox d ((M ^ (depth + 1)) * N) → SUNLieComplexCoord Nc :=
  ∑ source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)),
    cmp99SourceFlatFullComplexSingle
      (cmp99GeneratedFineBoxOneBlockEquiv
        (d := d) M N (depth + 1) source.1)
      (cmp99SUNLieCoordComplexificationLM Nc (eta source))

/-- The literal full-box complex mass distributes over a finite sum of
full-box fields. -/
theorem cmp99SourceFlatFullComplexQprimeMass_sum
    {ι : Type*} [Fintype ι]
    (phi : ι → FinBox d (M * N) → SUNLieComplexCoord Nc)
    (target : FinBox d (M * N)) :
    cmp99SourceFlatFullComplexQprimeMass (∑ i, phi i) target =
      ∑ i, cmp99SourceFlatFullComplexQprimeMass (phi i) target := by
  classical
  simp only [cmp99SourceFlatFullComplexQprimeMass]
  rw [show cmp99SourceFlatFullActiveComplexField (∑ i, phi i) =
      ∑ i, cmp99SourceFlatFullActiveComplexField (phi i) by
    apply WithLp.ofLp_injective
    funext x
    simp]
  rw [map_sum, map_sum]
  exact finitePiLp_sum_apply _ _ _

/-- The generated counting mass on an arbitrary real active field agrees,
after pointwise complexification, with the literal full-box complex mass of
its explicit zero extension at every transported active target. -/
theorem cmp99SourceGeneratedCountingMass_complexFieldDictionary
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (spacing epsilon : ℝ)
    (eta : PiLp 2 (fun _ : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
        SUNLieCoord Nc))
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) :
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
    let targetBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) target.1
    cmp99SUNLieCoordComplexificationLM Nc
        (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon •
          (((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
            (regions.flatExplicitQprime (Nc := Nc))) eta target)) =
      ((cmp99SourceGeneratedFullComplexA
          d M (depth + 1) spacing epsilon : ℝ) : ℂ) •
        cmp99SourceFlatFullComplexQprimeMass
          (M := M ^ (depth + 1)) (N' := N)
          (cmp99SourceGeneratedTerminalComplexZeroExtension
            (M := M) (Nc := Nc) Omega depth eta) targetBox := by
  classical
  dsimp only
  have heta : eta = ∑ source, singleFinitePiLp source (eta source) :=
    (sum_singleFinitePiLp_eq eta).symm
  conv_lhs =>
    rw [heta]
  rw [map_sum]
  rw [finitePiLp_sum_apply]
  rw [Finset.smul_sum]
  rw [map_sum]
  unfold cmp99SourceGeneratedTerminalComplexZeroExtension
  rw [cmp99SourceFlatFullComplexQprimeMass_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro source _hsource
  exact cmp99SourceGeneratedCountingMass_complexCoordinateDictionary
    Omega depth spacing epsilon source target (eta source)

end

end YangMills.RG
