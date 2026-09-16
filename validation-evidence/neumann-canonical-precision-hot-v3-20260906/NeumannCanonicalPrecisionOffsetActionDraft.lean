import YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
import YangMills.RG.BalabanCMP89NeumannPrecisionThreeSpecies
import YangMills.RG.NeumannRetainedCountingMassDictionary
import YangMills.RG.NeumannGeneratedMassCompleteOffsets

/-!
PRE-VALIDATION: source present; .olean not materialized and the result has not
yet been verified by the compiler. R1 finite-action dictionary only.

Use the literal canonical Neumann precision, not the compressed Dirichlet
precision. Its retained tower and positive terminal prefix are constructed
internally. The counting coefficient stays literal: this module neither
normalizes the Fourier coefficient nor proves the reflected right inverse.
The three species remain separate; no bound, Green family or operator
identification is supplied as an input.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The actual canonical Neumann precision uses the explicit counting mass.
Only that term is rewritten; the internal-bond Laplacian is unchanged. -/
theorem neumannCanonicalPrecision_eq_explicitCountingMass
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (steps : ℕ) (spacing mass a : ℝ) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (steps + 1)
    letI : NeZero (cmp99RegionalLatticeSize M N (steps + 1)) := regions.neZero
    let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
      (Nc := Nc) hd hM Omega steps spacing
    let r := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
        (Nc := Nc) hd hM Omega steps spacing mass a =
      (cmp89SourceNeumannRegionalLaplacian
          (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
          (matrixSUNAdjointModel Nc)
          (cmp99SourceFlatGaugeConfig d
            (cmp99RegionalLatticeSize M N (steps + 1)) Nc) spacing +
        mass ^ 2 • ContinuousLinearMap.id ℝ
          (ActiveGaugeZeroCochain
            (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
            (SUNLieCoord Nc))) +
        cmp85SourcePrefixCountingCoefficient T a r •
          ((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
            (regions.flatExplicitQprime (Nc := Nc))) := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (steps + 1)
  letI : NeZero (cmp99RegionalLatticeSize M N (steps + 1)) := regions.neZero
  let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
    (Nc := Nc) hd hM Omega steps spacing
  let r := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
  have hmass : ((T.towerAt r.1).Qprime).adjoint.comp (T.towerAt r.1).Qprime =
      (regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
        (regions.flatExplicitQprime (Nc := Nc)) := by
    simpa only [T, r, regions,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix,
      cmp99SourceFlatRetainedPhysicalTower] using
      (neumannFlatRetainedTerminalCountingMass_eq_explicit
        hd hM (matrixSUNAdjointModel Nc) Omega (steps + 1) spacing)
  rw [cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision,
    cmp89SourceRetainedNeumannPrefixGaugePrecision,
    cmp89SourceNeumannRegionalGaugePrecision_eq_threeSpecies]
  rw [hmass]

/-- Pointwise action of the same canonical precision, with the actual complete
fibre and its counting weight. This is not a Neumann boundary equation. -/
theorem neumannCanonicalPrecision_apply_eq_completeOffsets
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (steps : ℕ) (spacing mass a : ℝ) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (steps + 1)
    letI : NeZero (cmp99RegionalLatticeSize M N (steps + 1)) := regions.neZero
    let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
      (Nc := Nc) hd hM Omega steps spacing
    let r := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
    ∀ (f : ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1)) (SUNLieCoord Nc))
      (target : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))),
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
          (Nc := Nc) hd hM Omega steps spacing mass a f target =
        (cmp89SourceNeumannRegionalLaplacian
            (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
            (matrixSUNAdjointModel Nc)
            (cmp99SourceFlatGaugeConfig d
              (cmp99RegionalLatticeSize M N (steps + 1)) Nc) spacing f) target +
          mass ^ 2 • f target +
          cmp85SourcePrefixCountingCoefficient T a r •
            ((cmp99SourceBlockAverageWeight M d) ^ (2 * (steps + 1)) •
              (∑ offset : FinBox d (M ^ (steps + 1)),
                f (neumannGeneratedCompleteFibreOffsetEquiv Omega (steps + 1)
                  (neumannGeneratedActiveCoarseOwner Omega (steps + 1) target) offset).1)) := by
  dsimp only
  intro f target
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (steps + 1)
  letI : NeZero (cmp99RegionalLatticeSize M N (steps + 1)) := regions.neZero
  rw [neumannCanonicalPrecision_eq_explicitCountingMass hd hM Omega steps spacing mass a]
  change _ + mass ^ 2 • f target +
    cmp85SourcePrefixCountingCoefficient
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
        (Nc := Nc) hd hM Omega steps spacing) a
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps) •
        (((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
          (regions.flatExplicitQprime (Nc := Nc))) f target) = _
  rw [neumannGeneratedCountingMass_apply_eq_completeOffsets Omega (steps + 1) f target]
  rfl

#print axioms neumannCanonicalPrecision_eq_explicitCountingMass
#print axioms neumannCanonicalPrecision_apply_eq_completeOffsets

end
end YangMills.RG
