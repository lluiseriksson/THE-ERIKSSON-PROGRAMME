import YangMills.RG.BalabanCMP99SourceAliasReflectionStabilizedSolution
import YangMills.RG.BalabanCMP89Eq246StabilizedAliasTransposeFullSolution
import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceSolutionDomain

/-!
# PRE-VALIDATION: complete solver domain at the negated physical momentum

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

The endpoint-reflection theorem needs the complete finite solver domain at
both `z` and `-z`.  This module constructs the second domain from the sealed
physical representative, the actual half-open alias reflection and the
source-specific nonzero central pair.  It does not accept the negative domain
as an input and does not identify periodic representatives.
-/

namespace YangMills.RG

noncomputable section

/-- The literal negative of every uncentered physical coarse momentum has the
complete Eq. (2.46) solver domain. -/
theorem cmp99SourceFlatFullPointSourceSolutionDomain_neg_physical
    {M N' : ℕ} [NeZero M] [NeZero N'] {a rho : ℝ}
    (ha : 0 < a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (ell : FinBox 4 N') :
    CMP89Eq246FullSolutionDomain 4 M 1 0 a
      (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) := by
  let z := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  let reflect := cmp99SourceAliasIndexOneReflection 4 M
  let central := cmp89Eq249CentralAliasIndex 4 M 1
  have hz : CMP89Eq246FullSolutionDomain 4 M 1 0 a z := by
    exact cmp99SourceFlatFullPointSourceSolutionDomain_physical
      ha hrho hamplitude hradius hdenWindow hpairWindow ell
  have hpair : cmp89Eq249CentralEntireAveragePair 4 M 1 z ≠ 0 := by
    exact cmp89Eq249CentralEntireAveragePair_physicalCoarse_ne_zero ell
  have hcolumn :
      cmp89Eq246EntireAliasAverageColumn 4 M 1 z central ≠ 0 := by
    exact cmp89Eq246CentralAverageColumn_ne_zero_of_pair_ne_zero
      4 M 1 z hpair
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    let n : CMP89Eq246AliasIndex 4 M 1 := reflect.symm m
    have hreflect : reflect n = m := Equiv.apply_symm_apply reflect m
    have hn : n ≠ central := by
      intro hn
      apply hm
      rw [← hreflect, hn]
      exact cmp99SourceAliasIndexOneReflection_central 4 M
    rw [← hreflect]
    rw [cmp89Eq246EntireAliasFineSymbol_neg_reflection_eq]
    exact hz.fine n hn
  · rw [cmp89Eq249CentralStabilizedAliasDenominator_neg]
    exact hz.stabilized
  · have hreflectCentral : reflect central = central :=
      cmp99SourceAliasIndexOneReflection_central 4 M
    have hrow := cmp89Eq246EntireAliasAverageRow_neg_reflection_eq_column
      z central
    rw [hreflectCentral] at hrow
    rw [hrow]
    exact hcolumn

end

end YangMills.RG
