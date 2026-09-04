import YangMills.RG.BalabanCMP99FullGreenArbitraryResidueBound
import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionary

/-!
# PRE-VALIDATION: full Green residue bound at the physical endpoints

Source is present; the `.olean` is not materialized and this result is not
verified by the compiler. The step-13 dependency is cold-sealed; this consumer remains unverified.

The target argument is minus the source displacement; the source argument
is minus the target displacement, exactly as in the sealed point-source
residue identity. No translation invariance of the full Green is assumed.
This is the unscaled residue sum: the K^-4 prefactor belongs to step 15.
The explicit amplitude is not a uniform B0. Counters remain 20/41 and
TermSource = 0; window 15 is not attained.
-/

namespace YangMills.RG

noncomputable section

/-- The physical selected residue sum before fine-block normalization. -/
def cmp99PhysicalFullGreenUnscaledOwnerResidueSum
    {K N : ℕ} [NeZero K] [NeZero N] (a : ℝ)
    (source target : FinBox 4 (K * N)) : ℂ :=
  ∑' n : CMP99FlatIntegerResidueClass 4 N
      (cmp99FinBoxZModEquiv 4 N (blockSite K N source) -
        cmp99FinBoxZModEquiv 4 N (blockSite K N target)),
    cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient K 1 0 a
      (fun mu => -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
        K source (blockSite K N source) mu)
      (fun mu => -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
        K target (blockSite K N target) mu) n.1

/-- Endpoint reflection changes the two actual arguments, not merely their
difference. This equality concerns only the affine displacement after the
already chosen, literal endpoint arguments have been fixed. -/
theorem cmp99PhysicalFullGreenOwnerResidue_affineBase_eq
    {K N : ℕ} [NeZero K] [NeZero N]
    (source target : FinBox 4 (K * N)) :
    (fun mu =>
      -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          K source (blockSite K N source) mu -
        -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          K target (blockSite K N target) mu +
        (K : ℤ) * cmp99FlatIntegerResidueRepresentative
          (cmp99FinBoxZModEquiv 4 N (blockSite K N source) -
            cmp99FinBoxZModEquiv 4 N (blockSite K N target)) mu) =
      cmp99SourceGeneratedFlatPhysicalResidueEndpointBase source target := by
  funext mu
  dsimp only [cmp99SourceGeneratedFlatPhysicalResidueEndpointBase]
  ring

/-- Owner decay for the literal reflected/swapped endpoint sum. The contour
amplitude, geometric residue factor and endpoint cost remain separate. -/
theorem norm_cmp99PhysicalFullGreenUnscaledOwnerResidueSum_le_owner
    {K N : ℕ} [NeZero K] [NeZero N] {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (source target : FinBox 4 (K * N)) :
    ‖cmp99PhysicalFullGreenUnscaledOwnerResidueSum
      (K := K) (N := N) a source target‖ ≤
      cmp89Eq246DirectedFullSolutionSumBound K 1 a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp (2 * rho) * Real.exp (-rho *
            (finBoxDist (blockSite K N source) (blockSite K N target) : ℝ)))) := by
  have h := norm_tsum_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic
    (K := K) (N := N) ha hrho hamplitude hradius hdenWindow hpairWindow
    (fun mu => -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
      K source (blockSite K N source) mu)
    (fun mu => -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
      K target (blockSite K N target) mu)
    (cmp99FinBoxZModEquiv 4 N (blockSite K N source) -
      cmp99FinBoxZModEquiv 4 N (blockSite K N target))
  rw [cmp99PhysicalFullGreenOwnerResidue_affineBase_eq source target] at h
  have hD := cmp89Eq246DirectedFullSolutionSumBound_nonneg_of_window
    (K := K) ha hrho.le hamplitude hradius hdenWindow hpairWindow
  have hgeom : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 := by positivity
  have howner :=
    cmp89SignedLatticeL1ExponentialWeight_centered_generatedPhysicalResidueEndpoint_le_owner
      hrho.le source target
  exact h.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left howner hgeom) hD)

end

end YangMills.RG
