import YangMills.RG.BalabanCMP89Eq246DirectedEndpointPhase
import YangMills.RG.BalabanCMP89Eq246SourceEnvelopeMoment

/-!
# Directed common-moment decay below CMP89 (2.46)

This leaf is the first joint consumer of the directed endpoint phase and the
common source-envelope transport.  It specializes the abstract envelope to
the literal fine point-source phase on the signed contour selected by
`targetEndpoint - sourceEndpoint`, then multiplies by the matching output
phase.  The two endpoint factors recombine to the exact relative `ell^1`
decay.

It controls only the common scalar moment.  It does not yet bound the bare
diagonal branch, the complete central component, the Fourier integral, or
the physical Green kernel.
-/

namespace YangMills.RG

noncomputable section

/-- The common stabilized source moment and one output synthesis phase have
the exact directed endpoint decay, without an absolute endpoint envelope. -/
theorem norm_cmp89Eq246TargetPhase_mul_stabilizedSourceMoment_signedContour_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ)
    (m : CMP89Eq246AliasIndex 4 L j) :
    let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
    let z := cmp89Eq251SignedContourMomentum rho p displacement
    ‖Complex.exp
          (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint) *
        cmp89Eq246StabilizedAliasFullSolutionMoment 4 L j mass a z
          (cmp89Eq246FinePointSourceAliasVector
            4 L j z sourceEndpoint)‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq246FinePointSourceMomentAmplitudeBound a rho := by
  dsimp only
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let g := Real.exp
    (rho * cmp89Eq246SignedEndpointPairing displacement sourceEndpoint)
  let source := cmp89Eq246FinePointSourceAliasVector
    4 L j z sourceEndpoint
  let targetPhase := Complex.exp
    (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum z m.1) targetEndpoint)
  have hreal : ∀ mu, (z mu).re = p mu := by
    intro mu
    simp [z]
  have himag : ∀ mu, |(z mu).im| ≤ rho := by
    intro mu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p displacement mu
  have hg : 0 ≤ g := by
    exact (Real.exp_pos _).le
  have hsource : ∀ n, ‖source n‖ ≤ g := by
    intro n
    exact le_of_eq
      (norm_cmp89Eq246FinePointSourceAliasVector_signedContour
        rho p displacement sourceEndpoint n)
  have hmoment :
      ‖cmp89Eq246StabilizedAliasFullSolutionMoment
          4 L j mass a z source‖ ≤
        g * cmp89Eq246FinePointSourceMomentAmplitudeBound a rho := by
    exact norm_cmp89Eq246StabilizedAliasFullSolutionMoment_le_of_envelope
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho) (g := g)
      ha hrho hradius hmass hwindow hamplitude hp hreal himag source hg hsource
  have htarget :
      ‖targetPhase‖ = Real.exp
        (-(rho * cmp89Eq246SignedEndpointPairing
          displacement targetEndpoint)) := by
    exact norm_cmp89Eq246TargetPhase_signedContour
      rho p displacement targetEndpoint m
  rw [norm_mul]
  calc
    ‖targetPhase‖ *
        ‖cmp89Eq246StabilizedAliasFullSolutionMoment
          4 L j mass a z source‖ ≤
      ‖targetPhase‖ *
        (g * cmp89Eq246FinePointSourceMomentAmplitudeBound a rho) :=
          mul_le_mul_of_nonneg_left hmoment (norm_nonneg targetPhase)
    _ = (Real.exp
          (-(rho * cmp89Eq246SignedEndpointPairing
            displacement targetEndpoint)) *
        Real.exp
          (rho * cmp89Eq246SignedEndpointPairing
            displacement sourceEndpoint)) *
        cmp89Eq246FinePointSourceMomentAmplitudeBound a rho := by
          rw [htarget]
          simpa only [g, mul_assoc]
    _ = Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq246FinePointSourceMomentAmplitudeBound a rho := by
          rw [cmp89Eq246_targetDecay_mul_sourceGrowth]

end

end YangMills.RG
