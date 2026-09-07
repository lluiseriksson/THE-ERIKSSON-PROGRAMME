import YangMills.RG.BalabanCMP89Eq246FullEndpointReflection
import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceNegativePhysicalDomain

/-!
# Physical endpoint reflection with domains built internally

This specialization supplies both complete Eq. (2.46) solver domains from
the physical source producers.  The statement has no free inverse, no free
negative-momentum domain and no periodic endpoint identification.
-/

namespace YangMills.RG

noncomputable section

/-- Simultaneous momentum and endpoint reflection at the literal physical
coarse momentum, with both solver domains constructed internally. -/
theorem cmp99SourceFlatFullPointSourcePhysicalFineToFineGreenIntegrand_neg_swap
    {M N' : ℕ} [NeZero M] [NeZero N'] {a rho : ℝ}
    (ha : 0 < a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (ell : FinBox 4 N') (target source : Fin 4 → ℤ) :
    cmp89Eq246PhysicalFineToFineGreenIntegrand M 1 0 a
        (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (fun mu => -target mu) (fun mu => -source mu) =
      cmp89Eq246PhysicalFineToFineGreenIntegrand M 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (fun mu => -source mu) (fun mu => -target mu) := by
  apply cmp89Eq246PhysicalFineToFineGreenIntegrand_neg_swap
  · exact cmp99SourceFlatFullPointSourceSolutionDomain_physical
      ha hrho hamplitude hradius hdenWindow hpairWindow ell
  · exact cmp99SourceFlatFullPointSourceSolutionDomain_neg_physical
      ha hrho hamplitude hradius hdenWindow hpairWindow ell

end

end YangMills.RG
