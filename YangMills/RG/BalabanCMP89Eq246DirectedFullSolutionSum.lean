import YangMills.RG.BalabanCMP89Eq246DirectedCentralComponent
import YangMills.RG.BalabanCMP89Eq246DirectedNoncentralSum

/-!
# PRE-VALIDATION: complete directed Fourier sum below CMP89 (2.46)

Source is present, its promoted `.olean` has not yet been materialized in a
fresh checkout, and the result has not yet been cold-verified by the compiler.

The central alias and the literal noncentral alias sum share the same source
and target endpoints. Their two amplitude budgets remain separate until the
last addition.
-/

namespace YangMills.RG

noncomputable section

/-- The complete target-phased finite-alias solution at fixed Brillouin
momentum. -/
def cmp89Eq246DirectedFullSolutionSum
    (L j : ℕ) [NeZero L] (mass a rho : ℝ)
    (p targetEndpoint sourceEndpoint : Fin 4 → ℝ) : ℂ :=
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let central := cmp89Eq249CentralAliasIndex 4 L j
  Complex.exp
      (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z central.1) targetEndpoint) *
    cmp89Eq246StabilizedFinePointSourceSolution
      4 L j mass a z sourceEndpoint central +
    cmp89Eq246DirectedNoncentralSolutionSum
      L j mass a rho p targetEndpoint sourceEndpoint

/-- The complete directed amplitude budget, with central and noncentral
contributions still visible as separate summands. Its `(L^j+1)^2` term is
the value component of the printed CMP99 (3.42) scale vector; it is not part
of the scale-uniform coefficient and must not be erased. -/
def cmp89Eq246DirectedFullSolutionSumBound
    (L j : ℕ) (a rho : ℝ) : ℝ :=
  cmp89Eq246FinePointSourceCentralComponentAmplitudeBound a rho +
    cmp89Eq246DirectedNoncentralSolutionSumBound L j a rho

/-- The complete finite-alias solution inherits the common relative endpoint
decay of its central and noncentral branches. -/
theorem norm_cmp89Eq246DirectedFullSolutionSum_signedContour_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hstabilized : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpair : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (targetEndpoint sourceEndpoint : Fin 4 → ℝ) :
    let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
    ‖cmp89Eq246DirectedFullSolutionSum
        L j mass a rho p targetEndpoint sourceEndpoint‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq246DirectedFullSolutionSumBound L j a rho := by
  dsimp only
  let displacement := fun mu => targetEndpoint mu - sourceEndpoint mu
  let z := cmp89Eq251SignedContourMomentum rho p displacement
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let centralTerm :=
    Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z central.1) targetEndpoint) *
      cmp89Eq246StabilizedFinePointSourceSolution
        4 L j mass a z sourceEndpoint central
  let noncentralTerm := cmp89Eq246DirectedNoncentralSolutionSum
    L j mass a rho p targetEndpoint sourceEndpoint
  let decay := Real.exp
    (-(rho * cmp89Eq251DisplacementL1 displacement))
  let centralBound :=
    cmp89Eq246FinePointSourceCentralComponentAmplitudeBound a rho
  let noncentralBound :=
    cmp89Eq246DirectedNoncentralSolutionSumBound L j a rho
  have hcentral : ‖centralTerm‖ ≤ decay * centralBound := by
    simpa [centralTerm, decay, centralBound, central, z, displacement] using
      (norm_cmp89Eq246CentralTargetPhase_mul_centralComponent_signedContour_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hstabilized hpair hamplitude hp
        targetEndpoint sourceEndpoint)
  have hnoncentral : ‖noncentralTerm‖ ≤ decay * noncentralBound := by
    simpa [noncentralTerm, decay, noncentralBound, displacement] using
      (norm_cmp89Eq246DirectedNoncentralSolutionSum_signedContour_le
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hradius hmass hstabilized hamplitude hp
        targetEndpoint sourceEndpoint)
  rw [cmp89Eq246DirectedFullSolutionSum]
  change ‖centralTerm + noncentralTerm‖ ≤ _
  calc
    _ ≤ ‖centralTerm‖ + ‖noncentralTerm‖ := norm_add_le _ _
    _ ≤ decay * centralBound + decay * noncentralBound :=
      add_le_add hcentral hnoncentral
    _ = Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) *
        cmp89Eq246DirectedFullSolutionSumBound L j a rho := by
      simp only [decay, centralBound, noncentralBound,
        cmp89Eq246DirectedFullSolutionSumBound]
      ring

end

end YangMills.RG
