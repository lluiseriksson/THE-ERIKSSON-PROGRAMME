/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Exact H5d1/H5d2 transport from the D4 derivative residue series to the
complete physical Holder integral sum.  Derivative and bond directions remain
independent.  This file contains no point-source operator identity, norm,
owner estimate, regional B0, window-15 claim or terminal field.
-/

import YangMills.RG.BalabanCMP89Eq249PhysicalHolderNormalizedIntegral
import YangMills.RG.BalabanCMP99SourceSeparatedPhysicalHolderTermwiseBridge
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- D4's target-wrap equivalence reindexes the literal derivative series at
`x.shift bondNu` to the ordinary `bondNu` forward shift of the source residue.
The Fourier derivative direction `derivMu` is not changed. -/
theorem
    tsum_cmp99SourceSeparatedGeneratedFlatPhysicalDerivative_shift_eq_forward_draft
    {K N : ℕ} [NeZero K] [NeZero N]
    (x : FinBox 4 (K * N)) (y : FinBox 4 N)
    (derivMu bondNu : Fin 4) (mass a : ℝ) :
    (∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          K 1 mass a derivMu
          (fun nu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              K (x.shift bondNu) y nu) n.1) =
      ∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          K 1 mass a derivMu
          (cmp89Eq248FineLatticeForwardCoordinateShift bondNu
            (fun nu =>
              -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                K x y nu)) n.1 := by
  simpa [cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient,
    cmp89SignedLatticeResidueAffineMap] using
    (tsum_cmp99SourceSeparatedFineTargetShift_affineResidue_eq_forward_draft
      (M := K) (N := N) x y bondNu
      (fun endpointU =>
        cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
          K 1 mass a derivMu endpointU))

/-- The complete physical Holder integrals sum to the literal
`xi^(-alpha)` multiple of the source-minus-target derivative coefficient
series.  Cancellation is performed termwise before any norm. -/
theorem
    tsum_cmp89Eq249PhysicalHolderIntegral_eq_xiRpowInv_mul_derivativeDiff_draft
    {K N : ℕ} [NeZero K] [NeZero N]
    {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (x : FinBox 4 (K * N)) (derivMu bondNu : Fin 4) (u : Fin 4 → ℤ) :
    let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
    let holderU := cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu)
    let xi := cmp89Eq249FineLatticeSpacing K 1
    (∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
          K 1 mass a alpha derivMu holderU
          (cmp89SignedLatticeResidueAffineMap K forwardU n.1)) =
      (((xi ^ alpha : ℝ) : ℂ)⁻¹) *
        ((∑' n : CMP99FlatIntegerResidueClass 4 N 0,
            cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
              K 1 mass a derivMu u n.1) -
          ∑' n : CMP99FlatIntegerResidueClass 4 N 0,
            cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
              K 1 mass a derivMu forwardU n.1) := by
  dsimp only
  let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
  let holderU := cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu)
  let xi := cmp89Eq249FineLatticeSpacing K 1
  let c : ℂ := (((xi ^ alpha : ℝ) : ℂ)⁻¹)
  let sourceCoeff := fun n : CMP99FlatIntegerResidueClass 4 N 0 =>
    cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
      K 1 mass a derivMu u n.1
  let forwardCoeff := fun n : CMP99FlatIntegerResidueClass 4 N 0 =>
    cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
      K 1 mass a derivMu forwardU n.1
  let holderTerm := fun n : CMP99FlatIntegerResidueClass 4 N 0 =>
    cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_draft
      K 1 mass a alpha derivMu holderU
      (cmp89SignedLatticeResidueAffineMap K forwardU n.1)
  have hsource : Summable sourceCoeff :=
    summable_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_zeroResidue_draft
      (K := K) (N := N) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass derivMu u
  have hforward : Summable forwardCoeff :=
    summable_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_zeroResidue_draft
      (K := K) (N := N) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass derivMu forwardU
  have hpoint : ∀ n, holderTerm n =
      c * (sourceCoeff n - forwardCoeff n) := by
    intro n
    have hholder :=
      cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_eq_xiRpowInv_mul_raw_draft
        (L := K) (j := 1) (mass := mass) (a := a) (alpha := alpha)
        derivMu (cmp116CMP89PhysicalBondHolderDisplacement_unit (x, bondNu))
        (cmp89SignedLatticeResidueAffineMap K forwardU n.1)
    have hraw :=
      cmp89Eq249NormalizedFineLatticeStabilizedIntegral_physicalBond_eq_sourceCoefficient_sub_forwardCoefficient_draft
        (K := K) (N := N) (mass := mass) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hwindow hmass x derivMu bondNu u n
    simpa [holderTerm, holderU, sourceCoeff, forwardCoeff, forwardU, c, xi]
      using hholder.trans (congrArg (fun z : ℂ => c * z) hraw)
  change (∑' n, holderTerm n) =
    c * ((∑' n, sourceCoeff n) - ∑' n, forwardCoeff n)
  calc
    (∑' n, holderTerm n) =
        ∑' n, c * (sourceCoeff n - forwardCoeff n) := tsum_congr hpoint
    _ = c * ∑' n, (sourceCoeff n - forwardCoeff n) := tsum_mul_left
    _ = c * ((∑' n, sourceCoeff n) - ∑' n, forwardCoeff n) := by
      rw [hsource.tsum_sub hforward]

end

end YangMills.RG
