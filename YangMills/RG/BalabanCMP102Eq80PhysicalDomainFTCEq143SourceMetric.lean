/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCSecondFieldSourceMetricBound
import YangMills.RG.BalabanCMP116Eq143To219

/-!
# Match the CMP102 source-metric producer to equation (1.43)

The reconstructed CMP102 domain Hessian already carries separate exponential
decay in the domain cardinality and tree metric.  This file chooses those two
rates exactly as printed in CMP116 equation (1.43) and isolates the remaining
producer-side prefactor comparison.

The offsets `10000` used by the source-metric reconstruction remain visible
in the prefactor.  No equation-(1.43) bound is assumed under another name.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev Eq143CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- Cardinality-decay rate which matches the `M⁻⁴ |Y|` exponent in (1.43).

`CMP116LocalizationDomain.blocks.card` already is `M⁻⁴ |Y|`, by
`cmp116LocalizationDomain_sourceCard_eq`.  Hence the rate multiplying the
block count has no second factor `M⁻⁴`.  The unused scale argument is retained
to keep the source-facing API stable. -/
noncomputable def cmp102Eq80Eq143CardRate
    (_Msource : ℕ) (kappa1 : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (kappa1 - 1)

/-- Tree-metric decay rate which matches the `d_k(Y)` exponent in (1.43). -/
def cmp102Eq80Eq143MetricRate (kappa1 : ℝ) : ℝ :=
  (1 / 8 : ℝ) * (kappa1 - 1)

/-- The producer-only prefactor left after the two source-metric exponential
decays have been matched exactly with equation (1.43).  In particular, the
two reconstruction offsets `exp(rate * 10000)` remain explicit. -/
noncomputable def cmp102Eq80Eq143ProducerPrefactor
    {M Q Nc n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      Eq143CoarseField Q Nc →L[ℝ] Eq143CoarseField Q Nc)
    (sourceJetBound summationRatio : ℝ)
    (layerWord : Fin n → ℕ)
    (Δ Msource : ℕ) (kappa1 : ℝ) : ℝ :=
  sourceJetBound *
    ContinuousLinearMap.opNorm (𝕜 := ℝ)
      (cmp99PhysicalRectangularOfComplexMatrixContinuousLinearMap
        (d := 4) (N₁ := 2 * Q) (N₂ := M * (2 * Q)) (Nc := Nc)) *
    ((cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
    cmp102Eq80PhysicalFineHeadTailEndpointMajorant
      (M := M) baseCoarseCovariance *
    Real.exp (cmp102Eq80Eq143CardRate Msource kappa1 * 10000) *
    Real.exp (cmp102Eq80Eq143MetricRate kappa1 * 10000) *
    summationRatio ^ (1 + ∑ i : Fin n, (layerWord i + 1)) *
    (1 -
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio)⁻¹

/-- The sole scalar comparison required of the physical CMP102 producers.
It contains no domain cardinality or domain metric and hence is strictly
stronger information than merely assuming equation (1.43) pointwise. -/
def CMP102Eq80Eq143ProducerBudget
    {M Q Nc n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      Eq143CoarseField Q Nc →L[ℝ] Eq143CoarseField Q Nc)
    (sourceJetBound summationRatio : ℝ)
    (layerWord : Fin n → ℕ)
    (Δ Msource : ℕ) (kappa1 C3 epsilon1 C2 : ℝ) : Prop :=
  cmp102Eq80Eq143ProducerPrefactor
      (M := M) baseCoarseCovariance sourceJetBound summationRatio
      layerWord Δ Msource kappa1 ≤
    C3 * epsilon1 * (Msource : ℝ) ^ 4 * Real.exp (C2 * kappa1)

/-- Exact scalar match between the CMP102 source-metric majorant and the
printed equation-(1.43) majorant.  All dependence on the localization domain
is discharged by the two displayed rate choices; only the producer budget,
which is uniform in the domain, remains. -/
theorem
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant_le_eq143
    {M Q Nc n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      Eq143CoarseField Q Nc →L[ℝ] Eq143CoarseField Q Nc)
    (sourceJetBound summationRatio : ℝ)
    (layerWord : Fin n → ℕ)
    (Y : CMP116LocalizationDomain M (2 * Q))
    (Δ Msource : ℕ) (kappa1 C3 epsilon1 C2 : ℝ)
    (hbudget : CMP102Eq80Eq143ProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound summationRatio
      layerWord Δ Msource kappa1 C3 epsilon1 C2) :
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant
        baseCoarseCovariance sourceJetBound
        (cmp102Eq80Eq143CardRate Msource kappa1)
        (cmp102Eq80Eq143MetricRate kappa1)
        summationRatio layerWord Y Δ ≤
      cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
        (cmp116CubeEdgeTreeMetric Y : ℝ) Y.blocks.card := by
  let κcard := cmp102Eq80Eq143CardRate Msource kappa1
  let κmetric := cmp102Eq80Eq143MetricRate kappa1
  let decay :=
    Real.exp (-(κcard * (Y.blocks.card : ℝ))) *
      Real.exp (-(κmetric * (cmp116CubeEdgeTreeMetric Y : ℝ)))
  have hdecay0 : 0 ≤ decay := by
    positivity
  have hmul :
      cmp102Eq80Eq143ProducerPrefactor
            (M := M) baseCoarseCovariance sourceJetBound summationRatio
            layerWord Δ Msource kappa1 * decay ≤
        (C3 * epsilon1 * (Msource : ℝ) ^ 4 *
            Real.exp (C2 * kappa1)) * decay :=
    mul_le_mul_of_nonneg_right hbudget hdecay0
  have hdecay :
      decay =
        Real.exp (
          -(1 / 8 : ℝ) * (kappa1 - 1) *
              (cmp116CubeEdgeTreeMetric Y : ℝ) -
            (1 / 2 : ℝ) * (kappa1 - 1) * Y.blocks.card) := by
    dsimp [decay]
    rw [← Real.exp_add]
    congr 1
    dsimp [κcard, κmetric, cmp102Eq80Eq143CardRate,
      cmp102Eq80Eq143MetricRate]
    ring
  calc
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant
        baseCoarseCovariance sourceJetBound
        (cmp102Eq80Eq143CardRate Msource kappa1)
        (cmp102Eq80Eq143MetricRate kappa1)
        summationRatio layerWord Y Δ =
      cmp102Eq80Eq143ProducerPrefactor
          (M := M) baseCoarseCovariance sourceJetBound summationRatio
          layerWord Δ Msource kappa1 * decay := by
        unfold
          cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant
          cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
          cmp102Eq80Eq143ProducerPrefactor
        dsimp [decay, κcard, κmetric]
        ring
    _ ≤
      (C3 * epsilon1 * (Msource : ℝ) ^ 4 *
        Real.exp (C2 * kappa1)) * decay := hmul
    _ =
      cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
        (cmp116CubeEdgeTreeMetric Y : ℝ) Y.blocks.card := by
        rw [hdecay]
        unfold cmp116Eq143QMajorant
        rfl

end

end YangMills.RG
