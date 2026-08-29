/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq342SourceLocalizedCertificateAssembler
import YangMills.RG.BalabanCMP99Eq342LeftDerivativeAtTerminalSpacing
import YangMills.RG.BalabanCMP99Eq342RightAdjointAtTerminalSpacing
import YangMills.RG.BalabanCMP99Eq342LaplacianAtTerminalSpacing

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Uniform CMP99 (3.42) certificate from one value estimate

At the literal terminal spacing `L^(depth+1) * eta`, the powers of the block
side in the three derivative estimates cancel exactly against the inverse
spacing factors.  Consequently one value estimate with amplitude and rate
independent of `depth` produces all four actions with one common amplitude
independent of `depth`.

This is only a scalar/operator adapter.  It does not produce the regional
value estimate, its uniform amplitude or its rate, and therefore does not by
itself discharge the uniform physical `B0, delta0` boundary or attain window
15.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ} [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- A single uniform value estimate for the canonical regional Green gives
the full source-localized CMP99 (3.42) package at terminal spacing.  The
three derived amplitudes contain no residual power of `L^(depth+1)`. -/
theorem cmp99Eq342SourceLocalizedGreenCertificate_of_uniformValueBound
    {depth : ℕ}
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (background : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    {c : ℝ} (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    {eta valueAmplitude rate : ℝ}
    (heta : 0 < eta) (hvalueAmplitude : 0 ≤ valueAmplitude)
    (hrate : 0 < rate)
    (hvalue : FinitePiLpTypedBlockLocalizedSupBound
      (cmp99RegionalDirichletGreen Omega A hc hAcoer)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist
      (valueAmplitude * (L ^ (depth + 1) : ℝ) ^ 2) rate) :
    let leftAmplitude := valueAmplitude * ((1 + Real.exp rate) / eta)
    let rightAmplitude := 648 * valueAmplitude * Real.exp rate / eta
    let laplacianAmplitude :=
      4 * leftAmplitude * ((1 + Real.exp rate) / eta)
    CMP99Eq342SourceLocalizedGreenCertificate
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      depth Omega (matrixSUNAdjointModel Nc) background
      ((L ^ (depth + 1) : ℝ) * eta) A c hc hAcoer
      (cmp99Eq342CommonAmplitude valueAmplitude leftAmplitude
        rightAmplitude laplacianAmplitude) rate := by
  dsimp only
  let ell : ℝ := (L ^ (depth + 1) : ℝ)
  let leftAmplitude := valueAmplitude * ((1 + Real.exp rate) / eta)
  let rightAmplitude := 648 * valueAmplitude * Real.exp rate / eta
  let laplacianAmplitude :=
    4 * leftAmplitude * ((1 + Real.exp rate) / eta)
  have hell : 0 < ell := by
    dsimp [ell]
    positivity
  have hterminal : 0 < ell * eta := mul_pos hell heta
  have hleft0 :=
    cmp99Eq342_leftDerivative_blockLocalizedSupBound_at_terminalSpacing
      (L := L) (K := K) (Q := Q) (Nc := Nc) (depth := depth)
      Omega background (cmp99RegionalDirichletGreen Omega A hc hAcoer)
      hterminal hell (by simpa [ell] using hvalue)
  have hleft : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM Omega
          (matrixSUNAdjointModel Nc) background (ell * eta)).comp
        (cmp99RegionalDirichletGreen Omega A hc hAcoer))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist (leftAmplitude * ell) rate := by
    have hnormalize :
        valueAmplitude * ell ^ 2 *
            ((1 + Real.exp rate) / (ell * eta)) =
          leftAmplitude * ell := by
      dsimp [leftAmplitude]
      field_simp [ne_of_gt hell, ne_of_gt heta]
      ring
    rw [hnormalize] at hleft0
    exact hleft0
  have hright0 :=
    cmp99Eq342_rightAdjoint_blockLocalizedSupBound_at_terminalSpacing
      (L := L) (K := K) (Q := Q) (Nc := Nc) (depth := depth)
      Omega background (cmp99RegionalDirichletGreen Omega A hc hAcoer)
      hterminal hell (by simpa [ell] using hvalue)
  have hright : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99RegionalDirichletGreen Omega A hc hAcoer).comp
        (cmp99ActiveRegionSourceCovariantD0CLM Omega
          (matrixSUNAdjointModel Nc) background (ell * eta)).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (rightAmplitude * ell) rate := by
    have hnormalize :
        648 * valueAmplitude * Real.exp rate * ell ^ 2 / (ell * eta) =
          rightAmplitude * ell := by
      dsimp [rightAmplitude]
      field_simp [ne_of_gt hell, ne_of_gt heta]
      ring
    rw [hnormalize] at hright0
    exact hright0
  have hlaplacian0 :=
    cmp99Eq342_laplacian_blockLocalizedSupBound_at_terminalSpacing
      (L := L) (K := K) (Q := Q) (Nc := Nc) (depth := depth)
      Omega background (cmp99RegionalDirichletGreen Omega A hc hAcoer)
      hterminal hell hleft
  have hlaplacian : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) background (ell * eta)).comp
        (cmp99RegionalDirichletGreen Omega A hc hAcoer))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist laplacianAmplitude rate := by
    have hnormalize :
        4 * leftAmplitude * ell *
            ((1 + Real.exp rate) / (ell * eta)) =
          laplacianAmplitude := by
      dsimp [laplacianAmplitude]
      field_simp [ne_of_gt hell, ne_of_gt heta]
      ring
    rw [hnormalize] at hlaplacian0
    exact hlaplacian0
  have hleftAmplitude : 0 ≤ leftAmplitude := by
    dsimp [leftAmplitude]
    positivity
  have hrightAmplitude : 0 ≤ rightAmplitude := by
    dsimp [rightAmplitude]
    positivity
  have hlaplacianAmplitude : 0 ≤ laplacianAmplitude := by
    dsimp [laplacianAmplitude]
    positivity
  simpa [ell, leftAmplitude, rightAmplitude, laplacianAmplitude] using
    (cmp99Eq342SourceLocalizedGreenCertificate_of_actionBounds
      (L := L) (K := K) (Q := Q) (Nc := Nc) (depth := depth)
      (Omega := Omega) (rho := matrixSUNAdjointModel Nc)
      (U := background) (spacing := ell * eta) (A := A)
      (c := c) (hc := hc) (hAcoer := hAcoer)
      hvalueAmplitude hleftAmplitude hrightAmplitude hlaplacianAmplitude
      hrate (by simpa [ell] using hvalue) hleft hright hlaplacian)

end

end YangMills.RG
