/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalOuterNeumannAbsoluteSummability
import YangMills.RG.BalabanCMP102Eq80OuterNeumannDirectionalBound

/-!
# Source-specific uniform equation-(80) directional bound

This module instantiates the compactness argument for the literal physical
CMP99 outer Neumann layers.  Absolute summability is produced internally
from the coarse relative-defect estimate; callers do not supply a bound on
the minimizer layers.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

set_option maxHeartbeats 2000000 in
/-- The literal source CMP99 minimizer layers have one common
equation-(80) directional-derivative bound over every outer Neumann
segment. -/
theorem
    exists_uniform_bound_cmp102Eq80SourcePi4OuterNeumannDirectionalDerivative
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Set.uIcc (0 : ℝ) 1 →
        cmp102Eq80PropagatorDirectionalDerivativeBound
          D D₃
          (cmp102Eq80MinimizerPartialSum
              (fun neumannLength =>
                cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
                  (R := R) anchor K hc hmass hK
                  (cmp99SourcePi4WeakenedCoarseCovariance
                    (R := R) anchor K hc hmass hK (fun _ => 1)
                    hcoarseRate hcoarse)
                  sigma neumannLength)
              n +
            t •
              cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
                (R := R) anchor K hc hmass hK
                (cmp99SourcePi4WeakenedCoarseCovariance
                  (R := R) anchor K hc hmass hK (fun _ => 1)
                  hcoarseRate hcoarse)
                sigma n)
          Δπ J A
          (fderiv ℝ V₀
            (A -
              (cmp102Eq80MinimizerPartialSum
                  (fun neumannLength =>
                    cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
                      (R := R) anchor K hc hmass hK
                      (cmp99SourcePi4WeakenedCoarseCovariance
                        (R := R) anchor K hc hmass hK (fun _ => 1)
                        hcoarseRate hcoarse)
                      sigma neumannLength)
                  n +
                t •
                  cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
                    (R := R) anchor K hc hmass hK
                    (cmp99SourcePi4WeakenedCoarseCovariance
                      (R := R) anchor K hc hmass hK (fun _ => 1)
                      hcoarseRate hcoarse)
                    sigma n)
                (D A))) ≤ C := by
  let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
    fun neumannLength =>
      cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        sigma neumannLength
  have htermNorm : Summable fun n : ℕ => ‖term n‖ := by
    simpa [term] using
      (summable_norm_cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayers_of_source
        anchor K hsourceRange hc hmass hK hcoarseRate hcoarse
        hAhead hrho hrate hgeom Cert htri hΔ hΔ1 sigma
        hradius hRweak hdiff hcap hcontourSmall hcoarseSmall)
  simpa [term] using
    (exists_uniform_bound_cmp102Eq80OuterNeumannDirectionalDerivative
      D D₃ V₀ term Δπ J A hV₀ htermNorm)

end

end YangMills.RG
