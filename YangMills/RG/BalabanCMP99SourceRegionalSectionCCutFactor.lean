/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalSectionCRightFactor
import YangMills.RG.FinitePiLpTypedCutoff

/-!
# The cut regional core of CMP99 equation (3.97)

The image of printed page 412 gives the factor

`tildeChi * Q' * (G'_Pi0^2 - G'_Pi^2) * Q'^* * h_Pi * C_Pi * h_Pi`.

This file inserts the two kinds of scalar cutoff into the typed regional
resolvent core.  The cutoff functions remain explicit data because CMP99
chooses `h` through the partition of unity defined in CMP95, equation (1.118),
rather than fixing a unique formula.  Their contractivity is the precise
property used here.  Identification of a particular partition with these
functions is a separate source-dictionary theorem.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- The small-region coarse site type at one source transition. -/
abbrev CMP99OmegaTransitionSmallCoarseSite
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :=
  ActiveGaugeRegion.Site
    (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r)))

/-- The large-region coarse site type at one source transition. -/
abbrev CMP99OmegaTransitionLargeCoarseSite
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :=
  ActiveGaugeRegion.Site
    (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)))

/-- The two scalar cutoffs occurring in the typed version of (3.97), together
with the pointwise bounds supplied by the source partition of unity. -/
structure CMP99SourceSectionCTransitionCutData
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) where
  exterior : CMP99OmegaTransitionSmallCoarseSite (M := M) Seq r → ℝ
  partition : CMP99OmegaTransitionLargeCoarseSite (M := M) Seq r → ℝ
  exterior_norm_le_one : ∀ x, ‖exterior x‖ ≤ 1
  partition_norm_le_one : ∀ x, ‖partition x‖ ≤ 1

/-- Literal typed cut core corresponding to the operator ordering in (3.97).
The middle defect already contains the `Q'`, Green-square mismatch and
weighted adjoint; the covariance is cut by `h_Pi` on both sides and the whole
factor is cut on the left by the exterior localization. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepSectionCCutFactor
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (Cuts : CMP99SourceSectionCTransitionCutData (M := M) Seq r)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :=
  (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) Cuts.exterior).comp
    ((cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect
        Seq r rho U hspacing ha).comp
      ((finitePiLpScalarMultiplier (g := SUNLieCoord Nc) Cuts.partition).comp
        ((cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
            (cmp99OmegaTransitionIndex r) rho U hspacing ha).comp
          (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) Cuts.partition))))

set_option maxHeartbeats 1200000 in
/-- The cut factor retains the explicit, volume-independent amplitude and the
fixed rate of the one-sided resolvent core. -/
theorem cmp99OmegaSourcePhysicalOneStepSectionCCutFactor_exponentialKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (Cuts : CMP99SourceSectionCTransitionCutData (M := M) Seq r)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    let F := cmp99OmegaSourcePhysicalOneStepSectionCCutFactor
      Seq r Cuts rho U hspacing ha
    FinitePiLpTypedExponentialKernelBound F
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayAmplitude M spacing a)
      (cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayRate M spacing a) := by
  dsimp only
  let mu := cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate M spacing a
  let theta := cmp99OmegaSourcePhysicalOneStepCombesThomasRate M spacing a
  let base := min mu (theta / 12)
  let sigma := base / 3
  let AC := 2 /
    (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹
  let AD := cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDecayAmplitude
    M spacing a
  let S := cmp99OmegaSiteExpSumBound sigma
  let largeIndex := cmp99OmegaTransitionIndex r
  let Cl := cmp99OmegaSourcePhysicalOneStepCoarseCovariance
    Seq largeIndex rho U hspacing ha
  let D := cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect
    Seq r rho U hspacing ha
  let Hlarge := finitePiLpScalarMultiplier
    (g := SUNLieCoord Nc) Cuts.partition
  let Hsmall := finitePiLpScalarMultiplier
    (g := SUNLieCoord Nc) Cuts.exterior
  have hmu : 0 < mu :=
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate_pos hspacing ha
  have htheta : 0 < theta :=
    cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos hspacing ha
  have hbase : 0 < base := lt_min hmu (by positivity)
  have hsigma : 0 < sigma := by positivity
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hCl0 : FinitePiLpTypedExponentialKernelBound Cl
      (cmp99OmegaCoarseDist (M := M) Seq largeIndex) AC mu :=
    finitePiLpTypedExponentialKernelBound_of_square
      (cmp99OmegaSourcePhysicalOneStepCoarseCovariance_exponentialKernelBound
        Seq largeIndex rho U hspacing ha)
  have hD0 : FinitePiLpTypedExponentialKernelBound D
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r) AD (theta / 12) :=
    cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect_exponentialKernelBound
      Seq r rho U hspacing ha
  have hClBase : FinitePiLpTypedExponentialKernelBound Cl
      (cmp99OmegaCoarseDist (M := M) Seq largeIndex) AC base :=
    finitePiLpTypedExponentialKernelBound_mono_rate hbase (min_le_left _ _) hCl0
  have hD : FinitePiLpTypedExponentialKernelBound D
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r) AD base :=
    finitePiLpTypedExponentialKernelBound_mono_rate hbase (min_le_right _ _) hD0
  have hCutCl : FinitePiLpTypedExponentialKernelBound
      (Hlarge.comp (Cl.comp Hlarge))
      (cmp99OmegaCoarseDist (M := M) Seq largeIndex) AC base := by
    exact finitePiLpTypedExponentialKernelBound_cut
      Cuts.partition Cuts.partition Cl
      Cuts.partition_norm_le_one Cuts.partition_norm_le_one hClBase
  have hsumTransition : ∀ target,
      ∑ middle, Real.exp (-(sigma *
        (cmp99OmegaCoarseTransitionDist (M := M) Seq r target middle : ℝ))) ≤ S := by
    intro target
    exact cmp99OmegaCoarseTransitionDist_exp_sum_le Seq r target hsigma
  have hcore := finitePiLpTypedExponentialKernelBound_comp
    (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
    (cmp99OmegaCoarseDist (M := M) Seq largeIndex)
    (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
    (fun target middle source =>
      finBoxDist_triangle
        (cmp99OmegaCoarseRepresentative (M := M) Seq
          (cmp99OmegaTransitionNextIndex r) target)
        (cmp99OmegaCoarseRepresentative (M := M) Seq largeIndex middle)
        (cmp99OmegaCoarseRepresentative (M := M) Seq largeIndex source))
    hsigma (by dsimp [sigma]; linarith) hS hsumTransition
    D (Hlarge.comp (Cl.comp Hlarge)) hD hCutCl
  have hcore' : FinitePiLpTypedExponentialKernelBound
      (D.comp (Hlarge.comp (Cl.comp Hlarge)))
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (AD * AC * S) (2 * base / 3) := by
    convert hcore using 1
    ring
  have hcut :=
    finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_left
      Cuts.exterior (D.comp (Hlarge.comp (Cl.comp Hlarge)))
      Cuts.exterior_norm_le_one hcore'
  simpa [cmp99OmegaSourcePhysicalOneStepSectionCCutFactor,
    cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayRate,
    cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayAmplitude,
    mu, theta, base, sigma, AC, AD, S, largeIndex, Cl, D, Hlarge, Hsmall]
    using hcut

end

end YangMills.RG
