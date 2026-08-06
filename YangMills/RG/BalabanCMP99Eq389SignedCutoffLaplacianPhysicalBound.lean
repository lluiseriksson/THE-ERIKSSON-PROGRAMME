/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq342RegionalGreenCertificate
import YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay
import YangMills.RG.BalabanCMP99SourceSeparatedSignedCutoffLaplacian
import YangMills.RG.FinitePiLpSourceOverlapSum

/-!
# PRE-VALIDATION: signed cutoff-Laplacian species in CMP99 (3.89)

The source is present, but its `.olean` has not yet been materialized and the
results below have not yet been verified by the Lean compiler.

This module composes the literal signed cutoff-Laplacian coefficient with the
canonical regional Dirichlet Green from the CMP99 (3.42) certificate.  The
inverse-square large-block gain is present before the cell sum, and the sum
pays exactly the already derived source overlap `16` through the right signed
cutoff.

No Combes--Thomas/Schur replacement, third species, full CMP99 (3.89)
estimate, defect contraction, or attainment of window 15 is claimed here.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {L Klarge Q Nc : ℕ}
variable [NeZero L] [NeZero Klarge] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389SignedSeparatedBlockSide
    (L Klarge depth : ℕ) [NeZero L] [NeZero Klarge] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L Klarge depth) :=
  ⟨by
    unfold cmp99SourceSeparatedLargeBlockSide
    exact (Nat.mul_pos (NeZero.pos Klarge)
      (pow_pos (NeZero.pos L) (depth + 1))).ne'⟩

private instance instNeZeroEq389SignedSeparatedAmbientSide
    (L Klarge Q depth : ℕ) [NeZero L] [NeZero Klarge] [NeZero Q] :
    NeZero
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos Klarge)
      (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- The value component of the source CMP99 (3.42) certificate survives
restriction to, and zero extension from, the canonical regional Green.

This is a transport of the certified regional kernel, not a new Green
estimate and not a Combes--Thomas substitute for (3.42). -/
theorem CMP99Eq342RegionalGreenCertificate.extended_value_bound
    {m q : ℕ} [NeZero m] [NeZero q]
    (Omega : ActiveGaugeRegion 4 (m * (2 * q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (m * (2 * q)) Nc)
    (spacing : ℝ)
    (A : GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 ell : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U spacing A c hc
      hAcoer B0 delta0 ell) :
    FinitePiLpExponentialKernelBound
      (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer)
      (cmp99Eq342RescaledBlockDist m q)
      (B0 * ell ^ 2) delta0 := by
  refine ⟨C.value_bound.1, C.delta0_pos, ?_⟩
  intro source target v
  by_cases hsource : source ∈ Omega.sites
  · by_cases htarget : target ∈ Omega.sites
    · let sourceOmega : ActiveGaugeRegion.Site Omega := ⟨source, hsource⟩
      let targetOmega : ActiveGaugeRegion.Site Omega := ⟨target, htarget⟩
      have hrestrict :
          restrictZeroCLM Omega (singleFinitePiLp source v) =
            singleFinitePiLp sourceOmega v := by
        apply PiLp.ext
        intro x
        by_cases hx : x.1 = source
        · have heq : x = sourceOmega := Subtype.ext hx
          subst x
          simp [restrictZeroCLM, sourceOmega]
        · have hne : x ≠ sourceOmega := by
            intro heq
            exact hx (congrArg Subtype.val heq)
          simp [restrictZeroCLM, singleFinitePiLp, hx, hne]
      change ‖extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega A hc hAcoer
            (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
      rw [extendZeroZeroCLM_apply_of_mem Omega _ target htarget, hrestrict]
      exact C.value_bound.2.2 sourceOmega targetOmega v
    · change ‖extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega A hc hAcoer
            (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
      simp [extendZeroZeroCLM_apply_of_not_mem Omega _ target htarget]
      exact mul_nonneg
        (mul_nonneg C.value_bound.1 (Real.exp_pos _).le) (norm_nonneg v)
  · have hrestrict :
        restrictZeroCLM Omega (singleFinitePiLp source v) = 0 := by
      apply PiLp.ext
      intro x
      have hne : x.1 ≠ source := by
        intro heq
        apply hsource
        simpa [heq] using x.2
      simp [restrictZeroCLM, singleFinitePiLp, hne]
    change ‖extendZeroZeroCLM Omega
        (cmp99RegionalDirichletGreen Omega A hc hAcoer
          (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
    rw [hrestrict]
    simp only [map_zero, PiLp.zero_apply, norm_zero]
    exact mul_nonneg
      (mul_nonneg C.value_bound.1 (Real.exp_pos _).le) (norm_nonneg v)

/-- Explicit pre-overlap amplitude of the signed cutoff-Laplacian species in
CMP99 (3.89).  Both powers of the generated Green scale cancel before any
cell sum. -/
noncomputable def cmp99Eq389SignedCutoffLaplacianSourceBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (B0 : ℝ) (Klarge : ℕ) : ℝ :=
  (12 * B0 * P.secondDerivBound) / (Klarge : ℝ) ^ 2

/-- One signed cutoff-Laplacian cell, with the coefficient acting on the
target, the canonical regional Green in the middle, and the same signed
cutoff acting on the source. -/
noncomputable def cmp99Eq389SignedCutoffLaplacianRegionalCorrection
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc) :=
  (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
      (cmp99SourceSeparatedSignedCutoffLaplacianCoefficient
        (L := L) (K := Klarge) P depth cell)).comp
    ((cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer).comp
      (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
        (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L Klarge Q depth cell)))

/-- The isolated operator is definitionally the literal second species of
CMP99 (3.88), evaluated after the canonical regional Green and the right
signed cutoff. -/
theorem cmp99Eq389SignedCutoffLaplacianRegionalCorrection_apply
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))) :
    cmp99Eq389SignedCutoffLaplacianRegionalCorrection
        P depth cell Omega A c hc hAcoer phi x =
      cmp99CutoffLaplacianCorrection (Nc := Nc) 1
        (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L Klarge Q depth cell)
        (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer
          (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
            (cmp99SourceSeparatedSignedLargeBlockCutoff
              P L Klarge Q depth cell) phi)) x := by
  rw [cmp99Eq389SignedCutoffLaplacianRegionalCorrection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    finitePiLpScalarMultiplier_apply]
  exact
    (cmp99CutoffLaplacianCorrection_one_eq_sourceSeparatedSignedCoefficient
      (L := L) (K := Klarge) P depth cell _ x).symm

/-- The second displayed species of CMP99 (3.89) retains its exact
`Klarge⁻²` gain before the source-overlap sum. -/
theorem
    cmp99Eq389SignedCutoffLaplacianRegionalCorrection_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U 1 A c hc hAcoer
      B0 delta0 (L ^ (depth + 1) : ℝ)) :
    FinitePiLpExponentialKernelBound
      (cmp99Eq389SignedCutoffLaplacianRegionalCorrection
        P depth cell Omega A c hc hAcoer)
      (cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q)
      (cmp99Eq389SignedCutoffLaplacianSourceBudget P B0 Klarge) delta0 := by
  let hcutoff : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)) → ℝ :=
    cmp99SourceSeparatedSignedLargeBlockCutoff P L Klarge Q depth cell
  let coefficient : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)) → ℝ :=
    cmp99SourceSeparatedSignedCutoffLaplacianCoefficient
      (L := L) (K := Klarge) P depth cell
  let beta : ℝ := (48 * P.secondDerivBound) /
    cmp99SourceSeparatedLargeBlockCutoffScale L Klarge depth ^ 2
  have hbeta : 0 ≤ beta := by
    dsimp [beta]
    exact div_nonneg
      (mul_nonneg (by norm_num) P.secondDerivBound_nonneg) (sq_nonneg _)
  have hcutoff_le : ∀ source, ‖hcutoff source‖ ≤ 1 := by
    intro source
    exact
      (cmp99SourceSeparatedSignedLargeBlockSquarePartition
        (L := L) (K := Klarge) (Q := Q) (depth := depth) P).norm_value_le_one
          cell source
  have hgreen := C.extended_value_bound Omega rho U 1 A c hc hAcoer
    B0 delta0 (L ^ (depth + 1) : ℝ)
  have hgreenCut :=
    finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
      hcutoff (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer)
      hcutoff_le hgreen
  refine ⟨?_, C.delta0_pos, ?_⟩
  · unfold cmp99Eq389SignedCutoffLaplacianSourceBudget
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) C.B0_nonneg) P.secondDerivBound_nonneg)
      (sq_nonneg _)
  · intro source target v
    change ‖coefficient target •
      ((cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer).comp
        (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) hcutoff))
          (singleFinitePiLp source v) target‖ ≤ _
    rw [norm_smul]
    calc
      ‖coefficient target‖ *
          ‖((cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer).comp
            (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) hcutoff))
              (singleFinitePiLp source v) target‖ ≤
          beta * ((B0 * (L ^ (depth + 1) : ℝ) ^ 2) *
            Real.exp (-(delta0 *
              (cmp99Eq342RescaledBlockDist
                (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q
                target source : ℝ))) * ‖v‖) := by
        apply mul_le_mul
        · exact norm_cmp99SourceSeparatedSignedCutoffLaplacianCoefficient_le
            (L := L) (K := Klarge) P depth cell target
        · exact hgreenCut.2.2 source target v
        · exact norm_nonneg _
        · exact hbeta
      _ = cmp99Eq389SignedCutoffLaplacianSourceBudget P B0 Klarge *
          Real.exp (-(delta0 *
            (cmp99Eq342RescaledBlockDist
              (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q
              target source : ℝ))) * ‖v‖ := by
        rw [show beta * (B0 * (L ^ (depth + 1) : ℝ) ^ 2) =
            B0 * (beta * (L ^ (depth + 1) : ℝ) ^ 2) by ring,
          cmp99SourceSeparatedSignedCutoffLaplacianBudget_mul_range_sq]
        unfold cmp99Eq389SignedCutoffLaplacianSourceBudget
        ring

/-- A zero right signed cutoff kills the isolated second-species cell on a
one-site source probe. -/
theorem
    cmp99Eq389SignedCutoffLaplacianRegionalCorrection_single_eq_zero_of_value_eq_zero
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (source : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)))
    (v : SUNLieCoord Nc)
    (hzero : cmp99SourceSeparatedSignedLargeBlockCutoff
      P L Klarge Q depth cell source = 0) :
    cmp99Eq389SignedCutoffLaplacianRegionalCorrection
      P depth cell Omega A c hc hAcoer (singleFinitePiLp source v) = 0 := by
  unfold cmp99Eq389SignedCutoffLaplacianRegionalCorrection
  rw [ContinuousLinearMap.comp_apply, finitePiLpScalarMultiplier_single,
    hzero, zero_smul]
  have hsingle : singleFinitePiLp source (0 : SUNLieCoord Nc) = 0 := by
    apply PiLp.ext
    intro target
    by_cases htarget : target = source
    · subst target
      simp
    · rw [singleFinitePiLp_of_ne (0 : SUNLieCoord Nc) htarget]
      rfl
  rw [hsingle, map_zero, map_zero]

/-- Sum of all signed cutoff-Laplacian regional cells. -/
noncomputable def cmp99Eq389SignedCutoffLaplacianRegionalDefect
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c) :=
  ∑ cell, cmp99Eq389SignedCutoffLaplacianRegionalCorrection
    P depth cell (Omega cell) A c hc hAcoer

/-- The second species pays exactly the signed source overlap `16`, with no
dependence on the number of regional cells. -/
theorem cmp99Eq389SignedCutoffLaplacianRegionalDefect_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ)
    (C : ∀ cell, CMP99Eq342RegionalGreenCertificate (Omega cell) rho U 1
      A c hc hAcoer B0 delta0 (L ^ (depth + 1) : ℝ)) :
    FinitePiLpExponentialKernelBound
      (cmp99Eq389SignedCutoffLaplacianRegionalDefect
        P depth Omega A c hc hAcoer)
      (cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q)
      (16 * cmp99Eq389SignedCutoffLaplacianSourceBudget P B0 Klarge)
      delta0 := by
  unfold cmp99Eq389SignedCutoffLaplacianRegionalDefect
  apply finitePiLpExponentialKernelBound_sum_of_sourceOverlap
    (term := fun cell => cmp99Eq389SignedCutoffLaplacianRegionalCorrection
      P depth cell (Omega cell) A c hc hAcoer)
    (active := fun cell source =>
      cmp99SourceSeparatedSignedLargeBlockCutoff
        P L Klarge Q depth cell source ≠ 0)
    (dist := cmp99Eq342RescaledBlockDist
      (cmp99SourceSeparatedLargeBlockSide L Klarge depth) Q)
    (N := 16)
  · unfold cmp99Eq389SignedCutoffLaplacianSourceBudget
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (C default).B0_nonneg)
          P.secondDerivBound_nonneg)
      (sq_nonneg _)
  · exact (C default).delta0_pos
  · intro source
    simpa [cmp99SourceSeparatedSignedLargeBlockActiveCells] using
      card_cmp99SourceSeparatedSignedLargeBlockActiveCells_le_sixteen
        P L Klarge Q depth source
  · intro cell source v hinactive
    apply
      cmp99Eq389SignedCutoffLaplacianRegionalCorrection_single_eq_zero_of_value_eq_zero
        P depth cell (Omega cell) A c hc hAcoer source v
    simpa using hinactive
  · intro cell
    exact
      cmp99Eq389SignedCutoffLaplacianRegionalCorrection_exponentialKernelBound
        P depth cell (Omega cell) rho U A c hc hAcoer B0 delta0 (C cell)

end

end YangMills.RG
