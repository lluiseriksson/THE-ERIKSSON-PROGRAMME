/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389GeneratedMassAmbientInsertion
import YangMills.RG.BalabanCMP99SourceGeneratedQprimeMassCutoffIdentity
import YangMills.RG.BalabanCMP99SourceSeparatedSignedLargeBlockPartition
import YangMills.RG.FinitePiLpSourceOverlapSum

/-!
# PRE-VALIDATION: complete generated-mass species in CMP99 (3.89)

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

This file sums the sealed ambient generated-mass atoms to the literal scalar
commutator, inserts the contractive right signed cutoff, and sums the regional
cells with the already sealed overlap `16`.  The physical scalar mass, the
one surviving normalized block-average weight, and the inverse-`K` cutoff
gain remain separate in the displayed budget.

No combination with the two covariant-Laplacian species, full CMP99 (3.89)
bound, defect contraction, or attainment of window 15 is claimed here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389MassPhysicalBlockSide
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth) :=
  ⟨by
    unfold cmp99SourceSeparatedLargeBlockSide
    exact (Nat.mul_pos (NeZero.pos K)
      (pow_pos (NeZero.pos L) (depth + 1))).ne'⟩

private instance instNeZeroEq389MassPhysicalAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K)
      (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- Algebraic kernel expansion used by the physical third species.  It is
kept generic so specializing the generated tower does not ask elaboration to
reduce that tower merely to expose linearity. -/
theorem finitePiLpScalarCommutator_smul_comp_single_apply_eq_sum
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) (mass : ℝ)
    (T G : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (probe target : ι) (v : g) :
    ((finitePiLpScalarCommutator h (mass • T)).comp G)
        (singleFinitePiLp probe v) target =
      ∑ source, (-mass) • T (singleFinitePiLp source
        ((h source - h target) •
          G (singleFinitePiLp probe v) source)) target := by
  rw [ContinuousLinearMap.comp_apply,
    finitePiLpScalarCommutator_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro source _hsource
  have hsingle :
      singleFinitePiLp source
          ((h source - h target) •
            G (singleFinitePiLp probe v) source) =
        (h source - h target) •
          singleFinitePiLp source (G (singleFinitePiLp probe v) source) := by
    apply PiLp.ext
    intro x
    by_cases hx : x = source
    · subst x
      simp
    · rw [singleFinitePiLp_of_ne _ hx, PiLp.smul_apply,
        singleFinitePiLp_of_ne _ hx, smul_zero]
  rw [hsingle, map_smul]
  simp only [ContinuousLinearMap.smul_apply, PiLp.smul_apply]
  module

/-- Pre-overlap amplitude of the complete generated-mass species.  The
literal physical mass and the one surviving normalized counting-mass weight
are intentionally not absorbed into a shared constant. -/
noncomputable def cmp99Eq389GeneratedMassSourceBudget
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (spacing epsilon B0 ell : ℝ) : ℝ :=
  |cmp99SourceGeneratedPhysicalMass 4 L (depth + 1) spacing epsilon| *
    ((cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) *
      (((8 * P.derivBound) / (K : ℝ)) * (B0 * ell ^ 2)))

/-- The ambient third-species operator before the right cutoff.  It is the
literal commutator of the signed cutoff with the physical generated mass,
followed by the canonical regional Dirichlet Green. -/
noncomputable def cmp99Eq389GeneratedMassAmbientCorrection
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  let h := cmp99SourceSeparatedSignedLargeBlockCutoff
    P L K Q depth cell
  let mass := cmp99SourceGeneratedPhysicalMass
    4 L (depth + 1) spacing epsilon
  let T := cmp99SourceSeparatedGeneratedCountingMass
    (L := L) (K := K) (Q := Q) hL depth (matrixSUNAdjointModel Nc)
    spacing epsilon background chain fineSmall
  (finitePiLpScalarCommutator h (mass • T)).comp
    (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer)

/-- The ambient commutator is exactly the sum of the sealed physical kernel
atoms.  Thus the estimate below is attached to the literal operator rather
than to a separately chosen majorant. -/
theorem cmp99Eq389GeneratedMassAmbientCorrection_apply_eq_sum
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (probe target : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc) :
    cmp99Eq389GeneratedMassAmbientCorrection
        (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
        chain fineSmall cell Omega A c hc hAcoer
        (singleFinitePiLp probe v) target =
      ∑ source, cmp99Eq389GeneratedMassAmbientKernelAtom
        (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
        chain fineSmall cell Omega A c hc hAcoer target probe source v := by
  rw [cmp99Eq389GeneratedMassAmbientCorrection,
    finitePiLpScalarCommutator_smul_comp_single_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro source _hsource
  unfold cmp99Eq389GeneratedMassAmbientKernelAtom
  rfl

/-- Before the right cutoff, the literal generated-mass commutator has the
printed common metric and the explicit physical source budget. -/
theorem cmp99Eq389GeneratedMassAmbientCorrection_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 ell : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega (matrixSUNAdjointModel Nc)
      U spacing A c hc hAcoer B0 delta0 ell) :
    FinitePiLpTypedExponentialKernelBound
      (ι := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (κ := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (g := SUNLieCoord Nc)
      (cmp99Eq389GeneratedMassAmbientCorrection
        (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
        chain fineSmall cell Omega A c hc hAcoer)
      (cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L K depth) Q)
      (cmp99Eq389GeneratedMassSourceBudget
        (L := L) (K := K) P depth spacing epsilon B0 ell) delta0 := by
  refine ⟨?_, C.delta0_pos, ?_⟩
  · unfold cmp99Eq389GeneratedMassSourceBudget
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg
        (pow_nonneg (cmp99SourceBlockAverageWeight_nonneg L 4) _)
        (mul_nonneg
          (div_nonneg
            (mul_nonneg (by positivity) P.derivBound_nonneg)
            (Nat.cast_nonneg K))
          (mul_nonneg C.B0_nonneg (sq_nonneg ell))))
  · intro probe target v
    rw [cmp99Eq389GeneratedMassAmbientCorrection_apply_eq_sum]
    calc
      ‖∑ source, cmp99Eq389GeneratedMassAmbientKernelAtom
          (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
          chain fineSmall cell Omega A c hc hAcoer target probe source v‖ ≤
          ∑ source, ‖cmp99Eq389GeneratedMassAmbientKernelAtom
            (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
            chain fineSmall cell Omega A c hc hAcoer target probe source v‖ :=
        norm_sum_le _ _
      _ ≤ |cmp99SourceGeneratedPhysicalMass 4 L (depth + 1)
            spacing epsilon| *
          ((cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) *
            (((8 * P.derivBound) / (K : ℝ)) *
              ((B0 * ell ^ 2) * Real.exp (-(delta0 *
                (cmp99Eq342RescaledBlockDist
                  (cmp99SourceSeparatedLargeBlockSide L K depth) Q
                  target probe : ℝ))) * ‖v‖))) :=
        cmp99Eq389GeneratedMassAmbientKernelAtom_sum_norm_le
          (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
          chain fineSmall cell Omega U A c hc hAcoer B0 delta0 ell C
          target probe v
      _ = cmp99Eq389GeneratedMassSourceBudget
            (L := L) (K := K) P depth spacing epsilon B0 ell *
          Real.exp (-(delta0 *
            (cmp99Eq342RescaledBlockDist
              (cmp99SourceSeparatedLargeBlockSide L K depth) Q
              target probe : ℝ))) * ‖v‖ := by
        unfold cmp99Eq389GeneratedMassSourceBudget
        ring

/-- One complete third-species cell, with the right signed cutoff acting on
the source before the regional Green. -/
noncomputable def cmp99Eq389GeneratedMassRegionalCorrection
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  (cmp99Eq389GeneratedMassAmbientCorrection
      (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
      chain fineSmall cell Omega A c hc hAcoer).comp
    (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
      (cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell))

/-- The contractive right cutoff preserves the complete third-species
amplitude and rate. -/
theorem cmp99Eq389GeneratedMassRegionalCorrection_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 ell : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega (matrixSUNAdjointModel Nc)
      U spacing A c hc hAcoer B0 delta0 ell) :
    FinitePiLpTypedExponentialKernelBound
      (ι := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (κ := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (g := SUNLieCoord Nc)
      (cmp99Eq389GeneratedMassRegionalCorrection
        (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
        chain fineSmall cell Omega A c hc hAcoer)
      (cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L K depth) Q)
      (cmp99Eq389GeneratedMassSourceBudget
        (L := L) (K := K) P depth spacing epsilon B0 ell) delta0 := by
  exact finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
    (ι := FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (κ := FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (g := SUNLieCoord Nc)
    (cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell)
    (cmp99Eq389GeneratedMassAmbientCorrection
      (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
      chain fineSmall cell Omega A c hc hAcoer)
    (fun source =>
      (cmp99SourceSeparatedSignedLargeBlockSquarePartition
        (L := L) (K := K) (Q := Q) (depth := depth) P).norm_value_le_one
          cell source)
    (cmp99Eq389GeneratedMassAmbientCorrection_exponentialKernelBound
      (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
      chain fineSmall cell Omega U A c hc hAcoer B0 delta0 ell C)

/-- A zero right signed cutoff kills one complete third-species cell on a
one-site source probe. -/
theorem
    cmp99Eq389GeneratedMassRegionalCorrection_single_eq_zero_of_value_eq_zero
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (source : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc)
    (hzero : cmp99SourceSeparatedSignedLargeBlockCutoff
      P L K Q depth cell source = 0) :
    cmp99Eq389GeneratedMassRegionalCorrection
      (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
      chain fineSmall cell Omega A c hc hAcoer
      (singleFinitePiLp source v) = 0 := by
  unfold cmp99Eq389GeneratedMassRegionalCorrection
  rw [ContinuousLinearMap.comp_apply,
    finitePiLpScalarMultiplier_single, hzero, zero_smul]
  have hsingle : singleFinitePiLp source (0 : SUNLieCoord Nc) = 0 := by
    apply PiLp.ext
    intro target
    by_cases htarget : target = source
    · subst target
      simp
    · rw [singleFinitePiLp_of_ne (0 : SUNLieCoord Nc) htarget]
      rfl
  rw [hsingle, map_zero]

/-- Sum of all complete generated-mass regional cells. -/
noncomputable def cmp99Eq389GeneratedMassRegionalDefect
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c) :=
  ∑ cell, cmp99Eq389GeneratedMassRegionalCorrection
    (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
    chain fineSmall cell (Omega cell) A c hc hAcoer

/-- The complete generated-mass species pays exactly the existing signed
source overlap `16`, independently of the total number of regional cells. -/
theorem cmp99Eq389GeneratedMassRegionalDefect_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 ell : ℝ)
    (C : ∀ cell, CMP99Eq342RegionalGreenCertificate (Omega cell)
      (matrixSUNAdjointModel Nc) U spacing A c hc hAcoer B0 delta0 ell) :
    FinitePiLpTypedExponentialKernelBound
      (ι := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (κ := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (g := SUNLieCoord Nc)
      (cmp99Eq389GeneratedMassRegionalDefect
        (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
        chain fineSmall Omega A c hc hAcoer)
      (cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L K depth) Q)
      (16 * cmp99Eq389GeneratedMassSourceBudget
        (L := L) (K := K) P depth spacing epsilon B0 ell) delta0 := by
  unfold cmp99Eq389GeneratedMassRegionalDefect
  apply finitePiLpExponentialKernelBound_sum_of_sourceOverlap
    (ι := FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (g := SUNLieCoord Nc) (n := FinBox 4 Q)
    (term := fun cell => cmp99Eq389GeneratedMassRegionalCorrection
      (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
      chain fineSmall cell (Omega cell) A c hc hAcoer)
    (active := fun cell source =>
      cmp99SourceSeparatedSignedLargeBlockCutoff
        P L K Q depth cell source ≠ 0)
    (dist := cmp99Eq342RescaledBlockDist
      (cmp99SourceSeparatedLargeBlockSide L K depth) Q)
    (N := 16)
  · unfold cmp99Eq389GeneratedMassSourceBudget
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg
        (pow_nonneg (cmp99SourceBlockAverageWeight_nonneg L 4) _)
        (mul_nonneg
          (div_nonneg
            (mul_nonneg (by positivity) P.derivBound_nonneg)
            (Nat.cast_nonneg K))
          (mul_nonneg (C default).B0_nonneg (sq_nonneg ell))))
  · exact (C default).delta0_pos
  · intro source
    simpa [cmp99SourceSeparatedSignedLargeBlockActiveCells] using
      card_cmp99SourceSeparatedSignedLargeBlockActiveCells_le_sixteen
        P L K Q depth source
  · intro cell source v hinactive
    apply
      cmp99Eq389GeneratedMassRegionalCorrection_single_eq_zero_of_value_eq_zero
        (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
        chain fineSmall cell (Omega cell) A c hc hAcoer source v
    simpa using hinactive
  · intro cell
    exact
      cmp99Eq389GeneratedMassRegionalCorrection_exponentialKernelBound
        (L := L) (K := K) (Q := Q) P hL depth spacing epsilon background
        chain fineSmall cell (Omega cell) U A c hc hAcoer B0 delta0 ell
        (C cell)

end

end YangMills.RG
