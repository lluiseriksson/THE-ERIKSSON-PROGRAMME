/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389GeneratedMassPhysicalBound
import YangMills.RG.BalabanCMP99Eq389SignedCovariantLinkPhysicalBound
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary

/-!
# PRE-VALIDATION: literal three-species CMP99 (3.89) assembly

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

This module adds the three separately sealed displayed species only after
specializing all of them to the same source-generated physical data.  The
differential background is the dependent cast of the fine `background`, the
precision and coercivity are constructed internally from that same
background, and every regional Green certificate uses rescaled spacing `1`
and scale `L^(depth+1)`.

Thus the endpoint is not an abstract sum with an independently supplied `U`,
precision, coercivity or family of unrelated Green operators.  The three
budgets remain visibly separate.  No contraction, complete Neumann inverse,
rows 23--24, window-15 attainment or `TermSource` inhabitant is claimed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389ThreeSpeciesAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- The one differential background used by every species: the same fine
background transported across the printed carrier equality. -/
noncomputable def cmp99Eq389SourceSeparatedPhysicalBackground
    (L K Q depth Nc : ℕ) [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc)) :
    PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc :=
  let hsize :=
    cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth
  { toFun := fun edge => background
      { source := hsize.symm ▸ edge.source
        dir := edge.dir
        sign := edge.sign }
    map_reverse := by
      intro edge
      cases edge with
      | mk source dir sign =>
          exact background.map_reverse
            { source := hsize.symm ▸ source
              dir := dir
              sign := sign } }

/-- The literal generated precision on the separated ambient carrier. -/
noncomputable def cmp99Eq389SourceSeparatedPhysicalPrecision
    (hL : 2 ≤ L) (depth : ℕ) (epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    (spacing := 1) (epsilon := epsilon)
    hL depth background budget fineSmall

/-- The physical coercivity constant paired with the generated precision at
the source-required rescaled spacing `1`. -/
noncomputable def cmp99Eq389SourceSeparatedPhysicalCoercivity
    (L depth : ℕ) (epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedCoercivity 4 L (depth + 1) 1 epsilon

theorem cmp99Eq389SourceSeparatedPhysicalCoercivity_pos
    (depth : ℕ) {epsilon : ℝ}
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1) :
    0 < cmp99Eq389SourceSeparatedPhysicalCoercivity L depth epsilon := by
  exact cmp99SourceGeneratedCoercivity_pos 4 L depth (by norm_num) hsmall

theorem isCoerciveCLM_cmp99Eq389SourceSeparatedPhysicalPrecision
    (hL : 2 ≤ L) (depth : ℕ) {epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1) :
    IsCoerciveCLM
      (cmp99Eq389SourceSeparatedPhysicalPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        hL depth epsilon background budget fineSmall)
      (cmp99Eq389SourceSeparatedPhysicalCoercivity L depth epsilon) := by
  exact isCoerciveCLM_cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    (spacing := 1) (epsilon := epsilon)
    hL depth (by norm_num) background budget fineSmall hsmall

/-- Literal sum of the three displayed CMP99 (3.88)--(3.89) regional
species, all specialized to one fine background and its generated precision.
-/
noncomputable def cmp99Eq389ThreeSpeciesPhysicalRegionalDefect
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  let U := cmp99Eq389SourceSeparatedPhysicalBackground
    L K Q depth Nc background
  let A := cmp99Eq389SourceSeparatedPhysicalPrecision
    hL depth epsilon background budget fineSmall
  let c := cmp99Eq389SourceSeparatedPhysicalCoercivity L depth epsilon
  let hc := cmp99Eq389SourceSeparatedPhysicalCoercivity_pos
    (L := L) depth hsmall
  let hAcoer := isCoerciveCLM_cmp99Eq389SourceSeparatedPhysicalPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth background budget fineSmall hsmall
  cmp99Eq389SignedCovariantLinkRegionalDefect
      (L := L) (K := K) (Q := Q) P depth Omega
      (matrixSUNAdjointModel Nc) U A c hc hAcoer +
    cmp99Eq389SignedCutoffLaplacianRegionalDefect
      (L := L) (Klarge := K) (Q := Q) (Nc := Nc)
      P depth Omega A c hc hAcoer +
    cmp99Eq389GeneratedMassRegionalDefect
      (L := L) (K := K) (Q := Q) P hL depth 1 epsilon background
      budget.toRadiusChain fineSmall Omega A c hc hAcoer

/-- The physical three-species budget keeps each printed mechanism visible;
no common constant is introduced before the contraction step. -/
noncomputable def cmp99Eq389ThreeSpeciesPhysicalSourceBudget
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (epsilon B0 delta0 : ℝ) : ℝ :=
  16 * cmp99Eq389SignedCovariantLinkSourceBudget P B0
      delta0 K +
    16 * cmp99Eq389SignedCutoffLaplacianSourceBudget P B0 K +
    16 * cmp99Eq389GeneratedMassSourceBudget
      (L := L) (K := K) P depth 1 epsilon B0 (L ^ (depth + 1) : ℝ)

/-- One family of regional Green certificates shared by all three species.
The background, precision, coercivity, spacing and scale are fixed by the
physical producer rather than chosen independently by the caller. -/
abbrev CMP99Eq389ThreeSpeciesPhysicalGreenCertificates
    (hL : 2 ≤ L) (depth : ℕ) (epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (B0 delta0 : ℝ) : Prop :=
  ∀ cell, CMP99Eq342RegionalGreenCertificate (Omega cell)
    (matrixSUNAdjointModel Nc)
    (cmp99Eq389SourceSeparatedPhysicalBackground L K Q depth Nc background)
    1
    (cmp99Eq389SourceSeparatedPhysicalPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth epsilon background budget fineSmall)
    (cmp99Eq389SourceSeparatedPhysicalCoercivity L depth epsilon)
    (cmp99Eq389SourceSeparatedPhysicalCoercivity_pos
      (L := L) depth hsmall)
    (isCoerciveCLM_cmp99Eq389SourceSeparatedPhysicalPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth background budget fineSmall hsmall)
    B0 delta0 (L ^ (depth + 1) : ℝ)

/-- The literal sum of the three physical species has the sum of their three
separate source budgets at the one common CMP99 (3.42) rate. -/
theorem cmp99Eq389ThreeSpeciesPhysicalRegionalDefect_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    {epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (B0 delta0 : ℝ)
    (C : CMP99Eq389ThreeSpeciesPhysicalGreenCertificates
      hL depth epsilon background budget fineSmall hsmall Omega B0 delta0) :
    FinitePiLpTypedExponentialKernelBound
      (ι := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (κ := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (g := SUNLieCoord Nc)
      (cmp99Eq389ThreeSpeciesPhysicalRegionalDefect
        (L := L) (K := K) (Q := Q) P hL depth epsilon background budget
        fineSmall hsmall Omega)
      (cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L K depth) Q)
      (cmp99Eq389ThreeSpeciesPhysicalSourceBudget
        (L := L) (K := K) P depth epsilon B0 delta0)
      delta0 := by
  let A := cmp99Eq389SourceSeparatedPhysicalPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth epsilon background budget fineSmall
  let c := cmp99Eq389SourceSeparatedPhysicalCoercivity L depth epsilon
  let hc := cmp99Eq389SourceSeparatedPhysicalCoercivity_pos
    (L := L) depth hsmall
  let hAcoer := isCoerciveCLM_cmp99Eq389SourceSeparatedPhysicalPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth background budget fineSmall hsmall
  let U := cmp99Eq389SourceSeparatedPhysicalBackground
    L K Q depth Nc background
  have hfirst :=
    cmp99Eq389SignedCovariantLinkRegionalDefect_exponentialKernelBound
      (L := L) (K := K) (Q := Q) P depth Omega
      (matrixSUNAdjointModel Nc) U A c hc hAcoer B0 delta0 C
  have hsecond :=
    cmp99Eq389SignedCutoffLaplacianRegionalDefect_exponentialKernelBound
      (L := L) (Klarge := K) (Q := Q) (Nc := Nc)
      P depth Omega (matrixSUNAdjointModel Nc) U A c hc hAcoer B0 delta0 C
  have hthird :=
    cmp99Eq389GeneratedMassRegionalDefect_exponentialKernelBound
      (L := L) (K := K) (Q := Q) P hL depth 1 epsilon background
      budget.toRadiusChain fineSmall Omega U A c hc hAcoer
      B0 delta0 (L ^ (depth + 1) : ℝ) C
  dsimp [cmp99Eq389ThreeSpeciesPhysicalRegionalDefect,
    cmp99Eq389ThreeSpeciesPhysicalSourceBudget]
  exact finitePiLpTypedExponentialKernelBound_add
    (finitePiLpTypedExponentialKernelBound_add hfirst hsecond) hthird

end

end YangMills.RG
