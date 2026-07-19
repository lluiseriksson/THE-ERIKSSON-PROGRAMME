/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99CoarseDerivativeRegionalScaled

/-!
# Source-generated regions and multiscale scaled-gradient energy

The regional CMP99 induction must not compare fields by a posteriori casts.
This module therefore stores the literal typed transition
`Omega_(r+1) = cmp99ActiveCoarseRegion Omega_r` in an inductive chain.  Its
only canonical producer uses the iterated lifted source region and proves
block saturation at every positive depth.

On that chain, the scaled-gradient energy is defined recursively from the
physical `Ubar` background and the literal regional average.  No family of
regions, backgrounds, gradients, or transition estimates is a caller input
to the canonical endpoint.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- A typed chain of literal source regions.  The successor constructor fixes
the next region to the actual active coarse region, rather than accepting an
independent region plus an equality certificate. -/
inductive CMP99SourceActiveRegionChain (d M : ℕ) [NeZero M] :
    (N : ℕ) → ActiveGaugeRegion d N → ℕ → Type
  | stop {N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N) :
      CMP99SourceActiveRegionChain d M N Omega 0
  | step {N' depth : ℕ} [NeZero N']
      (Omega : ActiveGaugeRegion d (M * N'))
      (blockSaturated : Omega.BlockSaturated)
      (tail : CMP99SourceActiveRegionChain d M N'
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth) :
      CMP99SourceActiveRegionChain d M (M * N') Omega (depth + 1)

/-- The lattice nondegeneracy carried by every typed region chain. -/
@[reducible] def CMP99SourceActiveRegionChain.neZero
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) : NeZero N := by
  cases regions <;> infer_instance

/-- The source lift generates the complete typed region chain.  This is the
canonical A1--A2 producer. -/
noncomputable def cmp99SourceIteratedLiftActiveRegionChain
    (Omega : ActiveGaugeRegion d N) :
    ∀ depth : ℕ,
      CMP99SourceActiveRegionChain d M
        (cmp99RegionalLatticeSize M N depth)
        (cmp99IteratedLiftActiveRegion (M := M) Omega depth) depth
  | 0 => .stop Omega
  | depth + 1 => .step
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
      (by
        rw [cmp99ActiveCoarseRegion_iteratedLift_succ_eq
          (M := M) Omega depth]
        exact cmp99SourceIteratedLiftActiveRegionChain Omega depth)

/-- The literal additive error in the scale-correct one-step derivative
recurrence. -/
noncomputable def cmp99SourceScaledGradientStepError
    (d M : ℕ) (epsilon spacing : ℝ) : ℝ :=
  2 * cmp99SourceBlockAverageWeight M d *
      (2 * (cmp99SourceTripleHolonomyRadius d M epsilon +
        cmp99SourceUbarNextFineRadius d M epsilon)) ^ 2 * (d : ℝ) /
    (((M : ℝ) * spacing) ^ 2)

/-- The squared scaled-gradient energy at every prefix of one typed physical
region chain.  The successor branch constructs `Ubar` and the next field from
the strongest normalized source scale. -/
noncomputable def CMP99SourceActiveRegionChain.scaledGradientEnergy
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) → (background : GaugeConfig d N (SUN Nc)) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    Fin (depth + 1) → ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) → ℝ := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall
  induction regions generalizing spacing epsilon with
  | stop Omega =>
      intro _r phi
      exact ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
        (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
          hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      let coarsePhi := cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport
          (matrixSUNAdjointModel Nc) background)
      intro r phi
      exact Fin.cases
        (‖cmp99ActiveRegionSourceCovariantD0CLM Omega
          (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2)
        (fun s => ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall s
          (coarsePhi phi)) r

/-- At every depth, the zeroth generated energy is literally the physical
fine scaled covariant derivative. -/
theorem CMP99SourceActiveRegionChain.scaledGradientEnergy_zero
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (spacing epsilon : ℝ) :
    letI : NeZero N := regions.neZero
    ∀
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)),
    regions.scaledGradientEnergy hd hM spacing epsilon background chain
        fineSmall 0 phi =
      ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
        (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2 := by
  letI : NeZero N := regions.neZero
  intro background chain fineSmall phi
  induction regions <;> rfl

/-- The first transition of every physical region chain consumes the
scale-correct `Ubar` estimate.  The coarse background and its small-field
certificate are both generated internally. -/
theorem CMP99SourceActiveRegionChain.scaledGradientEnergy_one_le
    {N' depth : ℕ} [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (tail : CMP99SourceActiveRegionChain d M N'
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    let regions := CMP99SourceActiveRegionChain.step Omega hOmega tail
    regions.scaledGradientEnergy hd hM spacing epsilon background chain
        fineSmall ⟨1, by omega⟩ phi ≤
      2 * cmp99SourceBlockAverageWeight M d *
          regions.scaledGradientEnergy hd hM spacing epsilon background chain
            fineSmall 0 phi +
        cmp99SourceScaledGradientStepError d M epsilon spacing * ‖phi‖ ^ 2 := by
  dsimp only
  have h :=
    norm_scaledCovariantD0_cmp99SourceRegionalAverage_physicalUbar_sq_le
      hd hM Omega hOmega background (cmp99SourceBlockAverageWeight M d)
      epsilon spacing chain.epsilon_nonneg hspacing chain.head_noWinding
      chain.head_logSmall fineSmall phi
  let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
    CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
      hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
  have nextSmall : ∀ e : ConcreteEdge d N',
      ‖(Scale.toSourceScale.data.nextBackground e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99SourceUbarNextFineRadius d M epsilon := by
    intro e
    simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
      CMP99SourceRegionalScale.ofFineSmall] using
      norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
        hd hM Omega background (cmp99SourceBlockAverageWeight M d)
        epsilon chain.epsilon_nonneg chain.head_noWinding
        chain.head_logSmall fineSmall e
  let coarsePhi := cmp99SourceTransportedBlockAverageCLM Omega
    (cmp99SourceWeightedPhysicalTransport
      (matrixSUNAdjointModel Nc) background) phi
  change tail.scaledGradientEnergy hd hM ((M : ℝ) * spacing)
      (cmp99SourceUbarNextFineRadius d M epsilon)
      Scale.toSourceScale.data.nextBackground chain.tail nextSmall 0
      coarsePhi ≤
    2 * cmp99SourceBlockAverageWeight M d *
      (CMP99SourceActiveRegionChain.step Omega hOmega tail).scaledGradientEnergy
        hd hM spacing epsilon background chain fineSmall 0 phi +
      cmp99SourceScaledGradientStepError d M epsilon spacing * ‖phi‖ ^ 2
  rw [tail.scaledGradientEnergy_zero,
    (CMP99SourceActiveRegionChain.step Omega hOmega tail).scaledGradientEnergy_zero]
  simpa [cmp99SourceScaledGradientStepError, Scale,
    CMP99SourceNormalizedRegionalScale.ofFineSmall,
    CMP99SourceRegionalScale.ofFineSmall, coarsePhi] using h

/-- Canonical source specialization of the first scale-correct recurrence.
No region chain or saturation proof is exposed. -/
theorem cmp99SourceIteratedLift_scaledGradientEnergy_one_le
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (phi : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      (SUNLieCoord Nc)) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    regions.scaledGradientEnergy hd hM spacing epsilon background chain
        fineSmall ⟨1, by omega⟩ phi ≤
      2 * cmp99SourceBlockAverageWeight M d *
          regions.scaledGradientEnergy hd hM spacing epsilon background chain
            fineSmall 0 phi +
        cmp99SourceScaledGradientStepError d M epsilon spacing * ‖phi‖ ^ 2 := by
  dsimp only
  let fineOmega :=
    cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let tail : CMP99SourceActiveRegionChain d M
      (cmp99RegionalLatticeSize M N depth)
      (cmp99ActiveCoarseRegion
        (M := M) (N' := cmp99RegionalLatticeSize M N depth) fineOmega) depth := by
    rw [show cmp99ActiveCoarseRegion
        (M := M) (N' := cmp99RegionalLatticeSize M N depth) fineOmega =
      cmp99IteratedLiftActiveRegion (M := M) Omega depth by
        simpa [fineOmega] using
          cmp99ActiveCoarseRegion_iteratedLift_succ_eq (M := M) Omega depth]
    exact cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  simpa [cmp99SourceIteratedLiftActiveRegionChain, fineOmega, tail] using
    CMP99SourceActiveRegionChain.scaledGradientEnergy_one_le
      fineOmega (cmp99IteratedLiftActiveRegion_blockSaturated Omega depth)
      tail hd hM hspacing background chain fineSmall phi

end

end YangMills.RG
