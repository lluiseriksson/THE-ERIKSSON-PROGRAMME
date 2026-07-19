/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedScaledGradient

/-!
# Iterated source-generated scaled-gradient recurrence

This module iterates the physical one-step derivative estimate along the
typed source region chain.  The error ledger is generated recursively from
the literal error at each scale and the exact regional-average contraction;
it is not supplied as an external sequence.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

theorem cmp99SourceBlockAverageWeight_nonneg (M d : ℕ) :
    0 ≤ cmp99SourceBlockAverageWeight M d := by
  simp [cmp99SourceBlockAverageWeight]

theorem cmp99SourceScaledGradientStepError_nonneg
    (d M : ℕ) (epsilon spacing : ℝ) :
    0 ≤ cmp99SourceScaledGradientStepError d M epsilon spacing := by
  unfold cmp99SourceScaledGradientStepError
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (cmp99SourceBlockAverageWeight_nonneg M d))
        (sq_nonneg _))
      (Nat.cast_nonneg d))
    (sq_nonneg _)

/-- The source-generated accumulated derivative error.  At a successor
level it contains the head error transported through all later derivative
recurrences and the tail error contracted by the exact average weight. -/
noncomputable def CMP99SourceActiveRegionChain.scaledGradientCost
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) →
    CMP99SourceUbarRadiusChain d M Nc depth epsilon →
    Fin (depth + 1) → ℝ := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon chain
  induction regions generalizing spacing epsilon with
  | stop Omega =>
      intro _r
      exact 0
  | @step N' depth _ Omega hOmega tail ih =>
      intro r
      exact Fin.cases 0 (fun s =>
        (2 * cmp99SourceBlockAverageWeight M d) ^ s.1 *
            cmp99SourceScaledGradientStepError d M epsilon spacing +
          cmp99SourceBlockAverageWeight M d *
            ih ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon) chain.tail s) r

theorem CMP99SourceActiveRegionChain.scaledGradientCost_nonneg
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (spacing epsilon : ℝ)
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (r : Fin (depth + 1)) :
    0 ≤ regions.scaledGradientCost spacing epsilon chain r := by
  induction regions generalizing spacing epsilon with
  | stop Omega =>
      simp [CMP99SourceActiveRegionChain.scaledGradientCost]
  | @step N' depth _ Omega hOmega tail ih =>
      refine Fin.cases ?_ (fun s => ?_) r
      · simp [CMP99SourceActiveRegionChain.scaledGradientCost]
      · change 0 ≤
          (2 * cmp99SourceBlockAverageWeight M d) ^ s.1 *
              cmp99SourceScaledGradientStepError d M epsilon spacing +
            cmp99SourceBlockAverageWeight M d *
              tail.scaledGradientCost ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon) chain.tail s
        exact add_nonneg
          (mul_nonneg
            (pow_nonneg (mul_nonneg (by positivity)
              (cmp99SourceBlockAverageWeight_nonneg M d)) _)
            (cmp99SourceScaledGradientStepError_nonneg d M epsilon spacing))
          (mul_nonneg (cmp99SourceBlockAverageWeight_nonneg M d)
            (ih ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon) chain.tail s))

/-- Every prefix of the source-generated tower satisfies the iterated
scale-correct derivative estimate.  No error sequence, background tower, or
region family is exposed to the caller. -/
theorem CMP99SourceActiveRegionChain.scaledGradientEnergy_le
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    letI : NeZero N := regions.neZero
    ∀ {spacing epsilon : ℝ}, 0 < spacing →
    ∀ (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (r : Fin (depth + 1))
      (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)),
      regions.scaledGradientEnergy hd hM spacing epsilon background chain
          fineSmall r phi ≤
        (2 * cmp99SourceBlockAverageWeight M d) ^ r.1 *
            regions.scaledGradientEnergy hd hM spacing epsilon background chain
              fineSmall 0 phi +
          regions.scaledGradientCost spacing epsilon chain r * ‖phi‖ ^ 2 := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon hspacing background chain fineSmall r phi
      rcases r with ⟨r, hr⟩
      have : r = 0 := by omega
      subst r
      simp [CMP99SourceActiveRegionChain.scaledGradientCost]
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon hspacing background chain fineSmall r phi
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
          (matrixSUNAdjointModel Nc) background) phi
      rcases r with ⟨r, hr⟩
      cases r with
      | zero =>
        simp [CMP99SourceActiveRegionChain.scaledGradientCost]
      | succ s =>
        let sFin : Fin (depth + 1) := ⟨s, by omega⟩
        have htail := ih
          (mul_pos (Nat.cast_pos.mpr (NeZero.pos M)) hspacing)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall sFin coarsePhi
        have hhead :=
          CMP99SourceActiveRegionChain.scaledGradientEnergy_one_le
            Omega hOmega tail hd hM hspacing background chain fineSmall phi
        change tail.scaledGradientEnergy hd hM ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall 0
            coarsePhi ≤
          2 * cmp99SourceBlockAverageWeight M d *
              (CMP99SourceActiveRegionChain.step Omega hOmega tail).scaledGradientEnergy
                hd hM spacing epsilon background chain fineSmall 0 phi +
            cmp99SourceScaledGradientStepError d M epsilon spacing * ‖phi‖ ^ 2
          at hhead
        have havg : ‖coarsePhi‖ ^ 2 ≤
            cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2 := by
          simpa [coarsePhi] using
            norm_cmp99SourceRegionalAverage_sq_le Omega hOmega
              (matrixSUNAdjointModel Nc) background phi
        have hw : 0 ≤ cmp99SourceBlockAverageWeight M d :=
          cmp99SourceBlockAverageWeight_nonneg M d
        have hpow : 0 ≤
            (2 * cmp99SourceBlockAverageWeight M d) ^ sFin.1 :=
          pow_nonneg (mul_nonneg (by positivity) hw) _
        have hcost : 0 ≤ tail.scaledGradientCost
            ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon) chain.tail sFin :=
          tail.scaledGradientCost_nonneg _ _ _ _
        change tail.scaledGradientEnergy hd hM ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall sFin
            coarsePhi ≤ _
        calc
          tail.scaledGradientEnergy hd hM ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              Scale.toSourceScale.data.nextBackground chain.tail nextSmall sFin
              coarsePhi ≤
            (2 * cmp99SourceBlockAverageWeight M d) ^ sFin.1 *
                tail.scaledGradientEnergy hd hM ((M : ℝ) * spacing)
                  (cmp99SourceUbarNextFineRadius d M epsilon)
                  Scale.toSourceScale.data.nextBackground chain.tail nextSmall 0
                  coarsePhi +
              tail.scaledGradientCost ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon) chain.tail sFin *
                  ‖coarsePhi‖ ^ 2 := htail
          _ ≤ (2 * cmp99SourceBlockAverageWeight M d) ^ sFin.1 *
                (2 * cmp99SourceBlockAverageWeight M d *
                    (CMP99SourceActiveRegionChain.step Omega hOmega tail).scaledGradientEnergy
                      hd hM spacing epsilon background chain fineSmall 0 phi +
                  cmp99SourceScaledGradientStepError d M epsilon spacing * ‖phi‖ ^ 2) +
              tail.scaledGradientCost ((M : ℝ) * spacing)
                (cmp99SourceUbarNextFineRadius d M epsilon) chain.tail sFin *
                  (cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2) := by
            gcongr
          _ = (2 * cmp99SourceBlockAverageWeight M d) ^ (sFin.1 + 1) *
                (CMP99SourceActiveRegionChain.step Omega hOmega tail).scaledGradientEnergy
                  hd hM spacing epsilon background chain fineSmall 0 phi +
              ((2 * cmp99SourceBlockAverageWeight M d) ^ sFin.1 *
                  cmp99SourceScaledGradientStepError d M epsilon spacing +
                cmp99SourceBlockAverageWeight M d *
                  tail.scaledGradientCost ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon) chain.tail sFin) *
                ‖phi‖ ^ 2 := by ring
          _ = _ := by
            rfl

/-- Canonical source specialization of the full recurrence.  The region
chain and every block-saturation certificate are generated internally from
the iterated source lift. -/
theorem cmp99SourceIteratedLift_scaledGradientEnergy_le
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (r : Fin (depth + 1))
    (phi : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
      (SUNLieCoord Nc)) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    regions.scaledGradientEnergy hd hM spacing epsilon background chain
        fineSmall r phi ≤
      (2 * cmp99SourceBlockAverageWeight M d) ^ r.1 *
          regions.scaledGradientEnergy hd hM spacing epsilon background chain
            fineSmall 0 phi +
        regions.scaledGradientCost spacing epsilon chain r * ‖phi‖ ^ 2 := by
  dsimp only
  exact CMP99SourceActiveRegionChain.scaledGradientEnergy_le
    (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth)
    hd hM hspacing background chain fineSmall r phi

end

end YangMills.RG
