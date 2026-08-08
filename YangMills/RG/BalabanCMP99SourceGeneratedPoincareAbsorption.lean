/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPoincare

/-!
# Source-generated multiscale Poincare absorption

The scalar ledgers in this module are recursive functions of the literal
source parameters.  They are not caller-supplied sequences.  They separate
the iterated Poincare bound into the fine derivative energy, the accumulated
`Ubar` error multiplying the fine field norm, and the retained terminal
field norm.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Coefficient of the initial scaled derivative energy after iterating the
regional Poincare inequality and the source `Ubar` derivative recurrence. -/
noncomputable def cmp99SourcePoincareEnergyCoeff (d M : ℕ) :
    ℕ → ℝ → ℝ → ℝ
  | 0, _spacing, _epsilon => 0
  | depth + 1, spacing, epsilon =>
      cmp99OneScaleBlockPoincareConstant d M *
        (spacing ^ 2 +
          2 * cmp99SourceBlockAverageWeight M d *
            cmp99SourcePoincareEnergyCoeff d M depth
              ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon))

/-- Coefficient of the fine field norm generated solely by the accumulated
physical `Ubar` derivative errors and average contractions. -/
noncomputable def cmp99SourcePoincareErrorCoeff (d M : ℕ) :
    ℕ → ℝ → ℝ → ℝ
  | 0, _spacing, _epsilon => 0
  | depth + 1, spacing, epsilon =>
      cmp99OneScaleBlockPoincareConstant d M *
        (cmp99SourcePoincareEnergyCoeff d M depth
            ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon) *
              cmp99SourceScaledGradientStepError d M epsilon spacing +
          cmp99SourcePoincareErrorCoeff d M depth
              ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon) *
            cmp99SourceBlockAverageWeight M d)

theorem cmp99SourcePoincareEnergyCoeff_nonneg
    (d M depth : ℕ) [NeZero d] [NeZero M] (spacing epsilon : ℝ) :
    0 ≤ cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon := by
  induction depth generalizing spacing epsilon with
  | zero => simp [cmp99SourcePoincareEnergyCoeff]
  | succ depth ih =>
      simp only [cmp99SourcePoincareEnergyCoeff]
      exact mul_nonneg (le_of_lt cmp99OneScaleBlockPoincareConstant_pos)
        (add_nonneg (sq_nonneg _)
          (mul_nonneg
            (mul_nonneg (by positivity)
              (cmp99SourceBlockAverageWeight_nonneg M d))
            (ih ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon))))

theorem cmp99SourcePoincareErrorCoeff_nonneg
    (d M depth : ℕ) [NeZero d] [NeZero M] (spacing epsilon : ℝ) :
    0 ≤ cmp99SourcePoincareErrorCoeff d M depth spacing epsilon := by
  induction depth generalizing spacing epsilon with
  | zero => simp [cmp99SourcePoincareErrorCoeff]
  | succ depth ih =>
      simp only [cmp99SourcePoincareErrorCoeff]
      exact mul_nonneg (le_of_lt cmp99OneScaleBlockPoincareConstant_pos)
        (add_nonneg
          (mul_nonneg
            (cmp99SourcePoincareEnergyCoeff_nonneg d M depth
              ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon))
            (cmp99SourceScaledGradientStepError_nonneg d M epsilon spacing))
          (mul_nonneg
            (ih ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon))
            (cmp99SourceBlockAverageWeight_nonneg M d)))

/-- The terminal field energy is the last member of the generated field
tower, not an independently supplied coarse field. -/
noncomputable def CMP99SourceActiveRegionChain.terminalFieldNormSq
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    letI : NeZero N := regions.neZero
    (epsilon : ℝ) → (background : GaugeConfig d N (SUN Nc)) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) → ℝ := by
  letI : NeZero N := regions.neZero
  intro epsilon background chain fineSmall phi
  exact regions.fieldNormSq hd hM epsilon background chain fineSmall
    (Fin.last depth) phi

/-- The recursive Poincare expression is bounded by three source-generated
scalar ledgers: fine derivative energy, accumulated fine-norm error, and the
literal retained terminal norm. -/
theorem CMP99SourceActiveRegionChain.poincareBound_le_coefficients
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    letI : NeZero N := regions.neZero
    ∀ {spacing epsilon : ℝ}, 0 < spacing →
    ∀ (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)),
      regions.poincareBound hd hM spacing epsilon background chain fineSmall phi ≤
        cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon *
            regions.scaledGradientEnergy hd hM spacing epsilon background chain
              fineSmall 0 phi +
          cmp99SourcePoincareErrorCoeff d M depth spacing epsilon * ‖phi‖ ^ 2 +
          cmp99OneScaleBlockPoincareConstant d M ^ depth *
            regions.terminalFieldNormSq hd hM epsilon background chain fineSmall phi := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon hspacing background chain fineSmall phi
      simp [CMP99SourceActiveRegionChain.poincareBound,
        cmp99SourcePoincareEnergyCoeff, cmp99SourcePoincareErrorCoeff,
        CMP99SourceActiveRegionChain.terminalFieldNormSq,
        CMP99SourceActiveRegionChain.scaledGradientEnergy,
        CMP99SourceActiveRegionChain.fieldNormSq]
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon hspacing background chain fineSmall phi
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
      have htail := ih
        (mul_pos (Nat.cast_pos.mpr (NeZero.pos M)) hspacing)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall coarsePhi
      have hgrad := CMP99SourceActiveRegionChain.scaledGradientEnergy_one_le
        Omega hOmega tail hd hM hspacing background chain fineSmall phi
      change tail.scaledGradientEnergy hd hM ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall 0
          coarsePhi ≤
        2 * cmp99SourceBlockAverageWeight M d *
            (CMP99SourceActiveRegionChain.step Omega hOmega tail).scaledGradientEnergy
              hd hM spacing epsilon background chain fineSmall 0 phi +
          cmp99SourceScaledGradientStepError d M epsilon spacing * ‖phi‖ ^ 2
        at hgrad
      rw [(CMP99SourceActiveRegionChain.step Omega hOmega tail).scaledGradientEnergy_zero]
        at hgrad
      have havg : ‖coarsePhi‖ ^ 2 ≤
          cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2 := by
        simpa [coarsePhi] using
          norm_cmp99SourceRegionalAverage_sq_le Omega hOmega
            (matrixSUNAdjointModel Nc) background phi
      have hCP : 0 ≤ cmp99OneScaleBlockPoincareConstant d M :=
        le_of_lt cmp99OneScaleBlockPoincareConstant_pos
      have hA : 0 ≤ cmp99SourcePoincareEnergyCoeff d M depth
          ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon) :=
        cmp99SourcePoincareEnergyCoeff_nonneg _ _ _ _ _
      have hB : 0 ≤ cmp99SourcePoincareErrorCoeff d M depth
          ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon) :=
        cmp99SourcePoincareErrorCoeff_nonneg _ _ _ _ _
      change cmp99OneScaleBlockPoincareConstant d M *
          (spacing ^ 2 *
              ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
                (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2 +
            tail.poincareBound hd hM ((M : ℝ) * spacing)
              (cmp99SourceUbarNextFineRadius d M epsilon)
              Scale.toSourceScale.data.nextBackground chain.tail nextSmall
              coarsePhi) ≤ _
      calc
        _ ≤ cmp99OneScaleBlockPoincareConstant d M *
            (spacing ^ 2 *
                ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
                  (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2 +
              (cmp99SourcePoincareEnergyCoeff d M depth
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon) *
                  tail.scaledGradientEnergy hd hM ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon)
                    Scale.toSourceScale.data.nextBackground chain.tail nextSmall
                    0 coarsePhi +
                cmp99SourcePoincareErrorCoeff d M depth
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon) *
                  ‖coarsePhi‖ ^ 2 +
                cmp99OneScaleBlockPoincareConstant d M ^ depth *
                  tail.terminalFieldNormSq hd hM
                    (cmp99SourceUbarNextFineRadius d M epsilon)
                    Scale.toSourceScale.data.nextBackground chain.tail nextSmall
                    coarsePhi)) := by
              gcongr
        _ ≤ cmp99OneScaleBlockPoincareConstant d M *
            (spacing ^ 2 *
                ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
                  (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2 +
              (cmp99SourcePoincareEnergyCoeff d M depth
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon) *
                  (2 * cmp99SourceBlockAverageWeight M d *
                      ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
                        (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2 +
                    cmp99SourceScaledGradientStepError d M epsilon spacing *
                      ‖phi‖ ^ 2) +
                cmp99SourcePoincareErrorCoeff d M depth
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon) *
                  (cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2) +
                cmp99OneScaleBlockPoincareConstant d M ^ depth *
                  tail.terminalFieldNormSq hd hM
                    (cmp99SourceUbarNextFineRadius d M epsilon)
                    Scale.toSourceScale.data.nextBackground chain.tail nextSmall
                    coarsePhi)) := by
              gcongr
        _ = _ := by
          simp only [cmp99SourcePoincareEnergyCoeff,
            cmp99SourcePoincareErrorCoeff]
          change _ =
            cmp99OneScaleBlockPoincareConstant d M *
                  (spacing ^ 2 +
                    2 * cmp99SourceBlockAverageWeight M d *
                      cmp99SourcePoincareEnergyCoeff d M depth
                        ((M : ℝ) * spacing)
                        (cmp99SourceUbarNextFineRadius d M epsilon)) *
                ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
                  (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2 +
              cmp99OneScaleBlockPoincareConstant d M *
                  (cmp99SourcePoincareEnergyCoeff d M depth
                      ((M : ℝ) * spacing)
                      (cmp99SourceUbarNextFineRadius d M epsilon) *
                        cmp99SourceScaledGradientStepError d M epsilon spacing +
                    cmp99SourcePoincareErrorCoeff d M depth
                        ((M : ℝ) * spacing)
                        (cmp99SourceUbarNextFineRadius d M epsilon) *
                      cmp99SourceBlockAverageWeight M d) * ‖phi‖ ^ 2 +
              cmp99OneScaleBlockPoincareConstant d M ^ (depth + 1) *
                tail.terminalFieldNormSq hd hM
                  (cmp99SourceUbarNextFineRadius d M epsilon)
                  Scale.toSourceScale.data.nextBackground chain.tail nextSmall
                  coarsePhi
          ring

/-- Absorbed multiscale Poincare inequality.  The only remaining scalar
condition is the explicit smallness of the recursively generated `Ubar`
error coefficient. -/
theorem CMP99SourceActiveRegionChain.norm_sq_le_absorbed_poincare
    {depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    letI : NeZero N := regions.neZero
    ∀ {spacing epsilon : ℝ}, 0 < spacing →
    ∀ (background : GaugeConfig d N (SUN Nc))
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
      (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)),
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1 →
      ‖phi‖ ^ 2 ≤
        (cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon *
              regions.scaledGradientEnergy hd hM spacing epsilon background chain
                fineSmall 0 phi +
            cmp99OneScaleBlockPoincareConstant d M ^ depth *
              regions.terminalFieldNormSq hd hM epsilon background chain fineSmall phi) /
          (1 - cmp99SourcePoincareErrorCoeff d M depth spacing epsilon) := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon hspacing background chain fineSmall phi hsmall
  have hp := regions.fieldNormSq_zero_le_poincareBound hd hM hspacing
    background chain fineSmall phi
  have hc := regions.poincareBound_le_coefficients hd hM hspacing
    background chain fineSmall phi
  rw [regions.fieldNormSq_zero] at hp
  have hcombined : ‖phi‖ ^ 2 ≤
      cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon *
            regions.scaledGradientEnergy hd hM spacing epsilon background chain
              fineSmall 0 phi +
          cmp99SourcePoincareErrorCoeff d M depth spacing epsilon * ‖phi‖ ^ 2 +
          cmp99OneScaleBlockPoincareConstant d M ^ depth *
            regions.terminalFieldNormSq hd hM epsilon background chain fineSmall phi :=
    hp.trans hc
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).2
  nlinarith

/-- Canonical absorbed Poincare theorem generated from the source lift and a
single closed small-field budget. -/
theorem cmp99SourceIteratedLift_norm_sq_le_absorbed_poincare_of_closedBudget
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (phi : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
      (SUNLieCoord Nc))
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega depth
    let chain := budget.toRadiusChain
    ‖phi‖ ^ 2 ≤
      (cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon *
            regions.scaledGradientEnergy hd hM spacing epsilon background chain
              fineSmall 0 phi +
          cmp99OneScaleBlockPoincareConstant d M ^ depth *
            regions.terminalFieldNormSq hd hM epsilon background chain fineSmall phi) /
        (1 - cmp99SourcePoincareErrorCoeff d M depth spacing epsilon) := by
  dsimp only
  exact CMP99SourceActiveRegionChain.norm_sq_le_absorbed_poincare
    (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth)
    hd hM hspacing background budget.toRadiusChain fineSmall phi hsmall

end

end YangMills.RG
