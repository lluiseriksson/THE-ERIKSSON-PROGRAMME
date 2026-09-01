/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246FinePointSourceFibreGreen
import YangMills.RG.BalabanCMP89Eq249NormalizedStabilizedEndpointIntegralBound
import YangMills.RG.BalabanCMP89Eq251StabilizedIntegrandHolomorphy

/-!
# PRE-VALIDATION: holomorphy and normalized inverse transform for CMP89 (2.46)

This module derives holomorphy and real-slice integrability for the complete
fine-point-source solution already constructed from the literal finite alias
system.  It then defines the source-normalized Brillouin integral with the
target and source fine endpoints kept separate.

It does not identify the integral with the repository's regional Green
operator, prove the multiple-reflection identity (2.42), produce uniform
`B0`/`delta0`, attain window 15, discharge terminal rows, or inhabit a
`TermSource`.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler. This file remains outside the
import graph until its own compiler and axiom gate passes.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

attribute [local fun_prop]
  differentiable_cmp89Eq245EntireAverageAmplitude
  differentiable_cmp89Eq248EntireAliasMomentum
  differentiable_cmp89Eq251EntirePhase

/-- Multivariable quotient rule for complex-valued maps.  Mathlib's static
`DifferentiableAt.div` theorem is one-dimensional; the product-by-inverse
form keeps the ambient normed complex vector space explicit. -/
private theorem differentiableAt_div_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {z : E}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hne : g z ≠ 0) :
    DifferentiableAt ℂ (fun w => f w / g w) z := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hne)

private theorem differentiable_cmp89Eq246EntireAliasFineSymbol_component
    (d L j : ℕ) (mass : ℝ) (m : CMP89Eq246AliasIndex d L j) :
    Differentiable ℂ (fun z : Fin d → ℂ =>
      cmp89Eq246EntireAliasFineSymbol d L j mass z m) := by
  exact
    (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
      d (((L : ℝ) ^ j)⁻¹) mass).comp
        (differentiable_cmp89Eq248EntireAliasMomentum m.1)

private theorem differentiable_cmp89Eq246EntireAliasAverageColumn_component
    (d L j : ℕ) (m : CMP89Eq246AliasIndex d L j) :
    Differentiable ℂ (fun z : Fin d → ℂ =>
      cmp89Eq246EntireAliasAverageColumn d L j z m) := by
  exact
    (differentiable_cmp89Eq245EntireAverageAmplitude d (L ^ j)).comp
      (differentiable_cmp89Eq248EntireAliasMomentum m.1)

private theorem differentiable_cmp89Eq246EntireAliasAverageRow_component
    (d L j : ℕ) (m : CMP89Eq246AliasIndex d L j) :
    Differentiable ℂ (fun z : Fin d → ℂ =>
      cmp89Eq246EntireAliasAverageRow d L j z m) := by
  unfold cmp89Eq246EntireAliasAverageRow
  fun_prop

theorem differentiable_cmp89Eq246FinePointSourceAliasVector_component
    (d L j : ℕ) (sourceEndpoint : Fin d → ℝ)
    (m : CMP89Eq246AliasIndex d L j) :
    Differentiable ℂ (fun z : Fin d → ℂ =>
      cmp89Eq246FinePointSourceAliasVector
        d L j z sourceEndpoint m) := by
  unfold cmp89Eq246FinePointSourceAliasVector
  fun_prop

theorem differentiableAt_cmp89Eq246StabilizedAliasNoncentralPointSourceMoment
    {d L j : ℕ} [NeZero L] {mass : ℝ} {z : Fin d → ℂ}
    {sourceEndpoint : Fin d → ℝ}
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq246StabilizedAliasNoncentralSourceMoment d L j mass w
        (cmp89Eq246FinePointSourceAliasVector
          d L j w sourceEndpoint)) z := by
  classical
  unfold cmp89Eq246StabilizedAliasNoncentralSourceMoment
  apply DifferentiableAt.fun_sum
  intro m hm
  have hmc : m ≠ cmp89Eq249CentralAliasIndex d L j :=
    (Finset.mem_erase.mp hm).1
  have hrow :=
    differentiable_cmp89Eq246EntireAliasAverageRow_component d L j m
  have hsource :=
    differentiable_cmp89Eq246FinePointSourceAliasVector_component
      d L j sourceEndpoint m
  have hden :=
    differentiable_cmp89Eq246EntireAliasFineSymbol_component d L j mass m
  exact differentiableAt_div_complex
    ((hrow z).mul (hsource z)) (hden z) (hfine m hmc)

/-- The exact stabilized row moment specialized to one literal fine point
source.  Naming this physical specialization keeps the multivariable
differentiability interface from unfolding the full alias solution in its
theorem header. -/
def cmp89Eq246StabilizedFinePointSourceSolutionMoment
    (d L j : ℕ) [NeZero L] (mass a : ℝ)
    (sourceEndpoint : Fin d → ℝ) (z : Fin d → ℂ) : ℂ :=
  let central := cmp89Eq249CentralAliasIndex d L j
  (cmp89Eq246EntireAliasAverageRow d L j z central *
        cmp89Eq246FinePointSourceAliasVector
          d L j z sourceEndpoint central +
      cmp89Eq246EntireAliasFineSymbol d L j mass z central *
        cmp89Eq246StabilizedAliasNoncentralSourceMoment d L j mass z
          (cmp89Eq246FinePointSourceAliasVector
            d L j z sourceEndpoint)) /
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z

/-- The literal fine-point specialization is definitionally the generic
stabilized row moment evaluated on the physical source vector. -/
theorem cmp89Eq246StabilizedFinePointSourceSolutionMoment_eq
    (d L j : ℕ) [NeZero L] (mass a : ℝ)
    (sourceEndpoint : Fin d → ℝ) (z : Fin d → ℂ) :
    cmp89Eq246StabilizedFinePointSourceSolutionMoment
        d L j mass a sourceEndpoint z =
      cmp89Eq246StabilizedAliasFullSolutionMoment d L j mass a z
        (cmp89Eq246FinePointSourceAliasVector
          d L j z sourceEndpoint) := by
  rfl

private theorem differentiableAt_cmp89Eq246StabilizedFinePointSourceMomentNumerator
    {d L j : ℕ} [NeZero L] {mass : ℝ} {z : Fin d → ℂ}
    {sourceEndpoint : Fin d → ℝ}
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      let central := cmp89Eq249CentralAliasIndex d L j
      cmp89Eq246EntireAliasAverageRow d L j w central *
          cmp89Eq246FinePointSourceAliasVector
            d L j w sourceEndpoint central +
        cmp89Eq246EntireAliasFineSymbol d L j mass w central *
          cmp89Eq246StabilizedAliasNoncentralSourceMoment d L j mass w
            (cmp89Eq246FinePointSourceAliasVector
              d L j w sourceEndpoint)) z := by
  let central : CMP89Eq246AliasIndex d L j :=
    cmp89Eq249CentralAliasIndex d L j
  have hrow :=
    differentiable_cmp89Eq246EntireAliasAverageRow_component d L j central
  have hsource :=
    differentiable_cmp89Eq246FinePointSourceAliasVector_component
      d L j sourceEndpoint central
  have hfineCentral :=
    differentiable_cmp89Eq246EntireAliasFineSymbol_component
      d L j mass central
  have hbase :=
    differentiableAt_cmp89Eq246StabilizedAliasNoncentralPointSourceMoment
      (z := z) (sourceEndpoint := sourceEndpoint) hfine
  exact ((hrow z).mul (hsource z)).add ((hfineCentral z).mul hbase)

private theorem cmp89Eq249NoncentralFineDenominators_of_aliasFine
    {d L j : ℕ} [NeZero L] {mass : ℝ} {z : Fin d → ℂ}
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0) :
    ∀ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
        (cmp89Eq249ZeroAlias d),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
  intro m hm
  apply hfine
  intro hmc
  subst m
  simpa using hm

private theorem differentiableAt_cmp89Eq249CentralStabilizedAliasDenominator_of_fine
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {z : Fin d → ℂ}
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a w) z := by
  exact differentiableAt_cmp89Eq249CentralStabilizedAliasDenominator
    (cmp89Eq249NoncentralFineDenominators_of_aliasFine hfine)

theorem differentiableAt_cmp89Eq246StabilizedFinePointSourceSolutionMoment
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {z : Fin d → ℂ}
    {sourceEndpoint : Fin d → ℝ}
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0) :
    DifferentiableAt ℂ
      (cmp89Eq246StabilizedFinePointSourceSolutionMoment
        d L j mass a sourceEndpoint) z := by
  unfold cmp89Eq246StabilizedFinePointSourceSolutionMoment
  exact differentiableAt_div_complex
    (differentiableAt_cmp89Eq246StabilizedFinePointSourceMomentNumerator hfine)
    (differentiableAt_cmp89Eq249CentralStabilizedAliasDenominator_of_fine hfine)
    hstabilized

theorem differentiableAt_cmp89Eq246StabilizedFinePointSourceSolution_component
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {z : Fin d → ℂ}
    {sourceEndpoint : Fin d → ℝ}
    (m : CMP89Eq246AliasIndex d L j)
    (hfine : ∀ n : CMP89Eq246AliasIndex d L j,
      n ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z n ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0)
    (hrow : cmp89Eq246EntireAliasAverageRow d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq246StabilizedFinePointSourceSolution
        d L j mass a w sourceEndpoint m) z := by
  classical
  let central := cmp89Eq249CentralAliasIndex d L j
  have hmoment :=
    differentiableAt_cmp89Eq246StabilizedFinePointSourceSolutionMoment
      (z := z) (sourceEndpoint := sourceEndpoint) hfine hstabilized
  unfold cmp89Eq246StabilizedFinePointSourceSolutionMoment at hmoment
  have hsource :=
    differentiable_cmp89Eq246FinePointSourceAliasVector_component
      d L j sourceEndpoint
  have hfineDiff :=
    differentiable_cmp89Eq246EntireAliasFineSymbol_component d L j mass
  have hcolumn :=
    differentiable_cmp89Eq246EntireAliasAverageColumn_component d L j
  by_cases hm : m = central
  · subst m
    have hsum : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
        ∑ n ∈ Finset.univ.erase central,
          cmp89Eq246EntireAliasAverageRow d L j w n *
            (cmp89Eq246FinePointSourceAliasVector
                d L j w sourceEndpoint n /
                cmp89Eq246EntireAliasFineSymbol d L j mass w n -
              (a : ℂ) * cmp89Eq246EntireAliasAverageColumn d L j w n *
                cmp89Eq246StabilizedAliasFullSolutionMoment d L j mass a w
                  (cmp89Eq246FinePointSourceAliasVector
                    d L j w sourceEndpoint) /
                cmp89Eq246EntireAliasFineSymbol d L j mass w n)) z := by
      apply DifferentiableAt.fun_sum
      intro n hn
      have hnc : n ≠ central := (Finset.mem_erase.mp hn).1
      have hrowN :=
        differentiable_cmp89Eq246EntireAliasAverageRow_component d L j n
      have hsN := hsource n
      have hfN := hfineDiff n
      have hcN := hcolumn n
      exact (hrowN z).mul
        ((differentiableAt_div_complex
             (hsN z) (hfN z) (hfine n hnc)).sub
           (differentiableAt_div_complex
             (((hcN z).const_mul (a : ℂ)).mul hmoment)
             (hfN z) (hfine n hnc)))
    have hrowDiff :=
      differentiable_cmp89Eq246EntireAliasAverageRow_component
        d L j central
    simpa [cmp89Eq246StabilizedFinePointSourceSolution,
      cmp89Eq246StabilizedAliasFullSolution, central] using
        differentiableAt_div_complex
          (hmoment.sub hsum) (hrowDiff z) hrow
  · have hsM := hsource m
    have hfM := hfineDiff m
    have hcM := hcolumn m
    simpa [cmp89Eq246StabilizedFinePointSourceSolution,
      cmp89Eq246StabilizedAliasFullSolution, central, hm] using
        (differentiableAt_div_complex
          (hsM z) (hfM z) (hfine m hm)).sub
          (differentiableAt_div_complex
            (((hcM z).const_mul (a : ℂ)).mul hmoment)
            (hfM z) (hfine m hm))

theorem differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {z : Fin d → ℂ}
    {targetEndpoint sourceEndpoint : Fin d → ℝ}
    (hfine : ∀ n : CMP89Eq246AliasIndex d L j,
      n ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z n ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0)
    (hrow : cmp89Eq246EntireAliasAverageRow d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq246StabilizedFineToFineGreenIntegrand d L j mass a w
        targetEndpoint sourceEndpoint) z := by
  unfold cmp89Eq246StabilizedFineToFineGreenIntegrand
  apply DifferentiableAt.fun_sum
  intro m _
  have hphase : Differentiable ℂ (fun w : Fin d → ℂ =>
      Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum w m.1) targetEndpoint)) := by
    fun_prop
  exact (hphase z).mul
    (differentiableAt_cmp89Eq246StabilizedFinePointSourceSolution_component
      m hfine hstabilized hrow)

theorem differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand_of_commonRadius
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    {targetEndpoint sourceEndpoint : Fin 4 → ℝ} :
    DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a w
        targetEndpoint sourceEndpoint) z := by
  have hfine : ∀ m : CMP89Eq246AliasIndex 4 L j,
      m ≠ cmp89Eq249CentralAliasIndex 4 L j →
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z m ≠ 0 := by
    intro m hm
    have hm0 : m.1 ≠ cmp89Eq249ZeroAlias 4 := by
      intro hm0
      apply hm
      apply Subtype.ext
      exact hm0
    have hmErase :
        m.1 ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
          (cmp89Eq249ZeroAlias 4) := Finset.mem_erase.mpr ⟨hm0, m.2⟩
    exact cmp89Eq251NoncentralFineSymbol_ne_zero_of_commonRadius
      hrho hradius hmErase hp hreal himag
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 :=
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero
      ha hmassPos hrho hradius hmass hdenWindow hp hreal himag hamplitude
  have hpair : cmp89Eq249CentralEntireAveragePair 4 L j z ≠ 0 :=
    cmp89Eq249CentralEntireAveragePair_ne_zero
      hrho hpairWindow hp hreal himag
  exact
    differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand
      hfine hstabilized
        (cmp89Eq246CentralAverageRow_ne_zero_of_pair_ne_zero 4 L j z hpair)

theorem integrable_cmp89Eq246PhysicalFineToFineGreenIntegrand_real
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    Integrable (fun x : Fin 4 → ℝ =>
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
        target source)
      cmp89Eq249FourDimensionalBrillouinMeasure := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let xi := cmp89Eq249FineLatticeSpacing L j
  let targetEndpoint : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi target
  let sourceEndpoint : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement xi source
  have hcont : ContinuousOn (fun x : Fin 4 → ℝ =>
      cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a
        (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
        targetEndpoint sourceEndpoint)
      (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi)) := by
    intro x hx
    have hp : ∀ mu,
        |cmp89Eq251PhysicalBrillouinParameter x mu| ≤ Real.pi := by
      intro mu
      rw [abs_le]
      have hxLower := hx.1 mu
      have hxUpper := hx.2 mu
      simp only [cmp89Eq251PhysicalBrillouinParameter]
      constructor <;> linarith [Real.pi_pos]
    have houter :=
      differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand_of_commonRadius
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hmassPos hrho hamplitude hradius hdenWindow hpairWindow hmass
        (p := cmp89Eq251PhysicalBrillouinParameter x) hp
        (z := fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
        (by intro mu; simp) (by intro mu; simpa using hrho)
        (targetEndpoint := targetEndpoint) (sourceEndpoint := sourceEndpoint)
    have hinner : ContinuousAt (fun y : Fin 4 → ℝ =>
        fun mu => (cmp89Eq251PhysicalBrillouinParameter y mu : ℂ)) x := by
      apply Continuous.continuousAt
      apply continuous_pi
      intro mu
      simp only [cmp89Eq251PhysicalBrillouinParameter]
      fun_prop
    exact (houter.continuousAt.comp hinner).continuousWithinAt
  have hIcc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a
        (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
        targetEndpoint sourceEndpoint)
      (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hcont.integrableOn_compact
      (isCompact_Icc : IsCompact
        (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi)))
  have hIoc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a
        (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
        targetEndpoint sourceEndpoint)
      (Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hIcc.congr_set_ae Measure.univ_pi_Ioc_ae_eq_Icc
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi] at hIoc
  simpa [cmp89Eq246PhysicalFineToFineGreenIntegrand, targetEndpoint,
    sourceEndpoint, xi, cmp89Eq249FourDimensionalBrillouinMeasure,
    IntegrableOn, Set.uIoc_of_le htwoPi] using hIoc

/-- The literal fibre equation may be integrated over the physical
Brillouin cube without introducing a Fourier-to-operator dictionary.  This
is only the integral of the already proved pointwise equation; it does not
identify the left side with a regional precision acting on the inverse
transform. -/
theorem integral_cmp89Eq246FinePointSourceFibreEquation_of_commonRadius
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (source : Fin 4 → ℤ) (n : CMP89Eq246AliasIndex 4 L j) :
    (∫ x : Fin 4 → ℝ,
        (cmp89Eq246EntireAliasPrecisionMatrix 4 L j mass a
          (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))).mulVec
            (cmp89Eq246StabilizedFinePointSourceSolution 4 L j mass a
              (fun mu =>
                (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
              (cmp89Eq249PhysicalFineLatticeDisplacement
                (cmp89Eq249FineLatticeSpacing L j) source)) n
      ∂cmp89Eq249FourDimensionalBrillouinMeasure) =
    ∫ x : Fin 4 → ℝ,
        cmp89Eq243FineLatticeFourierTransform 4
          (cmp89Eq249FineLatticeSpacing L j)
          (cmp89Eq248EntireAliasMomentum
            (fun mu =>
              (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ)) n.1)
          (cmp89Eq243NormalizedFinePointSource 4
            (cmp89Eq249FineLatticeSpacing L j) source)
      ∂cmp89Eq249FourDimensionalBrillouinMeasure := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let cube : Set (Fin 4 → ℝ) :=
    Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi)
  have hmeasure :
      cmp89Eq249FourDimensionalBrillouinMeasure =
        (volume : Measure (Fin 4 → ℝ)).restrict cube := by
    dsimp [cmp89Eq249FourDimensionalBrillouinMeasure, cube]
    rw [volume_pi, Measure.restrict_pi_pi]
    simp [Set.uIoc_of_le htwoPi]
  have hcube : MeasurableSet cube := by
    exact MeasurableSet.pi (Set.to_countable Set.univ) fun _ _ =>
      measurableSet_Ioc
  have hmem :
      ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure, x ∈ cube := by
    rw [hmeasure]
    exact ae_restrict_mem hcube
  apply integral_congr_ae
  filter_upwards [hmem] with x hx
  have hp : ∀ mu,
      |cmp89Eq251PhysicalBrillouinParameter x mu| ≤ Real.pi := by
    intro mu
    have hxmu : x mu ∈ Set.Ioc 0 (2 * Real.pi) := hx mu (by simp)
    rw [abs_le]
    simp only [cmp89Eq251PhysicalBrillouinParameter]
    constructor <;> linarith [Real.pi_pos, hxmu.1, hxmu.2]
  have heq :=
    cmp89Eq246EntireAliasPrecisionMatrix_mulVec_normalizedFinePointSourceSolution_of_commonRadius
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hdenWindow hpairWindow hmass
      (p := cmp89Eq251PhysicalBrillouinParameter x) hp
      (z := fun mu =>
        (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
      (by intro mu; simp) (by intro mu; simpa using hrho) source
  exact congrFun heq n

def cmp89Eq246NormalizedPhysicalFineToFineGreen
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (target source : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
      (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
      target source

theorem cmp89Eq246NormalizedPhysicalFineToFineGreen_eq
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246NormalizedPhysicalFineToFineGreen
        L j mass a target source =
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
        cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
          (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
          target source := rfl

end

end YangMills.RG
