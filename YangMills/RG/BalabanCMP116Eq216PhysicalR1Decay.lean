/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq216PhysicalR3Decay
import YangMills.RG.BalabanCMP116InteractingResolventCorrection

/-!
# Exponential kernel reduction for the CMP116 correction `R₁`

The exact three-term telescope is combined with the physical exponential
kernel calculus.  Once `R₃ = Γ₁-Γ₀`, `C₁-C₀`, and the four base operators
are localized at one common input rate, `R₁` is localized after two physical
bond convolutions.  No operator factors are commuted.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Exponential localization of the exact three-term `R₁` telescope. -/
theorem cmp116R1Correction_exponentialKernelBound
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ x y, dist x y = dist y x)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {κ σ S AΓ₀ AΓ₁ AC₀ AC₁ AR₃ ACdiff : ℝ}
    (hσ : 0 ≤ σ)
    (h2σκ : 2 * σ < κ)
    (hS : 0 ≤ S)
    (Γ₀ Γ₁ C₀ C₁ : PhysicalEndomorphism d N Nc)
    (hΓ₀ : PhysicalCovarianceExponentialKernelBound
      Γ₀ dist AΓ₀ κ)
    (hΓ₁ : PhysicalCovarianceExponentialKernelBound
      Γ₁ dist AΓ₁ κ)
    (hC₀ : PhysicalCovarianceExponentialKernelBound
      C₀ dist AC₀ κ)
    (hC₁ : PhysicalCovarianceExponentialKernelBound
      C₁ dist AC₁ κ)
    (hR₃ : PhysicalCovarianceExponentialKernelBound
      (Γ₁ - Γ₀) dist AR₃ κ)
    (hCdiff : PhysicalCovarianceExponentialKernelBound
      (C₁ - C₀) dist ACdiff κ)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ S) :
    PhysicalCovarianceExponentialKernelBound
      (cmp116R1Correction Γ₀ Γ₁ C₀ C₁)
      dist
      (AR₃ * (AC₁ * AΓ₁ * S) * S +
          AΓ₀ * (ACdiff * AΓ₁ * S) * S +
        AΓ₀ * (AC₀ * AR₃ * S) * S)
      ((κ - σ) - σ) := by
  have hR₃adj :
      PhysicalCovarianceExponentialKernelBound
        (Γ₁ - Γ₀).adjoint dist AR₃ κ :=
    physicalCovarianceExponentialKernelBound_adjoint
      dist hsymm (Γ₁ - Γ₀) hR₃
  have hΓ₀adj :
      PhysicalCovarianceExponentialKernelBound
        Γ₀.adjoint dist AΓ₀ κ :=
    physicalCovarianceExponentialKernelBound_adjoint
      dist hsymm Γ₀ hΓ₀
  have hfirst :
      PhysicalCovarianceExponentialKernelBound
        ((Γ₁ - Γ₀).adjoint.comp (C₁.comp Γ₁))
        dist (AR₃ * (AC₁ * AΓ₁ * S) * S)
        ((κ - σ) - σ) :=
    physicalCovarianceExponentialKernelBound_comp_three
      dist htri hσ h2σκ hS
      (Γ₁ - Γ₀).adjoint C₁ Γ₁
      hR₃adj hC₁ hΓ₁ hsum
  have hsecond :
      PhysicalCovarianceExponentialKernelBound
        (Γ₀.adjoint.comp ((C₁ - C₀).comp Γ₁))
        dist (AΓ₀ * (ACdiff * AΓ₁ * S) * S)
        ((κ - σ) - σ) :=
    physicalCovarianceExponentialKernelBound_comp_three
      dist htri hσ h2σκ hS
      Γ₀.adjoint (C₁ - C₀) Γ₁
      hΓ₀adj hCdiff hΓ₁ hsum
  have hthird :
      PhysicalCovarianceExponentialKernelBound
        (Γ₀.adjoint.comp (C₀.comp (Γ₁ - Γ₀)))
        dist (AΓ₀ * (AC₀ * AR₃ * S) * S)
        ((κ - σ) - σ) :=
    physicalCovarianceExponentialKernelBound_comp_three
      dist htri hσ h2σκ hS
      Γ₀.adjoint C₀ (Γ₁ - Γ₀)
      hΓ₀adj hC₀ hR₃ hsum
  rw [cmp116R1Correction_eq_telescope]
  exact physicalCovarianceExponentialKernelBound_add dist
    ((Γ₁ - Γ₀).adjoint.comp (C₁.comp Γ₁) +
      Γ₀.adjoint.comp ((C₁ - C₀).comp Γ₁))
    (Γ₀.adjoint.comp (C₀.comp (Γ₁ - Γ₀)))
    (physicalCovarianceExponentialKernelBound_add dist
      ((Γ₁ - Γ₀).adjoint.comp (C₁.comp Γ₁))
      (Γ₀.adjoint.comp ((C₁ - C₀).comp Γ₁))
      hfirst hsecond)
    hthird

private abbrev CMP116FineEndomorphism
    (d L N' Nc : ℕ) [NeZero L] [NeZero N'] [NeZero (L * N')] :=
  FinePhysicalOneCochain d L N' Nc →L[ℝ]
    FinePhysicalOneCochain d L N' Nc

/-- Exponential localization of one literal interacting CMP116 source
`Γ = Elim† K (Elim Pcomp) S`.  The constraint eliminator, the interacting
precision, the complement projection, and the physical bond sum are
generated internally; only localization of the inverse root `S` remains as
an input. -/
theorem cmp116InteractingPhysicalGammaOperator_exponentialKernelBound
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]
    (hd : 3 ≤ d)
    {κ σ AS ε : ℝ}
    (hσ : 0 ≤ σ)
    (h4σκ : 4 * σ < κ)
    (hgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ) < 1)
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (Sroot : CMP116FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N')))
    (hSroot : PhysicalCovarianceExponentialKernelBound
      Sroot physicalBondDist AS κ) :
    PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalGammaOperator U a Sroot complement)
      physicalBondDist
      (let AElim :=
          (1 + (L : ℝ) ^ (d - 1)) *
            Real.exp (κ * ((3 * L : ℕ) : ℝ));
        let AK :=
          cmp116InteractingPhysicalKernelBudget d L Nc a ε *
            Real.exp (κ * ((3 * L : ℕ) : ℝ));
        let Sgeom :=
          (((2 ^ d) * d : ℕ) : ℝ) *
            (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ))⁻¹;
        AElim * (AK * ((AElim * 1 * Sgeom) * AS * Sgeom) * Sgeom) *
          Sgeom)
      ((((κ - σ) - σ) - σ) - σ) := by
  have hκ : 0 < κ := by linarith
  let Elim : CMP116FineEndomorphism d L N' Nc :=
    cmp96ConstraintEliminationCLM
      (d := d) (L := L) (N' := N') (Nc := Nc)
  let Proj : CMP116FineEndomorphism d L N' Nc :=
    physicalBondProjection complement
  let AElim :=
    (1 + (L : ℝ) ^ (d - 1)) *
      Real.exp (κ * ((3 * L : ℕ) : ℝ))
  let AK :=
    cmp116InteractingPhysicalKernelBudget d L Nc a ε *
      Real.exp (κ * ((3 * L : ℕ) : ℝ))
  let Sgeom :=
    (((2 ^ d) * d : ℕ) : ℝ) *
      (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ))⁻¹
  have hElim :
      PhysicalCovarianceExponentialKernelBound
        Elim physicalBondDist AElim κ := by
    exact cmp96ConstraintEliminationCLM_exponentialKernelBound hd hκ
  have hElimAdj :
      PhysicalCovarianceExponentialKernelBound
        Elim.adjoint physicalBondDist AElim κ :=
    physicalCovarianceExponentialKernelBound_adjoint
      physicalBondDist physicalBondDist_comm Elim hElim
  have hK :
      PhysicalCovarianceExponentialKernelBound
        (interactingPhysicalBasePrecisionCLM U a)
        physicalBondDist AK κ := by
    apply physicalCovarianceExponentialKernelBound_of_finiteRange
        physicalBondDist
        (cmp116InteractingPhysicalKernelBudget_nonneg a ε hε)
        hκ
        (interactingPhysicalBasePrecisionCLM U a)
    · exact interactingPhysicalBasePrecisionCLM_finiteRange U a
    · exact interactingPhysicalBasePrecisionCLM_kernelBound
        U a hε hsmall
  have hProj :
      PhysicalCovarianceExponentialKernelBound
        Proj physicalBondDist 1 κ :=
    physicalBondProjection_exponentialKernelBound
      physicalBondDist physicalBondDist_self complement hκ
  have hSgeom : 0 ≤ Sgeom := by
    dsimp [Sgeom]
    have hden :
        0 < 1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ) :=
      sub_pos.mpr hgeom
    positivity
  have hsum : ∀ x : PhysicalBond d (L * N'),
      ∑ z : PhysicalBond d (L * N'),
        Real.exp (-(σ * (physicalBondDist x z : ℝ))) ≤ Sgeom := by
    intro x
    exact physicalBondDist_exp_sum_le_geometric x hgeom
  change PhysicalCovarianceExponentialKernelBound
    (Elim.adjoint.comp
      ((interactingPhysicalBasePrecisionCLM U a).comp
        ((Elim.comp Proj).comp Sroot)))
    physicalBondDist
    (AElim * (AK * ((AElim * 1 * Sgeom) * AS * Sgeom) * Sgeom) *
      Sgeom)
    ((((κ - σ) - σ) - σ) - σ)
  exact physicalCovarianceExponentialKernelBound_comp_five
    physicalBondDist
    (fun x y z => physicalBondDist_triangle x z y)
    hσ h4σκ hSgeom
    Elim.adjoint (interactingPhysicalBasePrecisionCLM U a)
    Elim Proj Sroot
    hElimAdj hK hElim hProj hSroot hsum

/-- Physical `R₁` localization with both source operators generated from
their literal CMP116 factorizations.  The two root bounds live at `κ`; four
source convolutions lower the common rate to `sourceRate`, and the exact
three-term `R₁` telescope costs two further convolutions. -/
theorem
    cmp116InteractingPhysicalR1Correction_of_sourceRoots_exponentialKernelBound
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]
    (hd : 3 ≤ d)
    {κ γ τ AS₀ AS₁ AC₀ AC₁ AR₃ ACdiff ε₀ ε₁ : ℝ}
    (hγ : 0 ≤ γ)
    (h4γκ : 4 * γ < κ)
    (hγgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-γ) < 1)
    (hτ : 0 ≤ τ)
    (h2τsource : 2 * τ < (((κ - γ) - γ) - γ) - γ)
    (hτgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-τ) < 1)
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (hε₀ : 0 ≤ ε₀)
    (hε₁ : 0 ≤ ε₁)
    (hsmall₀ : PhysicalWilsonSmallBackground U₀ ε₀)
    (hsmall₁ : PhysicalWilsonSmallBackground U₁ ε₁)
    (S₀ S₁ : CMP116FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N')))
    (C₀ C₁ : CMP116FineEndomorphism d L N' Nc)
    (hS₀ : PhysicalCovarianceExponentialKernelBound
      S₀ physicalBondDist AS₀ κ)
    (hS₁ : PhysicalCovarianceExponentialKernelBound
      S₁ physicalBondDist AS₁ κ)
    (hC₀ : PhysicalCovarianceExponentialKernelBound
      C₀ physicalBondDist AC₀ ((((κ - γ) - γ) - γ) - γ))
    (hC₁ : PhysicalCovarianceExponentialKernelBound
      C₁ physicalBondDist AC₁ ((((κ - γ) - γ) - γ) - γ))
    (hR₃ : PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalGammaOperator U₁ a S₁ complement -
        cmp116InteractingPhysicalGammaOperator U₀ a S₀ complement)
      physicalBondDist AR₃ ((((κ - γ) - γ) - γ) - γ))
    (hCdiff : PhysicalCovarianceExponentialKernelBound
      (C₁ - C₀) physicalBondDist ACdiff
        ((((κ - γ) - γ) - γ) - γ)) :
    let sourceRate := (((κ - γ) - γ) - γ) - γ
    let AElim :=
      (1 + (L : ℝ) ^ (d - 1)) *
        Real.exp (κ * ((3 * L : ℕ) : ℝ))
    let AK₀ :=
      cmp116InteractingPhysicalKernelBudget d L Nc a ε₀ *
        Real.exp (κ * ((3 * L : ℕ) : ℝ))
    let AK₁ :=
      cmp116InteractingPhysicalKernelBudget d L Nc a ε₁ *
        Real.exp (κ * ((3 * L : ℕ) : ℝ))
    let Sγ :=
      (((2 ^ d) * d : ℕ) : ℝ) *
        (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-γ))⁻¹
    let AΓ₀ :=
      AElim * (AK₀ * ((AElim * 1 * Sγ) * AS₀ * Sγ) * Sγ) * Sγ
    let AΓ₁ :=
      AElim * (AK₁ * ((AElim * 1 * Sγ) * AS₁ * Sγ) * Sγ) * Sγ
    let Sτ :=
      (((2 ^ d) * d : ℕ) : ℝ) *
        (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-τ))⁻¹
    PhysicalCovarianceExponentialKernelBound
      (cmp116R1Correction
        (cmp116InteractingPhysicalGammaOperator U₀ a S₀ complement)
        (cmp116InteractingPhysicalGammaOperator U₁ a S₁ complement)
        C₀ C₁)
      physicalBondDist
      (AR₃ * (AC₁ * AΓ₁ * Sτ) * Sτ +
          AΓ₀ * (ACdiff * AΓ₁ * Sτ) * Sτ +
        AΓ₀ * (AC₀ * AR₃ * Sτ) * Sτ)
      ((sourceRate - τ) - τ) := by
  let sourceRate := (((κ - γ) - γ) - γ) - γ
  let AElim :=
    (1 + (L : ℝ) ^ (d - 1)) *
      Real.exp (κ * ((3 * L : ℕ) : ℝ))
  let AK₀ :=
    cmp116InteractingPhysicalKernelBudget d L Nc a ε₀ *
      Real.exp (κ * ((3 * L : ℕ) : ℝ))
  let AK₁ :=
    cmp116InteractingPhysicalKernelBudget d L Nc a ε₁ *
      Real.exp (κ * ((3 * L : ℕ) : ℝ))
  let Sγ :=
    (((2 ^ d) * d : ℕ) : ℝ) *
      (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-γ))⁻¹
  let AΓ₀ :=
    AElim * (AK₀ * ((AElim * 1 * Sγ) * AS₀ * Sγ) * Sγ) * Sγ
  let AΓ₁ :=
    AElim * (AK₁ * ((AElim * 1 * Sγ) * AS₁ * Sγ) * Sγ) * Sγ
  let Sτ :=
    (((2 ^ d) * d : ℕ) : ℝ) *
      (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-τ))⁻¹
  have hΓ₀ :
      PhysicalCovarianceExponentialKernelBound
        (cmp116InteractingPhysicalGammaOperator U₀ a S₀ complement)
        physicalBondDist AΓ₀ sourceRate := by
    simpa [AΓ₀, AElim, AK₀, Sγ, sourceRate] using
      (cmp116InteractingPhysicalGammaOperator_exponentialKernelBound
        hd hγ h4γκ hγgeom U₀ a hε₀ hsmall₀ S₀ complement hS₀)
  have hΓ₁ :
      PhysicalCovarianceExponentialKernelBound
        (cmp116InteractingPhysicalGammaOperator U₁ a S₁ complement)
        physicalBondDist AΓ₁ sourceRate := by
    simpa [AΓ₁, AElim, AK₁, Sγ, sourceRate] using
      (cmp116InteractingPhysicalGammaOperator_exponentialKernelBound
        hd hγ h4γκ hγgeom U₁ a hε₁ hsmall₁ S₁ complement hS₁)
  have hSτ : 0 ≤ Sτ := by
    dsimp [Sτ]
    have hden :
        0 < 1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-τ) :=
      sub_pos.mpr hτgeom
    positivity
  have hsumτ : ∀ x : PhysicalBond d (L * N'),
      ∑ z : PhysicalBond d (L * N'),
        Real.exp (-(τ * (physicalBondDist x z : ℝ))) ≤ Sτ := by
    intro x
    exact physicalBondDist_exp_sum_le_geometric x hτgeom
  exact cmp116R1Correction_exponentialKernelBound
    physicalBondDist physicalBondDist_comm
    (fun x y z => physicalBondDist_triangle x z y)
    hτ h2τsource hSτ
    (cmp116InteractingPhysicalGammaOperator U₀ a S₀ complement)
    (cmp116InteractingPhysicalGammaOperator U₁ a S₁ complement)
    C₀ C₁ hΓ₀ hΓ₁ hC₀ hC₁ hR₃ hCdiff hsumτ

end

end YangMills.RG
