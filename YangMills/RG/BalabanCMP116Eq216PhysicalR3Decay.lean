/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq216PhysicalR3
import YangMills.RG.BalabanCMP96ConstraintEliminationLocality
import YangMills.RG.PhysicalExponentialKernelComposition
import YangMills.RG.PhysicalInverseSqrtKernelDecay

/-!
# Exponential kernel bound for the physical CMP116 correction `R₃`

This module consumes the exact physical telescope

`R₃ = -Elim† R₂ (Elim Pcomp) S₀
      + Elim† K₁ (Elim Pcomp) (S₁-S₀)`

in the exponential block-kernel calculus.  Four intermediate physical-bond
sums cost four copies of the geometric constant and reduce the input rate
from `κ` to `κ - 4σ`.

The theorem is already specialized to the literal CMP116 operators and
projection.  It keeps only localization certificates for the nontrivial
factors as inputs; in particular, the complement projection and the adjoint
bound are discharged internally.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]

private abbrev FineEndomorphism (d L N' Nc : ℕ)
    [NeZero L] [NeZero N'] [NeZero (L * N')] :=
  FinePhysicalOneCochain d L N' Nc →L[ℝ]
    FinePhysicalOneCochain d L N' Nc

/-- Five-factor physical composition in the parenthesization occurring
literally in the CMP116 `R₃` telescope. -/
private theorem fiveFactor_exponentialKernelBound
    (dist : PhysicalBond d (L * N') → PhysicalBond d (L * N') → ℕ)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {A₀ A₁ A₂ A₃ A₄ κ σ S : ℝ}
    (hσ : 0 ≤ σ)
    (h4σκ : 4 * σ < κ)
    (hS : 0 ≤ S)
    (T₀ T₁ T₂ T₃ T₄ : FineEndomorphism d L N' Nc)
    (hT₀ : PhysicalCovarianceExponentialKernelBound T₀ dist A₀ κ)
    (hT₁ : PhysicalCovarianceExponentialKernelBound T₁ dist A₁ κ)
    (hT₂ : PhysicalCovarianceExponentialKernelBound T₂ dist A₂ κ)
    (hT₃ : PhysicalCovarianceExponentialKernelBound T₃ dist A₃ κ)
    (hT₄ : PhysicalCovarianceExponentialKernelBound T₄ dist A₄ κ)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d (L * N'),
        Real.exp (-(σ * (dist x z : ℝ))) ≤ S) :
    PhysicalCovarianceExponentialKernelBound
      (T₀.comp (T₁.comp ((T₂.comp T₃).comp T₄)))
      dist
      (A₀ * (A₁ * ((A₂ * A₃ * S) * A₄ * S) * S) * S)
      ((((κ - σ) - σ) - σ) - σ) := by
  have hσκ : σ < κ := by linarith
  have hσ2 : σ < κ - σ := by linarith
  have hσ3 : σ < (κ - σ) - σ := by linarith
  have hσ4 : σ < ((κ - σ) - σ) - σ := by linarith
  have h23 :
      PhysicalCovarianceExponentialKernelBound
        (T₂.comp T₃) dist (A₂ * A₃ * S) (κ - σ) :=
    physicalCovarianceExponentialKernelBound_comp
      dist htri hσ hσκ hS T₂ T₃ hT₂ hT₃ hsum
  have h4weak :
      PhysicalCovarianceExponentialKernelBound T₄ dist A₄ (κ - σ) :=
    physicalCovarianceExponentialKernelBound_mono_rate
      dist (sub_pos.mpr hσκ) (by linarith) T₄ hT₄
  have h234 :
      PhysicalCovarianceExponentialKernelBound
        ((T₂.comp T₃).comp T₄) dist
        ((A₂ * A₃ * S) * A₄ * S) ((κ - σ) - σ) :=
    physicalCovarianceExponentialKernelBound_comp
      dist htri hσ hσ2 hS (T₂.comp T₃) T₄ h23 h4weak hsum
  have h1weak :
      PhysicalCovarianceExponentialKernelBound
        T₁ dist A₁ ((κ - σ) - σ) :=
    physicalCovarianceExponentialKernelBound_mono_rate
      dist (by linarith) (by linarith) T₁ hT₁
  have h1234 :
      PhysicalCovarianceExponentialKernelBound
        (T₁.comp ((T₂.comp T₃).comp T₄)) dist
        (A₁ * ((A₂ * A₃ * S) * A₄ * S) * S)
        (((κ - σ) - σ) - σ) :=
    physicalCovarianceExponentialKernelBound_comp
      dist htri hσ hσ3 hS T₁ ((T₂.comp T₃).comp T₄)
      h1weak h234 hsum
  have h0weak :
      PhysicalCovarianceExponentialKernelBound
        T₀ dist A₀ (((κ - σ) - σ) - σ) :=
    physicalCovarianceExponentialKernelBound_mono_rate
      dist (by linarith) (by linarith) T₀ hT₀
  exact physicalCovarianceExponentialKernelBound_comp
    dist htri hσ hσ4 hS T₀
    (T₁.comp ((T₂.comp T₃).comp T₄))
    h0weak h1234 hsum

/-- Exponential localization of the literal physical CMP116 `R₃`
correction. -/
theorem cmp116InteractingPhysicalR3Correction_exponentialKernelBound
    (dist : PhysicalBond d (L * N') → PhysicalBond d (L * N') → ℕ)
    (hsymm : ∀ x y, dist x y = dist y x)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    (hself : ∀ x, dist x x = 0)
    {κ σ S AElim AR₂ AK₁ AS₀ ASdiff : ℝ}
    (hσ : 0 ≤ σ)
    (h4σκ : 4 * σ < κ)
    (hS : 0 ≤ S)
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (S₀ S₁ : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N')))
    (hElim : PhysicalCovarianceExponentialKernelBound
      (cmp96ConstraintEliminationCLM
        (d := d) (L := L) (N' := N') (Nc := Nc))
      dist AElim κ)
    (hR₂ : PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
      dist AR₂ κ)
    (hK₁ : PhysicalCovarianceExponentialKernelBound
      (interactingPhysicalBasePrecisionCLM U₁ a)
      dist AK₁ κ)
    (hS₀ : PhysicalCovarianceExponentialKernelBound
      S₀ dist AS₀ κ)
    (hSdiff : PhysicalCovarianceExponentialKernelBound
      (S₁ - S₀) dist ASdiff κ)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d (L * N'),
        Real.exp (-(σ * (dist x z : ℝ))) ≤ S) :
    PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR3Correction
        U₀ U₁ a S₀ S₁ complement)
      dist
      (AElim *
          (AR₂ * ((AElim * 1 * S) * AS₀ * S) * S) * S +
        AElim *
          (AK₁ * ((AElim * 1 * S) * ASdiff * S) * S) * S)
      ((((κ - σ) - σ) - σ) - σ) := by
  let Elim : FineEndomorphism d L N' Nc :=
    cmp96ConstraintEliminationCLM
      (d := d) (L := L) (N' := N') (Nc := Nc)
  let Proj : FineEndomorphism d L N' Nc :=
    physicalBondProjection complement
  have hElimAdj :
      PhysicalCovarianceExponentialKernelBound
        Elim.adjoint dist AElim κ :=
    physicalCovarianceExponentialKernelBound_adjoint
      dist hsymm Elim hElim
  have hProj :
      PhysicalCovarianceExponentialKernelBound Proj dist 1 κ :=
    physicalBondProjection_exponentialKernelBound
      dist hself complement hR₂.2.1
  have hfirst :
      PhysicalCovarianceExponentialKernelBound
        (Elim.adjoint.comp
          ((cmp116InteractingPhysicalR2Correction U₀ U₁ a).comp
            ((Elim.comp Proj).comp S₀)))
        dist
        (AElim * (AR₂ * ((AElim * 1 * S) * AS₀ * S) * S) * S)
        ((((κ - σ) - σ) - σ) - σ) :=
    fiveFactor_exponentialKernelBound
      dist htri hσ h4σκ hS
      Elim.adjoint
      (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
      Elim Proj S₀
      hElimAdj hR₂ hElim hProj hS₀ hsum
  have hsecond :
      PhysicalCovarianceExponentialKernelBound
        (Elim.adjoint.comp
          ((interactingPhysicalBasePrecisionCLM U₁ a).comp
            ((Elim.comp Proj).comp (S₁ - S₀))))
        dist
        (AElim * (AK₁ * ((AElim * 1 * S) * ASdiff * S) * S) * S)
        ((((κ - σ) - σ) - σ) - σ) :=
    fiveFactor_exponentialKernelBound
      dist htri hσ h4σκ hS
      Elim.adjoint
      (interactingPhysicalBasePrecisionCLM U₁ a)
      Elim Proj (S₁ - S₀)
      hElimAdj hK₁ hElim hProj hSdiff hsum
  rw [cmp116InteractingPhysicalR3Correction_eq_telescope]
  apply physicalCovarianceExponentialKernelBound_add dist
  · exact physicalCovarianceExponentialKernelBound_neg dist _ hfirst
  · exact hsecond

/-- The same physical `R₃` estimate with the localization certificate for
`Elim = I - EQ` generated internally from its literal CMP96 construction.
No abstract locality hypothesis for the constraint elimination remains. -/
theorem
    cmp116InteractingPhysicalR3Correction_of_physicalElimination_exponentialKernelBound
    (hd : 3 ≤ d)
    {κ σ S AR₂ AK₁ AS₀ ASdiff : ℝ}
    (hσ : 0 ≤ σ)
    (h4σκ : 4 * σ < κ)
    (hS : 0 ≤ S)
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (S₀ S₁ : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N')))
    (hR₂ : PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
      physicalBondDist AR₂ κ)
    (hK₁ : PhysicalCovarianceExponentialKernelBound
      (interactingPhysicalBasePrecisionCLM U₁ a)
      physicalBondDist AK₁ κ)
    (hS₀ : PhysicalCovarianceExponentialKernelBound
      S₀ physicalBondDist AS₀ κ)
    (hSdiff : PhysicalCovarianceExponentialKernelBound
      (S₁ - S₀) physicalBondDist ASdiff κ)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d (L * N'),
        Real.exp (-(σ * (physicalBondDist x z : ℝ))) ≤ S) :
    PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR3Correction
        U₀ U₁ a S₀ S₁ complement)
      physicalBondDist
      (let AElim :=
          (1 + (L : ℝ) ^ (d - 1)) *
            Real.exp (κ * ((3 * L : ℕ) : ℝ));
        AElim *
            (AR₂ * ((AElim * 1 * S) * AS₀ * S) * S) * S +
          AElim *
            (AK₁ * ((AElim * 1 * S) * ASdiff * S) * S) * S)
      ((((κ - σ) - σ) - σ) - σ) := by
  have hκ : 0 < κ := by linarith
  let AElim :=
    (1 + (L : ℝ) ^ (d - 1)) *
      Real.exp (κ * ((3 * L : ℕ) : ℝ))
  have hElim :
      PhysicalCovarianceExponentialKernelBound
        (cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc))
        physicalBondDist AElim κ := by
    exact cmp96ConstraintEliminationCLM_exponentialKernelBound hd hκ
  exact cmp116InteractingPhysicalR3Correction_exponentialKernelBound
    physicalBondDist physicalBondDist_comm
    (fun x y z => physicalBondDist_triangle x z y)
    physicalBondDist_self
    hσ h4σκ hS U₀ U₁ a S₀ S₁ complement
    hElim hR₂ hK₁ hS₀ hSdiff hsum

end

end YangMills.RG
