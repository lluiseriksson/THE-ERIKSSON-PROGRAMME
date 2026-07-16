/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq216PhysicalR3
import YangMills.RG.BalabanCMP96ConstraintEliminationLocality
import YangMills.RG.PhysicalExponentialKernelComposition
import YangMills.RG.PhysicalInverseSqrtKernelDecay
import YangMills.RG.PhysicalSingleInverseSqrtKernelDecay

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

open MeasureTheory Set
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
theorem physicalCovarianceExponentialKernelBound_comp_five
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
    physicalCovarianceExponentialKernelBound_comp_five
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
    physicalCovarianceExponentialKernelBound_comp_five
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

/-- Stronger specialization generating, in addition, the localization of the
literal interacting base precision and the volume-uniform exponential bond
sum.  The only remaining operator-localization inputs are `R₂`, the base
inverse root, and the inverse-root difference. -/
theorem
    cmp116InteractingPhysicalR3Correction_of_physicalBaseData_exponentialKernelBound
    (hd : 3 ≤ d)
    {κ σ AR₂ AS₀ ASdiff ε : ℝ}
    (hσ : 0 ≤ σ)
    (h4σκ : 4 * σ < κ)
    (hgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ) < 1)
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (hε : 0 ≤ ε)
    (hsmall₁ : PhysicalWilsonSmallBackground U₁ ε)
    (S₀ S₁ : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N')))
    (hR₂ : PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
      physicalBondDist AR₂ κ)
    (hS₀ : PhysicalCovarianceExponentialKernelBound
      S₀ physicalBondDist AS₀ κ)
    (hSdiff : PhysicalCovarianceExponentialKernelBound
      (S₁ - S₀) physicalBondDist ASdiff κ) :
    PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR3Correction
        U₀ U₁ a S₀ S₁ complement)
      physicalBondDist
      (let AElim :=
          (1 + (L : ℝ) ^ (d - 1)) *
            Real.exp (κ * ((3 * L : ℕ) : ℝ));
        let AK₁ :=
          cmp116InteractingPhysicalKernelBudget d L Nc a ε *
            Real.exp (κ * ((3 * L : ℕ) : ℝ));
        let Sgeom :=
          (((2 ^ d) * d : ℕ) : ℝ) *
            (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ))⁻¹;
        AElim *
            (AR₂ * ((AElim * 1 * Sgeom) * AS₀ * Sgeom) * Sgeom) *
              Sgeom +
          AElim *
            (AK₁ * ((AElim * 1 * Sgeom) * ASdiff * Sgeom) * Sgeom) *
              Sgeom)
      ((((κ - σ) - σ) - σ) - σ) := by
  have hκ : 0 < κ := by linarith
  let AElim :=
    (1 + (L : ℝ) ^ (d - 1)) *
      Real.exp (κ * ((3 * L : ℕ) : ℝ))
  let AK₁ :=
    cmp116InteractingPhysicalKernelBudget d L Nc a ε *
      Real.exp (κ * ((3 * L : ℕ) : ℝ))
  let Sgeom :=
    (((2 ^ d) * d : ℕ) : ℝ) *
      (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ))⁻¹
  have hElim :
      PhysicalCovarianceExponentialKernelBound
        (cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc))
        physicalBondDist AElim κ := by
    exact cmp96ConstraintEliminationCLM_exponentialKernelBound hd hκ
  have hK₁ :
      PhysicalCovarianceExponentialKernelBound
        (interactingPhysicalBasePrecisionCLM U₁ a)
        physicalBondDist AK₁ κ := by
    apply physicalCovarianceExponentialKernelBound_of_finiteRange
        physicalBondDist
        (cmp116InteractingPhysicalKernelBudget_nonneg a ε hε)
        hκ
        (interactingPhysicalBasePrecisionCLM U₁ a)
    · exact interactingPhysicalBasePrecisionCLM_finiteRange U₁ a
    · exact interactingPhysicalBasePrecisionCLM_kernelBound
        U₁ a hε hsmall₁
  have hSgeom : 0 ≤ Sgeom := by
    dsimp [Sgeom]
    have hden :
        0 <
          1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ) :=
      sub_pos.mpr hgeom
    positivity
  have hsum : ∀ x : PhysicalBond d (L * N'),
      ∑ z : PhysicalBond d (L * N'),
        Real.exp (-(σ * (physicalBondDist x z : ℝ))) ≤ Sgeom := by
    intro x
    exact physicalBondDist_exp_sum_le_geometric x hgeom
  exact cmp116InteractingPhysicalR3Correction_exponentialKernelBound
    physicalBondDist physicalBondDist_comm
    (fun x y z => physicalBondDist_triangle x z y)
    physicalBondDist_self
    hσ h4σκ hSgeom U₀ U₁ a S₀ S₁ complement
    hElim hR₂ hK₁ hS₀ hSdiff hsum

/-- The base root in the physical `R₃` telescope is now the canonical positive
inverse square root of the real coercive precision.  Its exponential
localization is generated internally from the physical finite-range,
small-background, coercivity, and tilt certificates.  No abstract `hS₀`
premise remains. -/
theorem
    cmp116InteractingPhysicalR3Correction_of_canonicalBaseRoot_exponentialKernelBound
    {dCoord LCoord lieDim : ℕ}
    [NeZero LCoord]
    (D : PhysicalGaugeCMP116Dictionary
      d (L * N') Nc dCoord LCoord lieDim)
    (hd : 3 ≤ d)
    {κ σ AR₂ ASdiff ε c₀ : ℝ}
    (hσ : 0 ≤ σ)
    (h4σκ : 4 * σ < κ)
    (hgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ) < 1)
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (hε : 0 ≤ ε)
    (hsmall₀ : PhysicalWilsonSmallBackground U₀ ε)
    (hsmall₁ : PhysicalWilsonSmallBackground U₁ ε)
    (hc₀ : 0 < c₀)
    (hcoer₀ : IsCoerciveCLM
      (interactingPhysicalBasePrecisionCLM U₀ a) c₀)
    (hK₀ :
      (interactingPhysicalBasePrecisionCLM U₀ a :
        FinePhysicalOneCochain d L N' Nc →ₗ[ℝ]
          FinePhysicalOneCochain d L N' Nc).IsSymmetric)
    (hbaseBudget₀ :
      cmp116InteractingPhysicalKernelBudget d L Nc a ε *
          (Real.exp (κ * ((3 * L : ℕ) : ℝ)) - 1) *
          (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ)
        ≤ c₀ / 2)
    (hshiftBudget :
      (Real.exp (κ * ((3 * L : ℕ) : ℝ)) - 1) *
          (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ)
        ≤ 1 / 2)
    (S₁ : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N')))
    (hR₂ : PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
      physicalBondDist AR₂ κ)
    (hSdiff : PhysicalCovarianceExponentialKernelBound
      (S₁ -
        D.physicalCanonicalInverseSqrt
          (interactingPhysicalBasePrecisionCLM U₀ a)
          hc₀ hcoer₀ hK₀)
      physicalBondDist ASdiff κ) :
    PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR3Correction
        U₀ U₁ a
        (D.physicalCanonicalInverseSqrt
          (interactingPhysicalBasePrecisionCLM U₀ a)
          hc₀ hcoer₀ hK₀)
        S₁ complement)
      physicalBondDist
      (let AElim :=
          (1 + (L : ℝ) ^ (d - 1)) *
            Real.exp (κ * ((3 * L : ℕ) : ℝ));
        let AK₁ :=
          cmp116InteractingPhysicalKernelBudget d L Nc a ε *
            Real.exp (κ * ((3 * L : ℕ) : ℝ));
        let Sgeom :=
          (((2 ^ d) * d : ℕ) : ℝ) *
            (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ))⁻¹;
        AElim *
            (AR₂ *
              ((AElim * 1 * Sgeom) *
                (2 * (Real.sqrt c₀)⁻¹) * Sgeom) *
              Sgeom) *
              Sgeom +
          AElim *
            (AK₁ * ((AElim * 1 * Sgeom) * ASdiff * Sgeom) * Sgeom) *
              Sgeom)
      ((((κ - σ) - σ) - σ) - σ) := by
  have hκ : 0 < κ := by linarith
  have hS₀ :
      PhysicalCovarianceExponentialKernelBound
        (D.physicalCanonicalInverseSqrt
          (interactingPhysicalBasePrecisionCLM U₀ a)
          hc₀ hcoer₀ hK₀)
        physicalBondDist (2 * (Real.sqrt c₀)⁻¹) κ := by
    exact physicalCanonicalInverseSqrt_exponentialKernelBound_of_coercive
      D physicalBondDist physicalBondDist_comm
      physicalBondDist_triangle physicalBondDist_self
      hκ
      (cmp116InteractingPhysicalKernelBudget_nonneg a ε hε)
      hc₀
      (fun x => physicalBondDist_ball_card_le x (3 * L))
      (interactingPhysicalBasePrecisionCLM U₀ a)
      (interactingPhysicalBasePrecisionCLM_finiteRange U₀ a)
      (interactingPhysicalBasePrecisionCLM_kernelBound
        U₀ a hε hsmall₀)
      hcoer₀ hK₀ hbaseBudget₀ hshiftBudget
  exact
    cmp116InteractingPhysicalR3Correction_of_physicalBaseData_exponentialKernelBound
      hd hσ h4σκ hgeom U₀ U₁ a hε hsmall₁
      (D.physicalCanonicalInverseSqrt
        (interactingPhysicalBasePrecisionCLM U₀ a)
        hc₀ hcoer₀ hK₀)
      S₁ complement hR₂ hS₀ hSdiff

/-- Fully canonical real-sector `R₃` estimate.  Both roots are the canonical
positive inverse square roots of the two physical coercive precisions.
The physical `R₂` bound, the base-root localization, and the root-difference
localization are all produced internally. -/
theorem
    cmp116InteractingPhysicalR3Correction_of_canonicalRoots_exponentialKernelBound
    {dCoord LCoord lieDim : ℕ}
    [NeZero LCoord]
    (D : PhysicalGaugeCMP116Dictionary
      d (L * N') Nc dCoord LCoord lieDim)
    (hd : 3 ≤ d)
    {θ ρ σ ε c₀ c₁ : ℝ}
    (hθ : 0 < θ)
    (hρ : 0 ≤ ρ)
    (h2ρθ : 2 * ρ < θ)
    (hσ : 0 ≤ σ)
    (h4σrootRate : 4 * σ < (θ - ρ) - ρ)
    (hrootGeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-ρ) < 1)
    (houterGeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ) < 1)
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (hε : 0 ≤ ε)
    (hsmall₀ : PhysicalWilsonSmallBackground U₀ ε)
    (hsmall₁ : PhysicalWilsonSmallBackground U₁ ε)
    (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁)
    (hcoer₀ : IsCoerciveCLM
      (interactingPhysicalBasePrecisionCLM U₀ a) c₀)
    (hcoer₁ : IsCoerciveCLM
      (interactingPhysicalBasePrecisionCLM U₁ a) c₁)
    (hK₀ :
      (interactingPhysicalBasePrecisionCLM U₀ a :
        FinePhysicalOneCochain d L N' Nc →ₗ[ℝ]
          FinePhysicalOneCochain d L N' Nc).IsSymmetric)
    (hK₁ :
      (interactingPhysicalBasePrecisionCLM U₁ a :
        FinePhysicalOneCochain d L N' Nc →ₗ[ℝ]
          FinePhysicalOneCochain d L N' Nc).IsSymmetric)
    (hbaseBudget₀ :
      cmp116InteractingPhysicalKernelBudget d L Nc a ε *
          (Real.exp (θ * ((3 * L : ℕ) : ℝ)) - 1) *
          (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ)
        ≤ c₀ / 2)
    (hbaseBudget₁ :
      cmp116InteractingPhysicalKernelBudget d L Nc a ε *
          (Real.exp (θ * ((3 * L : ℕ) : ℝ)) - 1) *
          (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ)
        ≤ c₁ / 2)
    (hshiftBudget :
      (Real.exp (θ * ((3 * L : ℕ) : ℝ)) - 1) *
          (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ)
        ≤ 1 / 2)
    (complement : Finset (PhysicalBond d (L * N'))) :
    let rootRate := (θ - ρ) - ρ
    let AR₂ :=
      cmp116InteractingTiltedDefectBudget d Nc ε θ +
        cmp116InteractingTiltedDefectBudget d Nc ε θ
    let Sroot :=
      (((2 ^ d) * d : ℕ) : ℝ) *
        (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-ρ))⁻¹
    let ASdiff :=
      Real.pi⁻¹ * (4 * AR₂ * Sroot * Sroot) *
        (∫ t in Ioi 0, inverseSqrtTwoMarginScalar c₀ c₁ t)
    let AElim :=
      (1 + (L : ℝ) ^ (d - 1)) *
        Real.exp (rootRate * ((3 * L : ℕ) : ℝ))
    let AK₁ :=
      cmp116InteractingPhysicalKernelBudget d L Nc a ε *
        Real.exp (rootRate * ((3 * L : ℕ) : ℝ))
    let Sgeom :=
      (((2 ^ d) * d : ℕ) : ℝ) *
        (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ))⁻¹
    PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR3Correction
        U₀ U₁ a
        (D.physicalCanonicalInverseSqrt
          (interactingPhysicalBasePrecisionCLM U₀ a)
          hc₀ hcoer₀ hK₀)
        (D.physicalCanonicalInverseSqrt
          (interactingPhysicalBasePrecisionCLM U₁ a)
          hc₁ hcoer₁ hK₁)
        complement)
      physicalBondDist
      (AElim *
          (AR₂ *
            ((AElim * 1 * Sgeom) *
              (2 * (Real.sqrt c₀)⁻¹) * Sgeom) *
            Sgeom) *
            Sgeom +
        AElim *
          (AK₁ * ((AElim * 1 * Sgeom) * ASdiff * Sgeom) * Sgeom) *
            Sgeom)
      ((((rootRate - σ) - σ) - σ) - σ) := by
  let rootRate := (θ - ρ) - ρ
  let AR₂ :=
    cmp116InteractingTiltedDefectBudget d Nc ε θ +
      cmp116InteractingTiltedDefectBudget d Nc ε θ
  let Sroot :=
    (((2 ^ d) * d : ℕ) : ℝ) *
      (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-ρ))⁻¹
  let ASdiff :=
    Real.pi⁻¹ * (4 * AR₂ * Sroot * Sroot) *
      (∫ t in Ioi 0, inverseSqrtTwoMarginScalar c₀ c₁ t)
  have hrootRate : 0 < rootRate := by
    dsimp [rootRate]
    linarith
  have hrootRate_le : rootRate ≤ θ := by
    dsimp [rootRate]
    linarith
  have hM :
      0 ≤ cmp116InteractingPhysicalKernelBudget d L Nc a ε :=
    cmp116InteractingPhysicalKernelBudget_nonneg a ε hε
  have hR₂θ :
      PhysicalCovarianceExponentialKernelBound
        (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
        physicalBondDist AR₂ θ := by
    exact cmp116InteractingPhysicalR2Correction_exponentialKernelBound
      U₀ U₁ a hε hε hsmall₀ hsmall₁ hθ
  have hR₂ :
      PhysicalCovarianceExponentialKernelBound
        (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
        physicalBondDist AR₂ rootRate :=
    physicalCovarianceExponentialKernelBound_mono_rate
      physicalBondDist hrootRate hrootRate_le
      (cmp116InteractingPhysicalR2Correction U₀ U₁ a) hR₂θ
  have hSroot : 0 ≤ Sroot := by
    dsimp [Sroot]
    have hden :
        0 < 1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-ρ) :=
      sub_pos.mpr hrootGeom
    positivity
  have hsumRoot : ∀ x : PhysicalBond d (L * N'),
      ∑ z : PhysicalBond d (L * N'),
        Real.exp (-(ρ * (physicalBondDist x z : ℝ))) ≤ Sroot := by
    intro x
    exact physicalBondDist_exp_sum_le_geometric x hrootGeom
  have hS₀θ :
      PhysicalCovarianceExponentialKernelBound
        (D.physicalCanonicalInverseSqrt
          (interactingPhysicalBasePrecisionCLM U₀ a)
          hc₀ hcoer₀ hK₀)
        physicalBondDist (2 * (Real.sqrt c₀)⁻¹) θ := by
    exact physicalCanonicalInverseSqrt_exponentialKernelBound_of_coercive
      D physicalBondDist physicalBondDist_comm
      physicalBondDist_triangle physicalBondDist_self
      hθ hM hc₀
      (fun x => physicalBondDist_ball_card_le x (3 * L))
      (interactingPhysicalBasePrecisionCLM U₀ a)
      (interactingPhysicalBasePrecisionCLM_finiteRange U₀ a)
      (interactingPhysicalBasePrecisionCLM_kernelBound
        U₀ a hε hsmall₀)
      hcoer₀ hK₀ hbaseBudget₀ hshiftBudget
  have hS₀ :
      PhysicalCovarianceExponentialKernelBound
        (D.physicalCanonicalInverseSqrt
          (interactingPhysicalBasePrecisionCLM U₀ a)
          hc₀ hcoer₀ hK₀)
        physicalBondDist (2 * (Real.sqrt c₀)⁻¹) rootRate :=
    physicalCovarianceExponentialKernelBound_mono_rate
      physicalBondDist hrootRate hrootRate_le
      (D.physicalCanonicalInverseSqrt
        (interactingPhysicalBasePrecisionCLM U₀ a)
        hc₀ hcoer₀ hK₀)
      hS₀θ
  have hSdiff :
      PhysicalCovarianceExponentialKernelBound
        (D.physicalCanonicalInverseSqrt
            (interactingPhysicalBasePrecisionCLM U₁ a)
            hc₁ hcoer₁ hK₁ -
          D.physicalCanonicalInverseSqrt
            (interactingPhysicalBasePrecisionCLM U₀ a)
            hc₀ hcoer₀ hK₀)
        physicalBondDist ASdiff rootRate := by
    have h :=
      physicalCanonicalInverseSqrt_sub_exponentialKernelBound_of_coercive
        D physicalBondDist physicalBondDist_comm
        physicalBondDist_triangle physicalBondDist_self
        hθ hρ h2ρθ
        hM hM hc₀ hc₁ hSroot
        (fun x => physicalBondDist_ball_card_le x (3 * L))
        (interactingPhysicalBasePrecisionCLM U₀ a)
        (interactingPhysicalBasePrecisionCLM U₁ a)
        (interactingPhysicalBasePrecisionCLM_finiteRange U₀ a)
        (interactingPhysicalBasePrecisionCLM_finiteRange U₁ a)
        (interactingPhysicalBasePrecisionCLM_kernelBound
          U₀ a hε hsmall₀)
        (interactingPhysicalBasePrecisionCLM_kernelBound
          U₁ a hε hsmall₁)
        hcoer₀ hcoer₁ hK₀ hK₁
        hbaseBudget₀ hbaseBudget₁ hshiftBudget
        (by
          simpa [cmp116InteractingPhysicalR2Correction_eq] using hR₂θ)
        hsumRoot
    simpa [ASdiff, AR₂, rootRate] using h
  exact
    cmp116InteractingPhysicalR3Correction_of_physicalBaseData_exponentialKernelBound
      hd hσ h4σrootRate houterGeom U₀ U₁ a hε hsmall₁
      (D.physicalCanonicalInverseSqrt
        (interactingPhysicalBasePrecisionCLM U₀ a)
        hc₀ hcoer₀ hK₀)
      (D.physicalCanonicalInverseSqrt
        (interactingPhysicalBasePrecisionCLM U₁ a)
        hc₁ hcoer₁ hK₁)
      complement hR₂ hS₀ hSdiff

end

end YangMills.RG
