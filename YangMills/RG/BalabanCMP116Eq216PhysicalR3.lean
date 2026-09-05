/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq216CorrectionDictionary
import YangMills.RG.BalabanCMP116Eq214PhysicalConstraintC
import YangMills.RG.PhysicalGaugeCMP116OperatorTransport

/-!
# CMP116 equation (2.16): physical source correction `R₃`

The physical source operator has the ordered form

`Gamma(K, S) = Elim† K (Elim Pcomp) S`,

where `Elim = I - E Q` is the concrete CMP96 constraint-elimination map,
`Pcomp` is a fixed physical complement projection, `K` is the complete
interacting precision, and `S` is its covariance root.

This module constructs that operator literally and proves the exact telescope

`Gamma(K₁,S₁) - Gamma(K₀,S₀)
  = Elim† (K₁-K₀) (Elim Pcomp) S₀
    + Elim† K₁ (Elim Pcomp) (S₁-S₀)`.

Thus the already controlled precision difference is separated from the only
new analytic debt, the covariance-root difference.  No factors are commuted.

Honest scope: the two roots are supplied physical operators.  This module does
not construct the canonical interacting square roots, compare them, extend to
the complex contour, or prove the common estimate (2.16).
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000

variable {d L N' Nc : ℕ}
  [NeZero L] [NeZero N'] [NeZero (L * N')]

private abbrev FineEndomorphism (d L N' Nc : ℕ)
    [NeZero L] [NeZero N'] [NeZero (L * N')] :=
  FinePhysicalOneCochain d L N' Nc →L[ℝ]
    FinePhysicalOneCochain d L N' Nc

/-- Ordered physical realization `Elim† K (Elim Pcomp) S` of the CMP116 source. -/
def cmp116PhysicalGammaOperator
    (Elim K S : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N'))) :
    FineEndomorphism d L N' Nc :=
  Elim.adjoint.comp
    (K.comp
      ((Elim.comp (physicalBondProjection complement)).comp S))

/-- Pointwise action of the ordered physical source. -/
theorem cmp116PhysicalGammaOperator_apply
    (Elim K S : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N')))
    (x : FinePhysicalOneCochain d L N' Nc) :
    cmp116PhysicalGammaOperator Elim K S complement x =
      Elim.adjoint
        (K
          (Elim
            (physicalBondProjection complement (S x)))) := by
  rfl

/-- Exact two-slot telescope for the physical source.  The reference root
`S₀` is paired with the known precision difference, while the new precision
`K₁` multiplies the unresolved root difference. -/
theorem cmp116PhysicalGammaOperator_sub_eq_telescope
    (Elim K₀ K₁ S₀ S₁ : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N'))) :
    cmp116PhysicalGammaOperator Elim K₁ S₁ complement -
        cmp116PhysicalGammaOperator Elim K₀ S₀ complement =
      Elim.adjoint.comp
          ((K₁ - K₀).comp
            ((Elim.comp (physicalBondProjection complement)).comp S₀)) +
        Elim.adjoint.comp
          (K₁.comp
            ((Elim.comp (physicalBondProjection complement)).comp (S₁ - S₀))) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [cmp116PhysicalGammaOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, map_sub]
  abel

/-- A physical coordinate projection is nonexpansive in the `L²` norm. -/
theorem norm_physicalBondProjection_le_one
    (complement : Finset (PhysicalBond d (L * N'))) :
    ‖(physicalBondProjection complement :
      FineEndomorphism d L N' Nc)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hsq :
      ‖physicalBondProjection complement x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro b _hb
    by_cases hbc : b ∈ complement
    · rw [physicalBondProjection_apply_mem complement hbc]
    · simp [physicalBondProjection_apply_not_mem complement hbc,
        sq_nonneg ‖x b‖]
  nlinarith [norm_nonneg (physicalBondProjection complement x), norm_nonneg x]

/-- Operator-norm consequence of the exact source telescope.  The projection
norm is kept literal here; a later weighted theorem may use a sharper
projection-specific estimate. -/
theorem norm_cmp116PhysicalGammaOperator_sub_le
    (Elim K₀ K₁ S₀ S₁ : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N'))) :
    ‖cmp116PhysicalGammaOperator Elim K₁ S₁ complement -
        cmp116PhysicalGammaOperator Elim K₀ S₀ complement‖ ≤
      ‖Elim‖ * ‖K₁ - K₀‖ * ‖Elim‖ *
          ‖(physicalBondProjection complement :
            FineEndomorphism d L N' Nc)‖ * ‖S₀‖ +
        ‖Elim‖ * ‖K₁‖ * ‖Elim‖ *
          ‖(physicalBondProjection complement :
            FineEndomorphism d L N' Nc)‖ * ‖S₁ - S₀‖ := by
  rw [cmp116PhysicalGammaOperator_sub_eq_telescope]
  calc
    ‖Elim.adjoint.comp
          ((K₁ - K₀).comp
            ((Elim.comp (physicalBondProjection complement)).comp S₀)) +
        Elim.adjoint.comp
          (K₁.comp
            ((Elim.comp (physicalBondProjection complement)).comp (S₁ - S₀)))‖
        ≤
          ‖Elim.adjoint.comp
            ((K₁ - K₀).comp
              ((Elim.comp (physicalBondProjection complement)).comp S₀))‖ +
          ‖Elim.adjoint.comp
            (K₁.comp
              ((Elim.comp (physicalBondProjection complement)).comp (S₁ - S₀)))‖ :=
      norm_add_le _ _
    _ ≤
        (‖Elim.adjoint‖ *
          (‖K₁ - K₀‖ *
            ((‖Elim‖ * ‖(physicalBondProjection complement :
              FineEndomorphism d L N' Nc)‖) * ‖S₀‖))) +
        (‖Elim.adjoint‖ *
          (‖K₁‖ *
            ((‖Elim‖ * ‖(physicalBondProjection complement :
              FineEndomorphism d L N' Nc)‖) * ‖S₁ - S₀‖))) := by
      gcongr
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left
            ((ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left
                ((ContinuousLinearMap.opNorm_comp_le _ _).trans
                  (mul_le_mul_of_nonneg_right
                    (ContinuousLinearMap.opNorm_comp_le _ _)
                    (norm_nonneg _)))
                (norm_nonneg _)))
            (norm_nonneg _))
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left
            ((ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left
                ((ContinuousLinearMap.opNorm_comp_le _ _).trans
                  (mul_le_mul_of_nonneg_right
                    (ContinuousLinearMap.opNorm_comp_le _ _)
                    (norm_nonneg _)))
                (norm_nonneg _)))
            (norm_nonneg _))
    _ =
        ‖Elim‖ * ‖K₁ - K₀‖ * ‖Elim‖ *
            ‖(physicalBondProjection complement :
              FineEndomorphism d L N' Nc)‖ * ‖S₀‖ +
          ‖Elim‖ * ‖K₁‖ * ‖Elim‖ *
            ‖(physicalBondProjection complement :
              FineEndomorphism d L N' Nc)‖ * ‖S₁ - S₀‖ := by
      rw [LinearIsometryEquiv.norm_map]
      ring

variable [NeZero d] [NeZero Nc]

/-- The concrete interacting CMP116 source with physical constraint
elimination and complete Wilson-plus-gauge precision. -/
def cmp116InteractingPhysicalGammaOperator
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (S : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N'))) :
    FineEndomorphism d L N' Nc :=
  cmp116PhysicalGammaOperator
    (cmp96ConstraintEliminationCLM
      (d := d) (L := L) (N' := N') (Nc := Nc))
    (interactingPhysicalBasePrecisionCLM U a)
    S complement

/-- Physical realization of CMP116 `R₃ = Gamma₁ - Gamma₀`. -/
def cmp116InteractingPhysicalR3Correction
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (S₀ S₁ : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N'))) :
    FineEndomorphism d L N' Nc :=
  cmp116R3Correction
    (cmp116InteractingPhysicalGammaOperator U₀ a S₀ complement)
    (cmp116InteractingPhysicalGammaOperator U₁ a S₁ complement)

/-- Terminal physical `R₃` telescope.  Since CMP116 orients
`R₂ = K₀-K₁`, the precision contribution appears with a minus sign. -/
theorem cmp116InteractingPhysicalR3Correction_eq_telescope
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (S₀ S₁ : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N'))) :
    cmp116InteractingPhysicalR3Correction U₀ U₁ a S₀ S₁ complement =
      -(cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc)).adjoint.comp
          ((cmp116InteractingPhysicalR2Correction U₀ U₁ a).comp
            (((cmp96ConstraintEliminationCLM
                (d := d) (L := L) (N' := N') (Nc := Nc)).comp
              (physicalBondProjection complement)).comp S₀)) +
        (cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc)).adjoint.comp
          ((interactingPhysicalBasePrecisionCLM U₁ a).comp
            (((cmp96ConstraintEliminationCLM
                (d := d) (L := L) (N' := N') (Nc := Nc)).comp
              (physicalBondProjection complement)).comp (S₁ - S₀))) := by
  change
    cmp116PhysicalGammaOperator
        (cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc))
        (interactingPhysicalBasePrecisionCLM U₁ a) S₁ complement -
      cmp116PhysicalGammaOperator
        (cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc))
        (interactingPhysicalBasePrecisionCLM U₀ a) S₀ complement = _
  rw [cmp116PhysicalGammaOperator_sub_eq_telescope]
  apply ContinuousLinearMap.ext
  intro x
  simp only [cmp116InteractingPhysicalR2Correction,
    cmp116R2Correction, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  abel

/-- Physical operator-norm reduction of `R₃`.  All factors except the root
difference are concrete operators already present in the CMP116 development. -/
theorem norm_cmp116InteractingPhysicalR3Correction_le
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (S₀ S₁ : FineEndomorphism d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N'))) :
    ‖cmp116InteractingPhysicalR3Correction U₀ U₁ a S₀ S₁ complement‖ ≤
      ‖cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc)‖ *
        ‖interactingPhysicalBasePrecisionCLM U₁ a -
          interactingPhysicalBasePrecisionCLM U₀ a‖ *
        ‖cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc)‖ *
        ‖(physicalBondProjection complement :
          FineEndomorphism d L N' Nc)‖ * ‖S₀‖ +
      ‖cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc)‖ *
        ‖interactingPhysicalBasePrecisionCLM U₁ a‖ *
        ‖cmp96ConstraintEliminationCLM
          (d := d) (L := L) (N' := N') (Nc := Nc)‖ *
        ‖(physicalBondProjection complement :
          FineEndomorphism d L N' Nc)‖ * ‖S₁ - S₀‖ := by
  change
    ‖cmp116PhysicalGammaOperator
          (cmp96ConstraintEliminationCLM
            (d := d) (L := L) (N' := N') (Nc := Nc))
          (interactingPhysicalBasePrecisionCLM U₁ a) S₁ complement -
        cmp116PhysicalGammaOperator
          (cmp96ConstraintEliminationCLM
            (d := d) (L := L) (N' := N') (Nc := Nc))
          (interactingPhysicalBasePrecisionCLM U₀ a) S₀ complement‖ ≤ _
  exact norm_cmp116PhysicalGammaOperator_sub_le
    (cmp96ConstraintEliminationCLM
      (d := d) (L := L) (N' := N') (Nc := Nc))
    (interactingPhysicalBasePrecisionCLM U₀ a)
    (interactingPhysicalBasePrecisionCLM U₁ a)
    S₀ S₁ complement

end

end YangMills.RG
