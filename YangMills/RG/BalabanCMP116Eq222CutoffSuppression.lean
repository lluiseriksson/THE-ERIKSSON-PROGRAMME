/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223GaussianDomination
import YangMills.RG.BalabanCMP116Eq223PhysicalLocalizationProjector

/-!
# CMP116 equation (2.22): large-field cutoff suppression

Balaban's equation (2.22) does more than bound the cutoff by one.  On every
selected large-field bond the threshold condition pays a cardinality penalty,
while a positive localized quadratic term is retained for the subsequent
Gaussian estimate.  This module proves that inequality directly for the
literal indicator product already used in equation (2.14).

With `threshold = epsilon1 / gk` and `gamma = gamma2`, the terminal estimate is

`‖cutoffFactor‖ <= exp (-gamma/2 * threshold^2 * |P|
  + gamma/2 * sum_{b in P} ‖B b‖^2)`.

No potential, covariance, or random-walk estimate is assumed here.  Those are
the independent equation-(2.20)--(2.21) inputs.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

namespace PhysicalGaugeCMP116Dictionary

variable {d M N' Nc L lieDim : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
variable [NeZero Nc] [NeZero L] [NeZero lieDim]

/-- Flattened scalar coordinates carried by the selected large-field bonds
`P`.  This is the coordinate realization of `PB` in equation (2.22). -/
noncomputable def cmp116Eq222SelectedCoordinates
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (P : Finset (PhysicalBond d (M * N'))) :
    Finset (CMP116CoordIndex d L lieDim) := by
  classical
  exact Finset.univ.filter fun qa => (Dict.coordEquiv qa).1 ∈ P

@[simp] theorem mem_cmp116Eq222SelectedCoordinates_iff
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (P : Finset (PhysicalBond d (M * N')))
    (qa : CMP116CoordIndex d L lieDim) :
    qa ∈ Dict.cmp116Eq222SelectedCoordinates P ↔
      (Dict.coordEquiv qa).1 ∈ P := by
  classical
  simp [cmp116Eq222SelectedCoordinates]

/-- Admissibility of `(D,P,Z0)` places every scalar coordinate of `PB` inside
the already constructed physical localization projector `P_Z0`. -/
theorem cmp116Eq222SelectedCoordinates_subset_physicalLocalizedCoordinates
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {Dset : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : CMP116LocalizationAdmissible Dset P Z0) :
    Dict.cmp116Eq222SelectedCoordinates P ⊆
      Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0 := by
  intro qa hqa
  rw [Dict.mem_cmp116Eq223PhysicalLocalizedCoordinates_iff]
  exact hZ0.2 _
    ((Dict.mem_cmp116Eq222SelectedCoordinates_iff P qa).mp hqa)

/-- The positive quadratic energy `‖PB‖²` in equation (2.22) is bounded by
the physical localized quadratic form already used in equation (2.23).  This
is the exact bridge that permits absorption into `alpha5 * P_Z0`. -/
theorem sum_sq_selectedCoordinates_le_dotProduct_physicalLocalizationProjection
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {Dset : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : CMP116LocalizationAdmissible Dset P Z0)
    (x : CMP116CoordIndex d L lieDim → ℝ) :
    (∑ qa ∈ Dict.cmp116Eq222SelectedCoordinates P, x qa ^ 2) ≤
      x ⬝ᵥ (cmp116Eq223CoordinateProjection
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x) := by
  rw [Dict.dotProduct_physicalLocalizationProjection_mulVec]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Dict.cmp116Eq222SelectedCoordinates_subset_physicalLocalizedCoordinates
      hZ0)
    (by
      intro qa hqa hnot
      positivity)

end PhysicalGaugeCMP116Dictionary

/-- One large-field indicator pays its share of the equation-(2.22)
cardinality penalty. -/
theorem norm_cmp116LargeFieldIndicator_le_exp_penalty
    {E : Type*} [Norm E]
    (gamma threshold : ℝ) (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ threshold)
    (x : E) :
    ‖cmp116LargeFieldIndicator threshold x‖ ≤
      Real.exp ((gamma / 2) * (‖x‖ ^ 2 - threshold ^ 2)) := by
  by_cases hlarge : threshold ≤ ‖x‖
  · rw [cmp116LargeFieldIndicator]
    simp only [if_pos hlarge, norm_one]
    have hsq : threshold ^ 2 ≤ ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - threshold)]
    exact Real.one_le_exp
      (mul_nonneg (div_nonneg hgamma (by norm_num)) (sub_nonneg.mpr hsq))
  · rw [cmp116LargeFieldIndicator]
    simp only [if_neg hlarge, norm_zero]
    exact (Real.exp_pos _).le

/-- Product form of equation (2.22) for the literal large-field cutoff. -/
theorem norm_cmp116LargeFieldCutoff_le_exp_card_energy
    {β E : Type*} [Norm E]
    (P : Finset β) (gamma threshold : ℝ)
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ threshold)
    (B : β → E) :
    ‖cmp116LargeFieldCutoff P threshold B‖ ≤
      Real.exp ((gamma / 2) *
        ((∑ b ∈ P, ‖B b‖ ^ 2) - threshold ^ 2 * (P.card : ℝ))) := by
  classical
  unfold cmp116LargeFieldCutoff
  rw [norm_prod]
  calc
    ∏ b ∈ P, ‖cmp116LargeFieldIndicator threshold (B b)‖ ≤
        ∏ b ∈ P,
          Real.exp ((gamma / 2) * (‖B b‖ ^ 2 - threshold ^ 2)) := by
      apply Finset.prod_le_prod
      · intro b hb
        exact norm_nonneg _
      · intro b hb
        exact norm_cmp116LargeFieldIndicator_le_exp_penalty
          gamma threshold hgamma hthreshold (B b)
    _ = Real.exp
        (∑ b ∈ P, (gamma / 2) * (‖B b‖ ^ 2 - threshold ^ 2)) := by
      rw [Real.exp_sum]
    _ = Real.exp ((gamma / 2) *
        ((∑ b ∈ P, ‖B b‖ ^ 2) - threshold ^ 2 * (P.card : ℝ))) := by
      apply congrArg Real.exp
      calc
        (∑ b ∈ P, (gamma / 2) * (‖B b‖ ^ 2 - threshold ^ 2)) =
            (gamma / 2) *
              (∑ b ∈ P, (‖B b‖ ^ 2 - threshold ^ 2)) := by
                rw [Finset.mul_sum]
        _ = (gamma / 2) *
            ((∑ b ∈ P, ‖B b‖ ^ 2) - threshold ^ 2 * (P.card : ℝ)) := by
              rw [Finset.sum_sub_distrib]
              have hconst :
                  (∑ _b ∈ P, threshold ^ 2) =
                    threshold ^ 2 * (P.card : ℝ) := by
                simp
                ring
              rw [hconst]

/-- Literal CMP116 equation-(2.22) bound for the complete signed cutoff in
equation (2.14).  The small-field factor and the inclusion--exclusion sign are
contractions; the selected large-field bonds retain the sharp exponential
cardinality/energy balance. -/
theorem CMP116Eq214AnalyticData.norm_cutoffFactor_le_exp_card_energy
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond) (b : B)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ A.threshold) :
    ‖A.cutoffFactor Y0 P b‖ ≤
      Real.exp ((gamma / 2) *
        ((∑ e ∈ P, ‖A.bondField b e‖ ^ 2) -
          A.threshold ^ 2 * (P.card : ℝ))) := by
  classical
  rw [CMP116Eq214AnalyticData.cutoffFactor, norm_mul, norm_mul]
  have hsign : ‖(-1 : ℂ) ^ P.card‖ = 1 := by simp
  rw [hsign, one_mul]
  have hsmall :=
    norm_cmp116SmallFieldCutoff_le_one Y0 A.threshold (A.bondField b)
  have hlarge := norm_cmp116LargeFieldCutoff_le_exp_card_energy
    P gamma A.threshold hgamma hthreshold (A.bondField b)
  exact mul_le_of_le_one_left (norm_nonneg _) hsmall |>.trans
    (by simpa using hlarge)

/-- Source-composed form of equations (2.20)--(2.23).  The quadratic energy
from (2.22) is combined with the interaction estimate before the Gaussian is
evaluated, while the strict `|P|` penalty survives as an exterior factor.

This theorem is the strengthened `hdom` producer needed by (2.26): unlike a
plain cutoff-contraction estimate, it does not discard the entropy-killing
large-field factor. -/
theorem CMP116Eq214AnalyticData.norm_innerIntegrand_le_cardPenalty_mul_realGaussian
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [Fintype Bond] [MeasurableSpace B] [Norm E]
    (G : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ) (x : X) (b : B)
    (A : Matrix Bond Bond ℝ) (r : Bond → ℝ) (gamma : ℝ)
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ G.threshold)
    (hinner :
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r i * ‖G.bondField b i‖))
    (hinteraction :
      (G.interactionExponent sigma tau psi phi b).re +
          (gamma / 2) * (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
        -(((fun i => ‖G.bondField b i‖) ⬝ᵥ
          (A *ᵥ (fun i => ‖G.bondField b i‖))) / 2)) :
    ‖G.innerIntegrand Y0 P sigma tau psi phi x b‖ ≤
      Real.exp (-(gamma / 2 * G.threshold ^ 2 * (P.card : ℝ))) *
        cmp116Eq223RealGaussian A r (fun i => ‖G.bondField b i‖) := by
  let v : Bond → ℝ := fun i => ‖G.bondField b i‖
  let linear : ℝ := ∑ i, r i * v i
  let energyP : ℝ := ∑ e ∈ P, v e ^ 2
  let quadratic : ℝ := v ⬝ᵥ (A *ᵥ v)
  let penalty : ℝ := gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)
  let cutoffExponent : ℝ :=
    (gamma / 2) * (energyP - G.threshold ^ 2 * (P.card : ℝ))
  have hcutoff :
      ‖G.cutoffFactor Y0 P b‖ ≤ Real.exp cutoffExponent := by
    simpa [cutoffExponent, energyP, v] using
      G.norm_cutoffFactor_le_exp_card_energy
        Y0 P b gamma hgamma hthreshold
  have hweight :
      ‖G.innerWeight sigma tau psi phi x b‖ ≤ Real.exp linear := by
    simpa [linear, v] using hinner
  have hinteraction' :
      (G.interactionExponent sigma tau psi phi b).re +
          (gamma / 2) * energyP ≤ -(quadratic / 2) := by
    simpa [energyP, quadratic, v] using hinteraction
  have hexponent :
      linear + cutoffExponent +
          (G.interactionExponent sigma tau psi phi b).re ≤
        -penalty + (-(quadratic / 2) + linear) := by
    dsimp [cutoffExponent, penalty]
    linarith
  rw [CMP116Eq214AnalyticData.innerIntegrand, norm_mul, norm_mul,
    Complex.norm_exp]
  calc
    ‖G.innerWeight sigma tau psi phi x b‖ * ‖G.cutoffFactor Y0 P b‖ *
        Real.exp (G.interactionExponent sigma tau psi phi b).re ≤
      Real.exp linear * Real.exp cutoffExponent *
        Real.exp (G.interactionExponent sigma tau psi phi b).re := by
          gcongr
    _ = Real.exp
        (linear + cutoffExponent +
          (G.interactionExponent sigma tau psi phi b).re) := by
      rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-penalty + (-(quadratic / 2) + linear)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-penalty) * cmp116Eq223RealGaussian A r v := by
      rw [Real.exp_add]
      rfl
    _ = Real.exp (-(gamma / 2 * G.threshold ^ 2 * (P.card : ℝ))) *
        cmp116Eq223RealGaussian A r (fun i => ‖G.bondField b i‖) := by
      rfl

end

end YangMills.RG
