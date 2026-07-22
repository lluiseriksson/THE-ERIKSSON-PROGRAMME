/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq124LocalGAdInverse
import YangMills.RG.BalabanCMP98Eq124GAdPhysical
import YangMills.RG.BalabanCMP99SourceRegionalScale

/-!
# Source small-field producer for the local CMP98 `g(ad)⁻¹` factors

This module identifies the zero-tangent ambient four-contour deviation used
in CMP98 with the literal CMP99 `UbarDeviationLogArg`.  The already proved
path-length estimate can then supply the radius `≤ 1/3` consumed by the
source-form `g(ad)⁻¹` theorem.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- At zero ambient tangent, the analytic Wilson-line extension is literally
the matrix underlying the physical `SU(N)` Wilson line. -/
theorem cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    cmp98AmbientWilsonLineMatrix U 0 es =
      (wilsonLine U es : SUN Nc).val := by
  have h := cmp98AmbientWilsonLineMatrix_twoParameter_eq_unitaryWilsonLine
    U (0 : PhysicalSuMatrixTangent d (M * N') Nc)
      (0 : PhysicalSuMatrixTangent d (M * N') Nc) 0 0 es
  have hz : physicalTwoParameterAmbientTangent
      (0 : PhysicalSuMatrixTangent d (M * N') Nc)
      (0 : PhysicalSuMatrixTangent d (M * N') Nc) 0 0 = 0 := by
    funext b
    change (0 : ℝ) • (0 : SuLie Nc).toMatrix +
      (0 : ℝ) • (0 : SuLie Nc).toMatrix = 0
    module
  rw [hz, physicalSuUnitaryLeftVariation_zero_zero] at h
  have hval :
      ((wilsonLine (physicalBackgroundToUnitary U) es : UN Nc).val) =
        (wilsonLine U es : SUN Nc).val := by
    unfold wilsonLine
    rw [SubmonoidClass.coe_list_prod, SubmonoidClass.coe_list_prod]
    apply congrArg List.prod
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro e he
    rfl
  exact h.trans hval

/-- The zero-tangent analytic deviation is exactly the physical CMP99
small-field variable, with the derived straight transport as coarse field. -/
theorem cmp98UbarAmbientDeviationMatrix_zero_eq_sourceUbarDeviationLogArg
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    cmp98UbarAmbientDeviationMatrix U b x 0 =
      UbarDeviationLogArg
        (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        U (cmp99SourceBaseCoarseBackground U)
        (positiveEdgeOfPhysicalBond b) x
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b) := by
  unfold cmp98UbarAmbientDeviationMatrix UbarDeviationLogArg UbarDeviation
  rw [cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine,
    cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine,
    cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine,
    cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine,
    cmp99SourceBaseCoarseBackground_apply_pos]
  rfl

/-- Fine-link smallness controls the literal zero-tangent deviation used by
the CMP98 local inverse.  There is no independently supplied local matrix
bound in this source-facing estimate. -/
theorem norm_cmp98UbarAmbientDeviationMatrix_zero_le_fineRadius
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤
      cmp99SourceUbarFineDeviationRadius d M epsilonFine := by
  rw [cmp98UbarAmbientDeviationMatrix_zero_eq_sourceUbarDeviationLogArg]
  exact norm_cmp99SourceUbarDeviationLogArg_le_fineRadius
    hd hM U epsilonFine epsilonFine_nonneg fine_small b x hx

/-- **Source-instantiated local-inverse endpoint for CMP98 (124).**
Uniform smallness of the literal fine links, together with the printed
path-length radius condition, produces every pointwise `g(ad y_x)⁻¹`
appearing in the physical block average. -/
theorem cmp98UbarLogAveragePhysicalVariation_eq_gadInv_of_sourceFineSmall
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (hradius : cmp99SourceUbarFineDeviationRadius d M epsilonFine ≤ 1 / 3) :
    cmp98UbarLogAveragePhysicalVariation U A b =
      cmp98Eq124MiddleGAdInvVariation U A b +
        cmp98Eq124CorrectionGAdInvVariation U A b := by
  apply cmp98UbarLogAveragePhysicalVariation_eq_gadInv_of_norm_le_third
  intro x hx
  exact (norm_cmp98UbarAmbientDeviationMatrix_zero_le_fineRadius
    hd hM U epsilonFine epsilonFine_nonneg fine_small b x hx).trans hradius

/-- The same source radius supplies the strict Mercator-chart condition used
by the outer exponential derivative. -/
theorem norm_cmp98UbarAmbientDeviationMatrix_zero_lt_one_of_sourceFineSmall
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (hradius : cmp99SourceUbarFineDeviationRadius d M epsilonFine ≤ 1 / 3)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
  calc
    ‖cmp98UbarAmbientDeviationMatrix U b x 0‖
        ≤ cmp99SourceUbarFineDeviationRadius d M epsilonFine :=
      norm_cmp98UbarAmbientDeviationMatrix_zero_le_fineRadius
        hd hM U epsilonFine epsilonFine_nonneg fine_small b x hx
    _ ≤ 1 / 3 := hradius
    _ < 1 := by norm_num

/-- **End-to-end source-small-field form of CMP98 (124).**  The literal
left-trivialized derivative of the nonlinear block average is the outer
`g(ad)` applied to the two block averages whose pointwise factors carry the
certified local `g(ad)⁻¹`.  No chart or inverse-smallness binder remains. -/
theorem cmp98Eq124_leftTrivialized_physicalVariation_eq_sourceGAdInv
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (hradius : cmp99SourceUbarFineDeviationRadius d M epsilonFine ≤ 1 / 3) :
    NormedSpace.exp (-(cmp98UbarLogAverage U b 0)) *
        fderiv ℝ (cmp98UbarExpAverage U b) 0
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) =
      cmp98GAd (cmp98UbarLogAverage U b 0)
          (cmp98Eq124MiddleGAdInvVariation U A b) +
        cmp98GAd (cmp98UbarLogAverage U b 0)
          (cmp98Eq124CorrectionGAdInvVariation U A b) := by
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    exact norm_cmp98UbarAmbientDeviationMatrix_zero_lt_one_of_sourceFineSmall
      hd hM U epsilonFine epsilonFine_nonneg fine_small hradius b x hx
  rw [cmp98Eq124_leftTrivialized_physicalVariation_eq_gad U A b hsmall]
  unfold cmp98Eq124GAdPhysicalVariation
  rw [cmp98UbarLogAveragePhysicalVariation_eq_gadInv_of_sourceFineSmall
    hd hM U A b epsilonFine epsilonFine_nonneg fine_small hradius, map_add]

end

end YangMills.RG
