/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceBlockTranslation
import YangMills.RG.BalabanCMP99OneScaleBlockPoincare

/-!
# Exact decomposition of the CMP99 coarse covariant derivative

The physical `Ubar` link is an exponential of an averaged logarithm.  It is
therefore not equal pointwise to the three-contour holonomy attached to one
fine site.  This module keeps the resulting remainder literal: the coarse
covariant derivative of the block average is the averaged straight defect
plus the average difference between those two adjoint transports.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig
open scoped BigOperators

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The target field, transported from the translated fine site to the target
coarse basepoint, but indexed by the corresponding source-block site. -/
noncomputable def cmp99SourceTargetTransportedValue
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d)
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) : SUNLieCoord Nc :=
  rho.adCLM
    (cmp99ContourHolonomy
      (cmp99BlockContainedContourSystem (G := SUN Nc)) U
      (y.shift mu) (cmp99SourceTranslatedSite x.1 mu))
    (phi (cmp99SourceTranslatedSite x.1 mu))

/-- Reindex the literal target block average by the source-to-target
translation. -/
theorem cmp99FullSourceBlockAverageValue_target_eq_source_sum
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d) :
    cmp99FullSourceBlockAverageValue rho U phi (y.shift mu) =
      cmp99SourceBlockAverageWeight M d •
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
          cmp99SourceTargetTransportedValue rho U phi y mu x := by
  unfold cmp99FullSourceBlockAverageValue
  rw [sum_cmp99SourceBlockTranslationEquiv (M := M) y mu]
  rfl

/-- The three-contour holonomy from the source coarse basepoint to the target
coarse basepoint, indexed by a source-block fine site. -/
noncomputable def cmp99SourceTripleHolonomy
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d)
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) : SUN Nc :=
  cmp99ContourHolonomy
      (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1 *
    (cmp99SourceParallelTransportPath (G := SUN Nc)
      (M := M) (N' := N') x.1 mu).holonomy U *
    wilsonLine U (cmp99SourceUbarGamma3 (G := SUN Nc) (y, mu) x.1)

/-- The return contour is literally the inverse of the target block contour. -/
theorem wilsonLine_cmp99SourceUbarGamma3_eq_targetContour_inv
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d)
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) :
    wilsonLine U (cmp99SourceUbarGamma3 (G := SUN Nc) (y, mu) x.1) =
      (cmp99ContourHolonomy
        (cmp99BlockContainedContourSystem (G := SUN Nc)) U
        (y.shift mu) (cmp99SourceTranslatedSite x.1 mu))⁻¹ := by
  have hx' := cmp99SourceTranslatedSite_mem_targetBlock y mu x.1 x.2
  simp only [cmp99SourceUbarGamma3, dif_pos x.2,
    cmp99ContourHolonomy]
  rw [cmp99BlockContainedContourSystem_of_mem (G := SUN Nc)
    (y.shift mu) (cmp99SourceTranslatedSite x.1 mu) hx']
  exact OrientedLatticePath.holonomy_symm
    (concreteCMP99BlockContour (G := SUN Nc) (y.shift mu)
      ⟨cmp99SourceTranslatedSite x.1 mu, hx'⟩).path U

/-- Acting on the target-transported value by the three-contour holonomy
cancels the return contour and leaves the source plus straight transports. -/
theorem ad_cmp99SourceTripleHolonomy_targetTransportedValue
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d)
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) :
    rho.adCLM (cmp99SourceTripleHolonomy U y mu x)
        (cmp99SourceTargetTransportedValue rho U phi y mu x) =
      rho.adCLM
        (cmp99ContourHolonomy
          (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1)
        (rho.adCLM
          ((cmp99SourceParallelTransportPath (G := SUN Nc)
            (M := M) (N' := N') x.1 mu).holonomy U)
          (phi (cmp99SourceTranslatedSite x.1 mu))) := by
  rw [cmp99SourceTripleHolonomy, cmp99SourceTargetTransportedValue,
    wilsonLine_cmp99SourceUbarGamma3_eq_targetContour_inv]
  simp only [rho.ad_mul, ContinuousLinearMap.comp_apply,
    rho.ad_inv_apply_ad]

/-- The averaged straight defect is the source average minus the target
values transported by the site-dependent three-contour holonomies. -/
theorem cmp99SourceParallelAverageDefectValue_eq_source_sub_tripleTarget
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d) :
    cmp99SourceParallelAverageDefectValue rho U phi y mu =
      cmp99FullSourceBlockAverageValue rho U phi y -
        cmp99SourceBlockAverageWeight M d •
          ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
            rho.adCLM (cmp99SourceTripleHolonomy U y mu x)
              (cmp99SourceTargetTransportedValue rho U phi y mu x) := by
  have hsum :
      (∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
        rho.adCLM
          (cmp99ContourHolonomy
            (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1)
          (rho.adCLM
            ((cmp99SourceParallelTransportPath (G := SUN Nc)
              (M := M) (N' := N') x.1 mu).holonomy U)
            (phi (cmp99SourceTranslatedSite x.1 mu)))) =
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
          rho.adCLM (cmp99SourceTripleHolonomy U y mu x)
            (cmp99SourceTargetTransportedValue rho U phi y mu x) := by
    apply Finset.sum_congr rfl
    intro x _hx
    exact
      (ad_cmp99SourceTripleHolonomy_targetTransportedValue
        rho U phi y mu x).symm
  unfold cmp99SourceParallelAverageDefectValue
  unfold cmp99FullSourceBlockAverageValue
  simp only [map_sub, Finset.sum_sub_distrib, smul_sub]
  rw [hsum]

/-- Pointwise difference between the literal three-contour transport and a
chosen coarse background transport.  For the physical application `V` is the
constructed `Ubar` background. -/
noncomputable def cmp99SourceCoarseTransportRemainderValue
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d)
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) : SUNLieCoord Nc :=
  rho.adCLM (cmp99SourceTripleHolonomy U y mu x)
      (cmp99SourceTargetTransportedValue rho U phi y mu x) -
    rho.adCLM (V (positiveEdgeOfPhysicalBond (y, mu)))
      (cmp99SourceTargetTransportedValue rho U phi y mu x)

/-- Source-normalized average of the literal coarse-transport mismatch. -/
noncomputable def cmp99SourceCoarseTransportRemainder
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d) : SUNLieCoord Nc :=
  cmp99SourceBlockAverageWeight M d •
    ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
      cmp99SourceCoarseTransportRemainderValue rho U V phi y mu x

/-- Exact source-faithful decomposition.  The coarse covariant derivative of
the block average is the averaged straight defect plus the explicit mismatch
between each three-contour holonomy and the coarse link. -/
theorem covariantD0_cmp99FullSourceBlockAverage_eq_defect_add_remainder
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d) :
    covariantD0CLM rho V (cmp99FullSourceBlockAverage rho U phi) (y, mu) =
      cmp99SourceParallelAverageDefectValue rho U phi y mu +
        cmp99SourceCoarseTransportRemainder rho U V phi y mu := by
  rw [covariantD0CLM_apply, cmp99FullSourceBlockAverage_apply,
    cmp99FullSourceBlockAverage_apply,
    cmp99FullSourceBlockAverageValue_target_eq_source_sum,
    cmp99SourceParallelAverageDefectValue_eq_source_sub_tripleTarget]
  simp only [cmp99SourceCoarseTransportRemainder,
    cmp99SourceCoarseTransportRemainderValue, map_smul, map_sum,
    Finset.sum_sub_distrib, smul_sub]
  abel

end

end YangMills.RG
