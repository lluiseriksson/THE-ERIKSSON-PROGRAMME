/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicFixedPointFirstJet
import YangMills.RG.LocalSecondJetFromDerivativeLipschitz

/-!
# Second joint jet of the intrinsic CMP102 fixed-point source

The source derivative-Lipschitz estimate is promoted to a second-jet
bound at an interior physical chart point.  The required slack is stated
only in the source radius and no-winding inequalities; no second-jet
budget is supplied by the caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator Topology

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
  [NeZero (M * N')]

local instance cmp102SecondJetCoordCLMNorm :
    Norm (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102SecondJetCoordCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102SecondJetCoordCLMNormedSpace :
    NormedSpace ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1000000 in
/-- **Physical second-joint-jet producer.**  At an interior point of the
literal CMP102 source chart, the norm of `D²T` is bounded by the existing
source-generated derivative-Lipschitz constant. -/
theorem
    norm_iteratedFDeriv_two_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d M N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (p : FinePhysicalOneCochain d M N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc)
    {r z₀ z s : ℝ}
    (hr : 0 ≤ r)
    (hp : ‖cmp102PhysicalCochainToAmbientCLM
      (cmp102PhysicalBackgroundShiftCLM
        U ha hP hε hsmall hbudget p)‖ < r)
    (hz13 : 1 / 3 ≤ z) (hz₀z : z₀ < z) (hz1 : z < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hDp : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget p))‖ ≤ z₀)
    (hdev :
      cmp102SourceAmbientRelativeDeviationValueBudget d M r z ≤ s) :
    ‖iteratedFDeriv ℝ 2
      (cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
        U ha hP hε hsmall hbudget) p‖ ≤
      cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
        U ha hP hε hsmall hbudget r z s := by
  let source :
      (FinePhysicalOneCochain d M N' Nc ×
        PhysicalGaugeOneCochainSup d N' Nc) →L[ℝ]
          PhysicalAmbientMatrixTangent d (M * N') Nc :=
    cmp102PhysicalCochainToAmbientCLM.comp
      (cmp102PhysicalBackgroundShiftCLM
        U ha hP hε hsmall hbudget)
  let T :=
    cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
      U ha hP hε hsmall hbudget
  let B :=
    cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget
      U ha hP hε hsmall hbudget r z s
  let L := cmp102SourceFourContourDeviationValueLipschitzBudget d M r
  have hB0 : 0 ≤ B := by
    exact
      cmp102SourceIntrinsicPhysicalBackgroundCorrectionMapDerivativeLipschitzBudget_nonneg
        U ha hP hε hsmall hbudget hr
          ((by norm_num : (0 : ℝ) ≤ 1 / 3).trans hz13) hs0
  have hp_source : ‖source p‖ < r := by
    simpa [source, ContinuousLinearMap.comp_apply] using hp
  have hsource :
      ∀ᶠ q in 𝓝 p, ‖source q‖ ≤ r := by
    have hc : ContinuousAt (fun q => ‖source q‖) p :=
      source.continuous.continuousAt.norm
    exact (hc.eventually (Iio_mem_nhds hp_source)).mono
      (fun _ hq => hq.le)
  have hgap : 0 < z - z₀ := sub_pos.mpr hz₀z
  have hclose :
      ∀ᶠ q in 𝓝 p, L * ‖source q - source p‖ ≤ z - z₀ := by
    have hc : ContinuousAt (fun q => L * ‖source q - source p‖) p :=
      continuousAt_const.mul
        ((source.continuous.continuousAt.sub continuousAt_const).norm)
    have he :
        ∀ᶠ q in 𝓝 p, L * ‖source q - source p‖ < z - z₀ := by
      exact hc.eventually
        (show Set.Iio (z - z₀) ∈
            𝓝 (L * ‖source p - source p‖) by
          simpa using (Iio_mem_nhds hgap))
    exact he.mono (fun _ hq => hq.le)
  have hlip :
      ∀ᶠ q in 𝓝 p, ‖fderiv ℝ T q - fderiv ℝ T p‖ ≤
        B * ‖q - p‖ := by
    filter_upwards [hsource, hclose] with q hq_source hq_close
    have hDq : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
        ‖cmp98UbarAmbientDeviationMatrix U b x (source q)‖ ≤ z := by
      intro b x hx
      have hdiff :=
        norm_cmp98UbarAmbientDeviationMatrix_sub_le_sourceLengthBudget
          U b x hx (source q) (source p) hr hq_source hp_source.le
      calc
        ‖cmp98UbarAmbientDeviationMatrix U b x (source q)‖
            ≤ ‖cmp98UbarAmbientDeviationMatrix U b x (source q) -
                cmp98UbarAmbientDeviationMatrix U b x (source p)‖ +
              ‖cmp98UbarAmbientDeviationMatrix U b x (source p)‖ := by
                simpa only [sub_add_cancel] using
                  norm_add_le
                    (cmp98UbarAmbientDeviationMatrix U b x (source q) -
                      cmp98UbarAmbientDeviationMatrix U b x (source p))
                    (cmp98UbarAmbientDeviationMatrix U b x (source p))
        _ ≤ L * ‖source q - source p‖ + z₀ :=
          add_le_add hdiff (by simpa [source, ContinuousLinearMap.comp_apply] using hDp b x hx)
        _ ≤ (z - z₀) + z₀ := by linarith
        _ = z := by ring
    have hDp' : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
        ‖cmp98UbarAmbientDeviationMatrix U b x (source p)‖ ≤ z := by
      intro b x hx
      exact (by
        simpa [source, ContinuousLinearMap.comp_apply] using
          (hDp b x hx).trans hz₀z.le)
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB0 (norm_nonneg _))
    intro R
    simpa [T, B, source, ContinuousLinearMap.comp_apply] using
      (norm_fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_sub_apply_le_sourceBudget
        (d := d) (L := M) (N' := N') (Nc := Nc)
        U ha hP hε hsmall hbudget q p R
        hr hz13 hz1 hs0 hs1
        (by simpa [source, ContinuousLinearMap.comp_apply] using hq_source)
        (by simpa [source, ContinuousLinearMap.comp_apply] using hp_source.le)
        hbase
        (by simpa [source, ContinuousLinearMap.comp_apply] using hDq)
        (by simpa [source, ContinuousLinearMap.comp_apply] using hDp')
        hdev)
  simpa [T, B] using
    (norm_iteratedFDeriv_two_le_of_eventually_fderiv_lipschitz
      T p hB0 hlip)

end

end YangMills.RG
