/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq342SourceLocalizedInputL2
import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge
import YangMills.RG.FinitePiLpTiltedInverseAction

/-!
# One-owner tilted input for CMP99 (3.42)

The arbitrary-input inverse action retains the counting-L2 norm of the
rooted tilt.  This file bounds that norm for a field supported in one source
owner.  The owner diameter contributes one exponential and the already
sealed four-dimensional conversion contributes exactly
`L^(2 * (depth + 1))`; there is no expansion into coordinate probes and no
second source-cardinality factor.
-/

namespace YangMills.RG

noncomputable section

/-- A field supported in one owner pays only the largest tilt inside that
owner.  This is the generic norm step before the physical `ell^2` conversion.
-/
theorem norm_finitePiLpTiltCLM_le_exp_diameter_mul_norm_of_supportedInOwner
    {ι β g : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (sourceOwner : ι → β) (owner : β)
    (root : ι) (diameter : ℕ) {rate : ℝ} (hrate : 0 ≤ rate)
    (f : FinitePiLpField ι g)
    (hf : FinitePiLpSupportedInOwner sourceOwner owner f)
    (hdiameter : ∀ source, sourceOwner source = owner →
      dist root source ≤ diameter) :
    ‖finitePiLpTiltCLM (g := g) dist rate root f‖ ≤
      Real.exp (rate * (diameter : ℝ)) * ‖f‖ := by
  classical
  simp only [PiLp.norm_eq_of_L2]
  have hsum :
      (∑ source : ι,
          ‖finitePiLpTiltCLM (g := g) dist rate root f source‖ ^ 2) ≤
        Real.exp (rate * (diameter : ℝ)) ^ 2 *
          ∑ source : ι, ‖f source‖ ^ 2 := by
    calc
      (∑ source : ι,
          ‖finitePiLpTiltCLM (g := g) dist rate root f source‖ ^ 2) ≤
          ∑ source : ι,
            (Real.exp (rate * (diameter : ℝ)) * ‖f source‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro source _hsource
        have hpoint :
            ‖finitePiLpTiltCLM (g := g) dist rate root f source‖ ≤
              Real.exp (rate * (diameter : ℝ)) * ‖f source‖ := by
          by_cases howner : sourceOwner source = owner
          · rw [finitePiLpTiltCLM_apply, norm_smul, Real.norm_eq_abs,
              Real.abs_exp]
            have hdistReal :
                (dist root source : ℝ) ≤ (diameter : ℝ) := by
              exact_mod_cast hdiameter source howner
            exact mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr
                (mul_le_mul_of_nonneg_left hdistReal hrate))
              (norm_nonneg (f source))
          · rw [finitePiLpTiltCLM_apply, hf source howner, smul_zero,
              norm_zero]
            positivity
        exact pow_le_pow_left₀
          (norm_nonneg
            (finitePiLpTiltCLM (g := g) dist rate root f source))
          hpoint 2
      _ = Real.exp (rate * (diameter : ℝ)) ^ 2 *
          ∑ source : ι, ‖f source‖ ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
  calc
    Real.sqrt (∑ source : ι,
        ‖finitePiLpTiltCLM (g := g) dist rate root f source‖ ^ 2) ≤
        Real.sqrt (Real.exp (rate * (diameter : ℝ)) ^ 2 *
          ∑ source : ι, ‖f source‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Real.exp (rate * (diameter : ℝ)) ^ 2) *
        Real.sqrt (∑ source : ι, ‖f source‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _)]
    _ = Real.exp (rate * (diameter : ℝ)) *
        Real.sqrt (∑ source : ι, ‖f source‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Physical one-owner tilt at source-localization scale
`ell = L^(depth+1)`.  The within-owner diameter is `ell - 1` and the only
counting-L2/sup conversion is the sealed factor `ell^2`. -/
theorem norm_cmp99Eq342_sourceLocalizedTilt_le_sourceScale
    (depth : ℕ)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (owner : FinBox 4 (2 * (K * Q)))
    (root : ActiveGaugeRegion.Site Omega)
    (hroot : cmp99Eq342SourceLocalizedActiveOwner L K Q depth root = owner)
    {rate : ℝ} (hrate : 0 ≤ rate)
    (f : FinitePiLpField (ActiveGaugeRegion.Site Omega) (SUNLieCoord Nc))
    (hf : FinitePiLpSupportedInOwner
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth) owner f) :
    ‖finitePiLpTiltCLM (g := SUNLieCoord Nc)
        (fun target source : ActiveGaugeRegion.Site Omega =>
          finBoxDist target.1 source.1)
        rate root f‖ ≤
      Real.exp (rate * ((L ^ (depth + 1) - 1 : ℕ) : ℝ)) *
        (L ^ (depth + 1) : ℝ) ^ 2 * finitePiLpSupNorm f := by
  let ell := L ^ (depth + 1)
  let n := 2 * (K * Q)
  let e := cmp99Eq389SourceLocalizationSiteEquiv L K Q depth
  have htilt :=
    norm_finitePiLpTiltCLM_le_exp_diameter_mul_norm_of_supportedInOwner
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth) owner root
      (L ^ (depth + 1) - 1) hrate f hf
      (fun source hsource => by
        have hsameBlocks :
            blockSite ell n (e root.1) = blockSite ell n (e source.1) := by
          simpa [ell, n, e, cmp99Eq342SourceLocalizedActiveOwner,
            cmp99Eq389SourceLocalizationOwner] using
              hroot.trans hsource.symm
        have hwithin :
            finBoxDist (e root.1) (e source.1) ≤ ell - 1 :=
          finBoxDist_le_of_same_block (e root.1) (e source.1) hsameBlocks
        have hcast := finBoxDist_equivCast_size
          (cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier
            L K Q depth) root.1 source.1
        calc
          finBoxDist root.1 source.1 =
              finBoxDist (e root.1) (e source.1) := by
            simpa [e] using hcast.symm
          _ ≤ L ^ (depth + 1) - 1 := by simpa [ell] using hwithin)
  have hinput := norm_finitePiLp_le_cmp99Eq342_sourceScale_mul_supNorm
    (L := L) (K := K) (Q := Q) (Nc := Nc) depth Omega owner f hf
  calc
    ‖finitePiLpTiltCLM (g := SUNLieCoord Nc)
        (fun target source : ActiveGaugeRegion.Site Omega =>
          finBoxDist target.1 source.1)
        rate root f‖ ≤
        Real.exp (rate * ((L ^ (depth + 1) - 1 : ℕ) : ℝ)) * ‖f‖ := htilt
    _ ≤ Real.exp (rate * ((L ^ (depth + 1) - 1 : ℕ) : ℝ)) *
        ((L ^ (depth + 1) : ℝ) ^ 2 * finitePiLpSupNorm f) :=
      mul_le_mul_of_nonneg_left hinput (Real.exp_pos _).le
    _ = Real.exp (rate * ((L ^ (depth + 1) - 1 : ℕ) : ℝ)) *
        (L ^ (depth + 1) : ℝ) ^ 2 * finitePiLpSupNorm f := by ring

end

end YangMills.RG
