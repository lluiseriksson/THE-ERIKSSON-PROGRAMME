import YangMills.RG.BalabanCMP99SourceFlowPhysicalGreenRealSlice
import YangMills.RG.BalabanCMP99SourceFlowPhysicalOwnerDictionary
import YangMills.RG.BalabanCMP99SourceFlowPhysicalPointProbe
import YangMills.RG.BalabanCMP99SourceFlowFullPointSourceFibreBound
import YangMills.RG.BalabanCMP85SourceFullGreenUniformAmplitude
import YangMills.RG.FinitePiLpOwnerFibreAction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# PRE-VALIDATION: literal full ambient Green action on one source-owner fibre

Source present; .olean not materialized; result not compiler-verified.
The three promoted physical dependencies are currently in their separate
cold gate at b2d5df8ad. This draft is NOT part of that immutable queue.
Run the isolated normalization repro first and only test this draft after
the physical prefix passes. No proof is imported from a free Green family.

The output/source orientation is exact, via the named symmetry of the
distance only. One source fibre has R^4 sites; F4 supplies R^-2 and the
action retains R^2. Constants are chosen before depth, K, Q and Nc.
This is the full ambient value action, not the inverse on a proper regional
carrier, not any derivative estimate, and not uniform regional B0.
Counters20/41,TermSource0,window15 unattained.
-/

namespace YangMills.RG
open YangMills
noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance physicalValueDraft_ambientNeZero (depth : ℕ) :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨by
    unfold cmp99SourceSeparatedLargeBlockSide
    exact mul_ne_zero
      (mul_ne_zero (NeZero.ne K) (pow_ne_zero _ (NeZero.ne L)))
      (mul_ne_zero (by decide) (NeZero.ne Q))⟩

/-- Literal real Green point probes, with output owner first in the metric.
Only individual Lie-fibre norms cross the real/complex dictionary. -/
theorem cmp99SourceFlowPhysicalRealGreen_typedKernel_draft
    (hL : 2 ≤ L) (depth : ℕ) {a rho : ℝ} (ha : 0 < a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho) :
    FinitePiLpTypedKernelBound
      (ι := FinBox 4 (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (κ := FinBox 4 (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (g := SUNLieCoord Nc)
      (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)
      (fun target source =>
        cmp99PhysicalFullGreenOwnerAmplitude (L ^ (depth + 1))
          (cmp99SourceFlowFlatFullComplexA a L depth) rho *
        Real.exp (-(rho * (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth target)
          (cmp99Eq389SourceLocalizationOwner L K Q depth source) : ℝ)))) := by
  classical
  intro source target v
  have h := norm_cmp99SourceFlowFullPointSourceGreen_fibre_le_owner
    (L := L) (Kloc := K) (Q := Q) (Nc := Nc)
    hL depth ha hrho hamplitude hradius hdenWindow hpairWindow
    (cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth source)
    (cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth target)
    (cmp99SUNLieCoordComplexificationLM Nc v)
  have hnorm := norm_cmp99SourceFlowPhysicalStep7bGreen_ofReal_apply
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth ha (singleFinitePiLp source v) target
  rw [cmp99PhysicalStep7b_complexSingle_eq_pointSource] at hnorm
  rw [hnorm, norm_cmp99SUNLieCoordComplexificationLM] at h
  simp only [cmp99PhysicalStep7b_blockSite_eq_sourceLocalizationOwner] at h
  rw [finBoxDist_comm
    (cmp99Eq389SourceLocalizationOwner L K Q depth source)
    (cmp99Eq389SourceLocalizationOwner L K Q depth target)] at h
  simpa only [neg_mul] using h

/-- One complete source fibre costs exactly R^4. With a supplied F4
inverse-square budget the resulting value-action amplitude is C R^2.
The next theorem supplies that budget uniformly rather than assuming it. -/
theorem cmp99SourceFlowPhysicalRealGreen_ownerAction_of_budget_draft
    (hL : 2 ≤ L) (depth : ℕ) {a rho C : ℝ} (ha : 0 < a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hC : 0 ≤ C)
    (hbudget : cmp99PhysicalFullGreenOwnerAmplitude (L ^ (depth + 1))
      (cmp99SourceFlowFlatFullComplexA a L depth) rho ≤
        C * (((L ^ (depth + 1) : ℕ) : ℝ) ^ 2)⁻¹) :
    CMP99Eq389SourceLocalizedActionBound (L := L) (K := K) (Q := Q)
      (g := SUNLieCoord Nc) depth
      (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)
      (C * (((L ^ (depth + 1) : ℕ) : ℝ) ^ 2)) rho := by
  classical
  have hk := cmp99SourceFlowPhysicalRealGreen_typedKernel_draft
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth ha hrho hamplitude hradius hdenWindow hpairWindow
  have hA : 0 ≤ C * (((L ^ (depth + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
    positivity
  have haction := finitePiLpTypedBlockLocalizedSupBound_of_kernel_fibre_card
    (ι := FinBox 4 (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (κ := FinBox 4 (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (β := FinBox 4 (2 * (K * Q))) (g := SUNLieCoord Nc)
    (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)
    (cmp99Eq389SourceLocalizationOwner L K Q depth)
    (cmp99Eq389SourceLocalizationOwner L K Q depth)
    finBoxDist ((L ^ (depth + 1)) ^ 4) hA hrho
    (fun owner => (card_cmp99SourceLocalizationOwner_fibre
      (L := L) (K := K) (Q := Q) depth owner).le)
    (by
      intro source target v
      exact (hk source target v).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbudget (Real.exp_pos _).le)
          (norm_nonneg v)))
  have hscale :
      (((L ^ (depth + 1)) ^ 4 : ℕ) : ℝ) *
          (C * (((L ^ (depth + 1) : ℕ) : ℝ) ^ 2)⁻¹) =
        C * (((L ^ (depth + 1) : ℕ) : ℝ) ^ 2) := by
    have hR : ((L ^ (depth + 1) : ℕ) : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (pow_pos (NeZero.pos L) _)).ne'
    rw [Nat.cast_pow]
    field_simp [hR] <;> ring
  rw [hscale] at haction
  exact haction

/-- A single radius and C work before depth and volume parameters are
chosen. The amplitude remains C times the square of the fine block side,
not a scale-free constant and not a bound for the regional inverse. -/
theorem exists_cmp99SourceFlowPhysicalRealGreen_uniformValueAction_draft
    {a : ℝ} (ha : 0 < a) (hL : 2 ≤ L) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧
      ∀ (K Q Nc : ℕ) [NeZero K] [NeZero Q] [NeZero Nc] (depth : ℕ),
        CMP99Eq389SourceLocalizedActionBound (L := L) (K := K) (Q := Q)
          (g := SUNLieCoord Nc) depth
          (cmp99SourceSeparatedSourceFlowFlatAmbientGreen
            (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha)
          (C * (((L ^ (depth + 1) : ℕ) : ℝ) ^ 2)) rho := by
  obtain ⟨rho, C, hrho, hC, hamp, hrad, hp, hdepth⟩ :=
    exists_cmp85SourceFullGreen_uniformOwnerAmplitude ha hL
  refine ⟨rho, C, hrho, hC, ?_⟩
  intro K Q Nc instK instQ instNc depth
  exact cmp99SourceFlowPhysicalRealGreen_ownerAction_of_budget_draft
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth ha hrho hamp hrad
    (by simpa only [cmp99SourceFlowFlatFullComplexA] using (hdepth depth).1)
    hp hC.le
    (by simpa only [cmp99SourceFlowFlatFullComplexA] using (hdepth depth).2)

#print axioms cmp99SourceFlowPhysicalRealGreen_typedKernel_draft
#print axioms cmp99SourceFlowPhysicalRealGreen_ownerAction_of_budget_draft
#print axioms exists_cmp99SourceFlowPhysicalRealGreen_uniformValueAction_draft

end
end YangMills.RG
