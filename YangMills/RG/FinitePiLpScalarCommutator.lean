/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95SourceSmoothPartitionProfile
import YangMills.RG.FinitePiLpTypedCutoff

/-!
# Kernel of a scalar-cutoff commutator

This is the exact algebra behind Balaban's `K(h) = h Delta' - Delta' h`.
On a one-site probe, the commutator kernel is the precision kernel multiplied
by `h(target) - h(source)`.  Combining this identity with the scaled tensor
slope from (1.118) exposes the genuine `M0⁻¹` factor before any Green
operator is attached.
-/

namespace YangMills.RG

noncomputable section

/-- The literal commutator of a scalar multiplier with a finite-field
operator. -/
def finitePiLpScalarCommutator
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :=
  (finitePiLpScalarMultiplier (g := g) h).comp A -
    A.comp (finitePiLpScalarMultiplier (g := g) h)

/-- Exact entry formula: the cutoff commutator inserts only the scalar
difference between target and source. -/
theorem finitePiLpScalarCommutator_single_apply
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (source target : ι) (v : g) :
    finitePiLpScalarCommutator h A (singleFinitePiLp source v) target =
      (h target - h source) • A (singleFinitePiLp source v) target := by
  rw [finitePiLpScalarCommutator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  change h target • A (singleFinitePiLp source v) target -
      A ((finitePiLpScalarMultiplier (g := g) h)
        (singleFinitePiLp source v)) target = _
  rw [finitePiLpScalarMultiplier_single]
  have hsingle : singleFinitePiLp source (h source • v) =
      h source • singleFinitePiLp source v := by
    apply PiLp.ext
    intro i
    by_cases hi : i = source
    · subst i
      simp
    · simp [singleFinitePiLp_of_ne, hi]
  rw [hsingle, map_smul, PiLp.smul_apply]
  rw [sub_smul]

/-- Any entrywise kernel estimate for `A` gives the corresponding exact
cutoff-difference estimate for `[h,A]`. -/
theorem finitePiLpScalarCommutator_kernelBound
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (weight : ι → ι → ℝ)
    (hA : FinitePiLpKernelBound A weight) :
    FinitePiLpKernelBound (finitePiLpScalarCommutator h A)
      (fun target source => ‖h target - h source‖ * weight target source) := by
  intro source target v
  rw [finitePiLpScalarCommutator_single_apply, norm_smul]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left (hA source target v)
      (norm_nonneg (h target - h source)))

/-- Source-scaled specialization.  The `M0⁻¹` gain is generated from the
literal tensor cutoff, not supplied as a commutator hypothesis. -/
theorem finitePiLpScalarCommutator_tensorCutoff_kernelBound
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    {d : ℕ} (P : CMP95SourceSmoothPartitionProfile)
    {M0 : ℝ} (hM0 : 0 < M0) (z : Fin d → ℝ)
    (coord : ι → Fin d → ℝ)
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (weight : ι → ι → ℝ)
    (hweight : ∀ target source, 0 ≤ weight target source)
    (hA : FinitePiLpKernelBound A weight) :
    FinitePiLpKernelBound
      (finitePiLpScalarCommutator
        (fun x => P.tensorCutoff M0 z (coord x)) A)
      (fun target source =>
        ((P.derivBound / M0) *
          ∑ μ, ‖coord target μ - coord source μ‖) *
            weight target source) := by
  intro source target v
  have hentry := finitePiLpScalarCommutator_kernelBound (g := g)
    (fun x => P.tensorCutoff M0 z (coord x)) A weight hA source target v
  have hslope := P.norm_tensorCutoff_sub_tensorCutoff_le hM0 z
    (coord source) (coord target)
  calc
    ‖finitePiLpScalarCommutator
        (fun x => P.tensorCutoff M0 z (coord x)) A
        (singleFinitePiLp source v) target‖ ≤
      ‖P.tensorCutoff M0 z (coord target) -
        P.tensorCutoff M0 z (coord source)‖ *
          weight target source * ‖v‖ := hentry
    _ ≤ ((P.derivBound / M0) *
        ∑ μ, ‖coord target μ - coord source μ‖) *
          weight target source * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hslope (hweight target source))
        (norm_nonneg v)

end
end YangMills.RG
