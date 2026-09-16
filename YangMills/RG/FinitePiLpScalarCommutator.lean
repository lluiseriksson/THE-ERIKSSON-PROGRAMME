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

/-- A linear distance factor can be absorbed by spending half of a positive
exponential rate.  This is the scalar estimate used in the passage from the
`M0⁻¹` cutoff slope to the source decay in CMP95 (1.128) and CMP99 (3.89). -/
theorem mul_exp_neg_le_two_div_mul_exp_neg_half
    {rate r : ℝ} (hrate : 0 < rate) (hr : 0 ≤ r) :
    r * Real.exp (-(rate * r)) ≤
      (2 / rate) * Real.exp (-((rate / 2) * r)) := by
  have hone : 1 + (rate / 2) * r ≤ Real.exp ((rate / 2) * r) :=
    by simpa [add_comm] using Real.add_one_le_exp ((rate / 2) * r)
  have hr_le : r ≤ (2 / rate) * Real.exp ((rate / 2) * r) := by
    have htwo_rate : 0 ≤ 2 / rate := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hone htwo_rate
    calc
      r ≤ (2 / rate) * (1 + (rate / 2) * r) := by
        have hid : (2 / rate) * (1 + (rate / 2) * r) = 2 / rate + r := by
          field_simp
        rw [hid]
        exact le_add_of_nonneg_left htwo_rate
      _ ≤ (2 / rate) * Real.exp ((rate / 2) * r) := hscaled
  calc
    r * Real.exp (-(rate * r)) ≤
        ((2 / rate) * Real.exp ((rate / 2) * r)) *
          Real.exp (-(rate * r)) :=
      mul_le_mul_of_nonneg_right hr_le (Real.exp_pos _).le
    _ = (2 / rate) * Real.exp (-((rate / 2) * r)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

/-- A Lipschitz scalar cutoff preserves exponential localization of a
kernel, at half the input rate.  The amplitude is fully explicit. -/
theorem finitePiLpScalarCommutator_exponentialKernelBound_of_lipschitz
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (dist : ι → ι → ℕ) {amplitude rate lipschitz : ℝ}
    (hlipschitz : 0 ≤ lipschitz)
    (hh : ∀ target source,
      ‖h target - h source‖ ≤
        lipschitz * (dist target source : ℝ))
    (hA : FinitePiLpExponentialKernelBound A dist amplitude rate) :
    FinitePiLpExponentialKernelBound
      (finitePiLpScalarCommutator h A) dist
      ((2 * lipschitz * amplitude) / rate) (rate / 2) := by
  refine ⟨div_nonneg (mul_nonneg (mul_nonneg zero_le_two hlipschitz) hA.1)
      hA.2.1.le, div_pos hA.2.1 zero_lt_two, ?_⟩
  intro source target v
  have hentry := finitePiLpScalarCommutator_single_apply h A source target v
  rw [hentry, norm_smul]
  have hbase := hA.2.2 source target v
  have hdist : (0 : ℝ) ≤ dist target source := by positivity
  have habsorb := mul_exp_neg_le_two_div_mul_exp_neg_half hA.2.1 hdist
  calc
    ‖h target - h source‖ *
        ‖A (singleFinitePiLp source v) target‖ ≤
      (lipschitz * (dist target source : ℝ)) *
        (amplitude * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖) :=
      mul_le_mul (hh target source) hbase (norm_nonneg _) (by positivity)
    _ = (lipschitz * amplitude) *
        ((dist target source : ℝ) *
          Real.exp (-(rate * (dist target source : ℝ)))) * ‖v‖ := by ring
    _ ≤ (lipschitz * amplitude) *
        ((2 / rate) *
          Real.exp (-((rate / 2) * (dist target source : ℝ)))) * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left habsorb
          (mul_nonneg hlipschitz hA.1)) (norm_nonneg v)
    _ = ((2 * lipschitz * amplitude) / rate) *
        Real.exp (-((rate / 2) * (dist target source : ℝ))) * ‖v‖ := by ring

/-- Source-specialized exponential commutator estimate.  The only remaining
geometric input is the comparison between the literal fine coordinates and
the chosen CMP99 distance; the analytic `M0⁻¹` gain is derived internally. -/
theorem finitePiLpScalarCommutator_tensorCutoff_exponentialKernelBound
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    {d : ℕ} (P : CMP95SourceSmoothPartitionProfile)
    {M0 : ℝ} (hM0 : 0 < M0) (z : Fin d → ℝ)
    (coord : ι → Fin d → ℝ) (dist : ι → ι → ℕ)
    {coordConstant : ℝ} (hcoordConstant : 0 ≤ coordConstant)
    (hcoord : ∀ target source,
      (∑ μ, ‖coord target μ - coord source μ‖) ≤
        coordConstant * (dist target source : ℝ))
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    {amplitude rate : ℝ}
    (hA : FinitePiLpExponentialKernelBound A dist amplitude rate) :
    FinitePiLpExponentialKernelBound
      (finitePiLpScalarCommutator
        (fun x => P.tensorCutoff M0 z (coord x)) A)
      dist
      ((2 * ((P.derivBound / M0) * coordConstant) * amplitude) / rate)
      (rate / 2) := by
  apply finitePiLpScalarCommutator_exponentialKernelBound_of_lipschitz
    (h := fun x => P.tensorCutoff M0 z (coord x))
    (A := A) (dist := dist)
  · exact mul_nonneg (div_nonneg P.derivBound_nonneg hM0.le) hcoordConstant
  · intro target source
    refine (P.norm_tensorCutoff_sub_tensorCutoff_le hM0 z
      (coord source) (coord target)).trans ?_
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (hcoord target source)
        (div_nonneg P.derivBound_nonneg hM0.le))
  · exact hA

/-- The source orientation `[A,h] = A h - h A`.  CMP99 p. 412 uses this
orientation with `A = G'` and the scalar multiplier `(h')²`. -/
def finitePiLpOperatorScalarCommutator
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (h : ι → ℝ) :=
  A.comp (finitePiLpScalarMultiplier (g := g) h) -
    (finitePiLpScalarMultiplier (g := g) h).comp A

/-- Reversing the commutator orientation only changes its sign.  Keeping this
identity explicit lets source formulas use Balaban's printed `[A,h]`
orientation while reusing estimates proved for `[h,A]`. -/
theorem finitePiLpOperatorScalarCommutator_eq_neg
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (h : ι → ℝ) :
    finitePiLpOperatorScalarCommutator A h =
      -finitePiLpScalarCommutator h A := by
  unfold finitePiLpOperatorScalarCommutator finitePiLpScalarCommutator
  abel

/-- Exact entry formula in the source orientation. -/
theorem finitePiLpOperatorScalarCommutator_single_apply
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (h : ι → ℝ) (source target : ι) (v : g) :
    finitePiLpOperatorScalarCommutator A h
        (singleFinitePiLp source v) target =
      (h source - h target) • A (singleFinitePiLp source v) target := by
  rw [finitePiLpOperatorScalarCommutator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  change A ((finitePiLpScalarMultiplier (g := g) h)
      (singleFinitePiLp source v)) target -
      h target • A (singleFinitePiLp source v) target = _
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

/-- Squaring a contractive Lipschitz real cutoff costs at most a factor two
in its Lipschitz constant. -/
theorem norm_sq_sub_sq_le_two_mul
    {a b lipschitz distance : ℝ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hlipschitz : ‖b - a‖ ≤ lipschitz * distance) :
    ‖b ^ 2 - a ^ 2‖ ≤ (2 * lipschitz) * distance := by
  rw [show b ^ 2 - a ^ 2 = (b - a) * (b + a) by ring, norm_mul]
  calc
    ‖b - a‖ * ‖b + a‖ ≤
        (lipschitz * distance) * (1 + 1) := by
      apply mul_le_mul hlipschitz
      · exact (norm_add_le b a).trans (add_le_add hb ha)
      · exact norm_nonneg _
      · have hnonneg : 0 ≤ lipschitz * distance :=
          (norm_nonneg (b - a)).trans hlipschitz
        exact hnonneg
    _ = (2 * lipschitz) * distance := by ring

/-- Exact exponential estimate for the source commutator `[A,h²]`. -/
theorem finitePiLpOperatorScalarCommutator_sq_exponentialKernelBound
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (dist : ι → ι → ℕ) {amplitude rate lipschitz : ℝ}
    (hlipschitz : 0 ≤ lipschitz)
    (hnorm : ∀ x, ‖h x‖ ≤ 1)
    (hh : ∀ target source,
      ‖h target - h source‖ ≤
        lipschitz * (dist target source : ℝ))
    (hA : FinitePiLpExponentialKernelBound A dist amplitude rate) :
    FinitePiLpExponentialKernelBound
      (finitePiLpOperatorScalarCommutator A (fun x => h x ^ 2)) dist
      ((4 * lipschitz * amplitude) / rate) (rate / 2) := by
  refine ⟨div_nonneg (mul_nonneg (mul_nonneg (by positivity) hlipschitz) hA.1)
      hA.2.1.le, div_pos hA.2.1 zero_lt_two, ?_⟩
  intro source target v
  rw [finitePiLpOperatorScalarCommutator_single_apply, norm_smul]
  have hsquare : ‖h source ^ 2 - h target ^ 2‖ ≤
      (2 * lipschitz) * (dist target source : ℝ) := by
    apply norm_sq_sub_sq_le_two_mul (hnorm target) (hnorm source)
    rw [show h source - h target = -(h target - h source) by ring, norm_neg]
    exact hh target source
  have hbase := hA.2.2 source target v
  have hdist : (0 : ℝ) ≤ dist target source := by positivity
  have habsorb := mul_exp_neg_le_two_div_mul_exp_neg_half hA.2.1 hdist
  calc
    ‖h source ^ 2 - h target ^ 2‖ *
        ‖A (singleFinitePiLp source v) target‖ ≤
      ((2 * lipschitz) * (dist target source : ℝ)) *
        (amplitude * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖) :=
      mul_le_mul hsquare hbase (norm_nonneg _) (by positivity)
    _ = ((2 * lipschitz) * amplitude) *
        ((dist target source : ℝ) *
          Real.exp (-(rate * (dist target source : ℝ)))) * ‖v‖ := by ring
    _ ≤ ((2 * lipschitz) * amplitude) *
        ((2 / rate) *
          Real.exp (-((rate / 2) * (dist target source : ℝ)))) * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left habsorb
          (mul_nonneg (mul_nonneg (by positivity) hlipschitz) hA.1))
        (norm_nonneg v)
    _ = ((4 * lipschitz * amplitude) / rate) *
        Real.exp (-((rate / 2) * (dist target source : ℝ))) * ‖v‖ := by ring

/-- The exact CMP95 tensor cutoff specialization of `[A,h²]`. -/
theorem finitePiLpOperatorScalarCommutator_tensorCutoff_sq_exponentialKernelBound
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    {d : ℕ} (P : CMP95SourceSmoothPartitionProfile)
    {M0 : ℝ} (hM0 : 0 < M0) (z : Fin d → ℝ)
    (coord : ι → Fin d → ℝ) (dist : ι → ι → ℕ)
    {coordConstant : ℝ} (hcoordConstant : 0 ≤ coordConstant)
    (hcoord : ∀ target source,
      (∑ μ, ‖coord target μ - coord source μ‖) ≤
        coordConstant * (dist target source : ℝ))
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    {amplitude rate : ℝ}
    (hA : FinitePiLpExponentialKernelBound A dist amplitude rate) :
    FinitePiLpExponentialKernelBound
      (finitePiLpOperatorScalarCommutator A
        (fun x => (P.tensorCutoff M0 z (coord x)) ^ 2))
      dist
      ((4 * ((P.derivBound / M0) * coordConstant) * amplitude) / rate)
      (rate / 2) := by
  apply finitePiLpOperatorScalarCommutator_sq_exponentialKernelBound
    (h := fun x => P.tensorCutoff M0 z (coord x))
    (A := A) (dist := dist)
  · exact mul_nonneg (div_nonneg P.derivBound_nonneg hM0.le) hcoordConstant
  · exact fun x => P.norm_tensorCutoff_le_one M0 z (coord x)
  · intro target source
    refine (P.norm_tensorCutoff_sub_tensorCutoff_le hM0 z
      (coord source) (coord target)).trans ?_
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (hcoord target source)
        (div_nonneg P.derivBound_nonneg hM0.le))
  · exact hA

/-- A symmetric exponential kernel bound and a volume-uniform exponential
row sum give the corresponding counting-Hilbert operator norm. -/
theorem finitePiLpOpNorm_le_of_exponentialKernelBound
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (dist : ι → ι → ℕ) (hsymm : ∀ x y, dist x y = dist y x)
    {amplitude rate rowSum : ℝ} (hrowSum : 0 ≤ rowSum)
    (hT : FinitePiLpExponentialKernelBound T dist amplitude rate)
    (hsum : ∀ x, ∑ y, Real.exp (-(rate * (dist x y : ℝ))) ≤ rowSum) :
    ‖T‖ ≤ amplitude * rowSum := by
  let weight : ι → ι → ℝ := fun target source =>
    amplitude * Real.exp (-(rate * (dist target source : ℝ)))
  have hweight : ∀ target source, 0 ≤ weight target source := fun _ _ =>
    mul_nonneg hT.1 (Real.exp_pos _).le
  have hrow : ∀ target, ∑ source, weight target source ≤
      amplitude * rowSum := by
    intro target
    change (∑ source, amplitude *
      Real.exp (-(rate * (dist target source : ℝ)))) ≤ amplitude * rowSum
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hsum target) hT.1
  have hcol : ∀ source, ∑ target, weight target source ≤
      amplitude * rowSum := by
    intro source
    have heq : (∑ target, weight target source) =
        amplitude * ∑ target,
          Real.exp (-(rate * (dist source target : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro target _
      change amplitude * Real.exp (-(rate * (dist target source : ℝ))) =
        amplitude * Real.exp (-(rate * (dist source target : ℝ)))
      rw [hsymm target source]
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hsum source) hT.1
  apply finitePiLpOpNorm_le_of_kernelBound_schur weight hweight
    (mul_nonneg hT.1 hrowSum) hrow hcol T
  exact hT.2.2

/-- Operator-norm `O(M0⁻¹)` estimate for the literal source commutator
`[A,h_z²]`.  The row-sum constant is volume independent in the later CMP99
instantiation. -/
theorem norm_finitePiLpOperatorScalarCommutator_tensorCutoff_sq_le
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    {d : ℕ} (P : CMP95SourceSmoothPartitionProfile)
    {M0 : ℝ} (hM0 : 0 < M0) (z : Fin d → ℝ)
    (coord : ι → Fin d → ℝ) (dist : ι → ι → ℕ)
    (hsymm : ∀ x y, dist x y = dist y x)
    {coordConstant : ℝ} (hcoordConstant : 0 ≤ coordConstant)
    (hcoord : ∀ target source,
      (∑ μ, ‖coord target μ - coord source μ‖) ≤
        coordConstant * (dist target source : ℝ))
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    {amplitude rate rowSum : ℝ} (hrowSum : 0 ≤ rowSum)
    (hA : FinitePiLpExponentialKernelBound A dist amplitude rate)
    (hsum : ∀ x, ∑ y,
      Real.exp (-((rate / 2) * (dist x y : ℝ))) ≤ rowSum) :
    ‖finitePiLpOperatorScalarCommutator A
        (fun x => (P.tensorCutoff M0 z (coord x)) ^ 2)‖ ≤
      ((4 * ((P.derivBound / M0) * coordConstant) * amplitude) / rate) *
        rowSum := by
  apply finitePiLpOpNorm_le_of_exponentialKernelBound _ dist hsymm hrowSum
    (hsum := hsum)
  exact finitePiLpOperatorScalarCommutator_tensorCutoff_sq_exponentialKernelBound
    P hM0 z coord dist hcoordConstant hcoord A hA

end
end YangMills.RG
