/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SectionCCovarianceDifferenceSupport
import YangMills.RG.PhysicalExponentialKernelComposition

/-!
# Bilateral decay through an exactly supported shell insertion

If `Delta = P_T Delta P_T`, the kernel of `Left * Delta * Right` is a finite
double sum over `T`.  At the full exterior decay rate, the sharp
volume-independent datum on the middle insertion is its double kernel mass on
`T`; a row supremum alone controls only one of the two shell sums.

The theorem below keeps the lower distances to `T` explicit.  This handles an
empty shell without manufacturing a value for `dist(x, empty)` and lets later
CMP99 geometry provide the precise collar gap.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Projection onto `T` is the finite sum of the single-bond components in
`T`. -/
theorem physicalBondProjection_eq_sum_single
    {d N Nc : ℕ} [NeZero N]
    (T : Finset (PhysicalBond d N))
    (x : PhysicalGaugeOneCochain d N Nc) :
    physicalBondProjection T x =
      ∑ source ∈ T, singlePhysicalBondCochain source (x source) := by
  apply PiLp.ext
  intro target
  rw [physicalCochain_sum_apply]
  by_cases htarget : target ∈ T
  · rw [physicalBondProjection_apply_mem T htarget]
    rw [Finset.sum_eq_single target]
    · simp
    · intro source hsource hne
      exact singlePhysicalBondCochain_of_ne (x source) hne.symm
    · exact fun h => (h htarget).elim
  · rw [physicalBondProjection_apply_not_mem T htarget]
    symm
    apply Finset.sum_eq_zero
    intro source hsource
    exact singlePhysicalBondCochain_of_ne (x source)
      (fun h => htarget (h ▸ hsource))

/-- Full-rate bilateral shell estimate.  `M source target` is a genuine
pointwise kernel majorant for the middle insertion and `B` bounds its double
mass on the exact support `T`; neither a raw shell cardinal nor the ambient
volume occurs in the conclusion. -/
theorem physicalExponentialKernel_comp_supported_comp_le
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (Left Delta Right : PhysicalEndomorphism d N Nc)
    (T : Finset (PhysicalBond d N))
    (M : PhysicalBond d N → PhysicalBond d N → ℝ)
    {A0 A1 mu B : ℝ}
    (hLeft : PhysicalCovarianceExponentialKernelBound Left dist A0 mu)
    (hRight : PhysicalCovarianceExponentialKernelBound Right dist A1 mu)
    (hDelta : PhysicalCovarianceKernelBound Delta M)
    (hM : ∀ source target, 0 ≤ M source target)
    (hB : ∑ target ∈ T, ∑ source ∈ T, M target source ≤ B)
    {source target : PhysicalBond d N} {dx dy : ℕ}
    (hx : ∀ u, u ∈ T → dx ≤ dist target u)
    (hy : ∀ v, v ∈ T → dy ≤ dist v source)
    (v0 : SUNLieCoord Nc) :
    ‖(Left.comp ((physicalBondProjection T).comp
        (Delta.comp ((physicalBondProjection T).comp Right))))
          (singlePhysicalBondCochain source v0) target‖ ≤
      A0 * A1 * B *
        Real.exp (-(mu * (dx : ℝ))) *
        Real.exp (-(mu * (dy : ℝ))) * ‖v0‖ := by
  let delta := singlePhysicalBondCochain
    (d := d) (N := N) (Nc := Nc) source v0
  let y := physicalBondProjection T (Right delta)
  let z := physicalBondProjection T (Delta y)
  have hydecomp :
      y = ∑ w ∈ T, singlePhysicalBondCochain w (Right delta w) := by
    dsimp [y]
    exact physicalBondProjection_eq_sum_single T (Right delta)
  have hzdecomp :
      z = ∑ u ∈ T, singlePhysicalBondCochain u (Delta y u) := by
    dsimp [z]
    exact physicalBondProjection_eq_sum_single T (Delta y)
  have hDapply : ∀ u,
      Delta y u =
        ∑ w ∈ T, Delta (singlePhysicalBondCochain w (Right delta w)) u := by
    intro u
    rw [hydecomp, map_sum, physicalCochain_sum_apply]
  have happ :
      (Left.comp ((physicalBondProjection T).comp
        (Delta.comp ((physicalBondProjection T).comp Right)))) delta target =
      ∑ u ∈ T, ∑ w ∈ T,
        Left (singlePhysicalBondCochain u
          (Delta (singlePhysicalBondCochain w (Right delta w)) u)) target := by
    change Left z target = _
    rw [hzdecomp, map_sum, physicalCochain_sum_apply]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hDapply u]
    have hsingleSum :
        singlePhysicalBondCochain u
            (∑ w ∈ T,
              Delta (singlePhysicalBondCochain w (Right delta w)) u) =
          ∑ w ∈ T, singlePhysicalBondCochain u
            (Delta (singlePhysicalBondCochain w (Right delta w)) u) := by
      apply PiLp.ext
      intro q
      by_cases hq : q = u
      · subst q
        simp
      · simp [singlePhysicalBondCochain_of_ne, hq]
    rw [hsingleSum, map_sum, physicalCochain_sum_apply]
  have hexpX : ∀ u, u ∈ T →
      Real.exp (-(mu * (dist target u : ℝ))) ≤
        Real.exp (-(mu * (dx : ℝ))) := by
    intro u hu
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (hx u hu)) (le_of_lt hLeft.2.1)
  have hexpY : ∀ w, w ∈ T →
      Real.exp (-(mu * (dist w source : ℝ))) ≤
        Real.exp (-(mu * (dy : ℝ))) := by
    intro w hw
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (hy w hw)) (le_of_lt hRight.2.1)
  let C := A0 * A1 * Real.exp (-(mu * (dx : ℝ))) *
    Real.exp (-(mu * (dy : ℝ)))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hLeft.1 hRight.1)
        (le_of_lt (Real.exp_pos _)))
      (le_of_lt (Real.exp_pos _))
  have hterm : ∀ u ∈ T, ∀ w ∈ T,
      ‖Left (singlePhysicalBondCochain u
          (Delta (singlePhysicalBondCochain w (Right delta w)) u)) target‖ ≤
        C * M u w * ‖v0‖ := by
    intro u hu w hw
    have hL := hLeft.2.2 u target
      (Delta (singlePhysicalBondCochain w (Right delta w)) u)
    have hD := hDelta w u (Right delta w)
    have hR := hRight.2.2 source w v0
    calc
      ‖Left (singlePhysicalBondCochain u
          (Delta (singlePhysicalBondCochain w (Right delta w)) u)) target‖
          ≤ A0 * Real.exp (-(mu * (dist target u : ℝ))) *
              ‖Delta (singlePhysicalBondCochain w (Right delta w)) u‖ := hL
      _ ≤ A0 * Real.exp (-(mu * (dist target u : ℝ))) *
              (M u w * ‖Right delta w‖) := by
            exact mul_le_mul_of_nonneg_left hD
              (mul_nonneg hLeft.1 (le_of_lt (Real.exp_pos _)))
      _ ≤ A0 * Real.exp (-(mu * (dist target u : ℝ))) *
              (M u w *
                (A1 * Real.exp (-(mu * (dist w source : ℝ))) * ‖v0‖)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hR (hM u w))
              (mul_nonneg hLeft.1 (le_of_lt (Real.exp_pos _)))
      _ ≤ C * M u w * ‖v0‖ := by
            dsimp [C]
            have hx' := hexpX u hu
            have hy' := hexpY w hw
            have hM' := hM u w
            have hA0 := hLeft.1
            have hA1 := hRight.1
            have hxcoef :
                A0 * Real.exp (-(mu * (dist target u : ℝ))) ≤
                  A0 * Real.exp (-(mu * (dx : ℝ))) :=
              mul_le_mul_of_nonneg_left hx' hA0
            have hycoef :
                A1 * Real.exp (-(mu * (dist w source : ℝ))) * ‖v0‖ ≤
                  A1 * Real.exp (-(mu * (dy : ℝ))) * ‖v0‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hy' hA1) (norm_nonneg v0)
            have hinner := mul_le_mul_of_nonneg_left hycoef hM'
            calc
              A0 * Real.exp (-(mu * (dist target u : ℝ))) *
                  (M u w *
                    (A1 * Real.exp (-(mu * (dist w source : ℝ))) * ‖v0‖))
                  ≤ A0 * Real.exp (-(mu * (dx : ℝ))) *
                    (M u w *
                      (A1 * Real.exp (-(mu * (dy : ℝ))) * ‖v0‖)) :=
                mul_le_mul hxcoef hinner
                  (mul_nonneg hM'
                    (mul_nonneg (mul_nonneg hA1 (le_of_lt (Real.exp_pos _)))
                      (norm_nonneg v0)))
                  (mul_nonneg hA0 (le_of_lt (Real.exp_pos _)))
              _ = A0 * A1 * Real.exp (-(mu * (dx : ℝ))) *
                    Real.exp (-(mu * (dy : ℝ))) * M u w * ‖v0‖ := by ring
  rw [happ]
  calc
    ‖∑ u ∈ T, ∑ w ∈ T,
        Left (singlePhysicalBondCochain u
          (Delta (singlePhysicalBondCochain w (Right delta w)) u)) target‖
        ≤ ∑ u ∈ T, ∑ w ∈ T,
            ‖Left (singlePhysicalBondCochain u
              (Delta (singlePhysicalBondCochain w (Right delta w)) u)) target‖ := by
          exact (norm_sum_le _ _).trans <|
            Finset.sum_le_sum fun u _ => norm_sum_le _ _
    _ ≤ ∑ u ∈ T, ∑ w ∈ T, C * M u w * ‖v0‖ := by
          exact Finset.sum_le_sum fun u hu =>
            Finset.sum_le_sum fun w hw => hterm u hu w hw
    _ = C * (∑ u ∈ T, ∑ w ∈ T, M u w) * ‖v0‖ := by
          simp_rw [← Finset.sum_mul]
          simp_rw [← Finset.mul_sum]
    _ ≤ C * B * ‖v0‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hB hC) (norm_nonneg v0)
    _ = A0 * A1 * B * Real.exp (-(mu * (dx : ℝ))) *
          Real.exp (-(mu * (dy : ℝ))) * ‖v0‖ := by
          dsimp [C]
          ring

/-- Bilateral collar decay for the literal CMP99 covariance-difference
species.  The only new quantitative datum is the explicit double kernel mass
of the already constructed precision difference on its exact shell support. -/
theorem cmp99SectionCCovarianceDifference_bilateralShellDecay
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {S1 S0 : Finset (PhysicalBond d N)} (hsub : S1 ⊆ S0)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    (R : ℕ) (hrange : PhysicalCovarianceFiniteRange K dist R)
    {c mass A0 A1 mu B : ℝ}
    (hc : 0 < c) (hmass : 0 < mass) (hK : IsCoerciveCLM K c)
    (hC0 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K S0 hc hmass hK) dist A0 mu)
    (hC1 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K S1 hc hmass hK) dist A1 mu)
    (M : PhysicalBond d N → PhysicalBond d N → ℝ)
    (hDelta : PhysicalCovarianceKernelBound
      (cmp99LocalizedPhysicalPrecision K S1 mass -
        cmp99LocalizedPhysicalPrecision K S0 mass) M)
    (hM : ∀ source target, 0 ≤ M source target)
    (hB : let T := cmp99PhysicalBondThickening dist R (S0 \ S1)
      ∑ target ∈ T, ∑ source ∈ T, M target source ≤ B)
    {source target : PhysicalBond d N} {dx dy : ℕ}
    (hx : let T := cmp99PhysicalBondThickening dist R (S0 \ S1)
      ∀ u, u ∈ T → dx ≤ dist target u)
    (hy : let T := cmp99PhysicalBondThickening dist R (S0 \ S1)
      ∀ v, v ∈ T → dy ≤ dist v source)
    (v0 : SUNLieCoord Nc) :
    ‖cmp99SectionCCovarianceDifference K S0 S1 hc hmass hK
        (singlePhysicalBondCochain source v0) target‖ ≤
      A0 * A1 * B * Real.exp (-(mu * (dx : ℝ))) *
        Real.exp (-(mu * (dy : ℝ))) * ‖v0‖ := by
  let T := cmp99PhysicalBondThickening dist R (S0 \ S1)
  rw [cmp99SectionCCovarianceDifference_eq_thickening_resolventProduct
    K hsub dist hsymm hself R hrange hc hmass hK]
  exact physicalExponentialKernel_comp_supported_comp_le
    dist
    (cmp99LocalizedPhysicalCovariance K S0 hc hmass hK)
    (cmp99LocalizedPhysicalPrecision K S1 mass -
      cmp99LocalizedPhysicalPrecision K S0 mass)
    (cmp99LocalizedPhysicalCovariance K S1 hc hmass hK)
    T M hC0 hC1 hDelta hM hB hx hy v0

end

end YangMills.RG
