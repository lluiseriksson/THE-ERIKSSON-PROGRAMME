/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

One-coordinate Cauchy shift for the literal mass-uniform fine-lattice left
derivative.  Holomorphy and the vertical seam are constructed from D1; no
slice equality is accepted from the caller. -/

import YangMills.RG.HolomorphicVerticalShiftBoundary
import YangMills.RG.BalabanCMP89Eq251OneCoordinateContourShift
import YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformHolomorphy

namespace YangMills.RG

noncomputable section

/-- Shift one physical Brillouin coordinate of the literal stabilized
fine-lattice left-derivative integrand through the common analytic strip. -/
theorem intervalIntegral_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_coordinateShift_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho eta : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (heta : |eta| ≤ rho)
    (nu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho) (hnuImag : (z nu).im = 0)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a (cmp89Eq251PhysicalCoordinateLine nu z (x : ℂ))
        mu endpointU) =
      ∫ x : ℝ in 0..2 * Real.pi,
        cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
          L j mass a
          (cmp89Eq251PhysicalCoordinateLine nu z
            ((x : ℂ) + eta * Complex.I))
          mu endpointU := by
  let f : ℂ → ℂ := fun w =>
    cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
      L j mass a (cmp89Eq251PhysicalCoordinateLine nu z w) mu endpointU
  have himag_of_mem (y : ℝ) (hy : y ∈ Set.uIcc (0 : ℝ) eta) :
      ∀ k, |(cmp89Eq251PhysicalCoordinateLine nu z
        (y * Complex.I) k).im| ≤ rho := by
    intro k
    by_cases hk : k = nu
    · subst k
      have hyAbs : |y| ≤ |eta| := by
        simpa using Set.abs_sub_left_of_mem_uIcc hy
      simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
        hnuImag] using hyAbs.trans heta
    · simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk]
        using himag k
  have hboundary : ∀ y ∈ Set.uIcc (0 : ℝ) eta,
      f (((2 * Real.pi : ℝ) : ℂ) + y * Complex.I) =
        f (y * Complex.I) := by
    intro y hy
    have hrealY : ∀ k,
        (cmp89Eq251PhysicalCoordinateLine nu z
          (y * Complex.I) k).re = p k := by
      intro k
      by_cases hk : k = nu
      · subst k
        simp [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
          hreal nu]
      · simp [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk,
          hreal k]
    have hseam :=
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_boundarySeam_massUniform_draft
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass nu hp hface hrealY
          (himag_of_mem y hy) mu endpointU
    unfold f
    convert hseam using 1
    exact congrArg
      (fun q : Fin 4 → ℂ =>
        cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
          L j mass a q mu endpointU)
      (cmp89Eq251PhysicalCoordinateLine_two_pi_add nu z
        (y * Complex.I))
  have hdiff : DifferentiableOn ℂ f
      (Set.uIcc 0 (2 * Real.pi) ×ℂ Set.uIcc 0 eta) := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    have hx : 0 ≤ w.re ∧ w.re ≤ 2 * Real.pi := by
      have hx' := hw.1
      rw [Set.uIcc_of_le
        (mul_nonneg (by norm_num) Real.pi_pos.le)] at hx'
      exact hx'
    have hyAbs : |w.im| ≤ |eta| := by
      simpa using Set.abs_sub_left_of_mem_uIcc hw.2
    let pw : Fin 4 → ℝ := fun k =>
      (cmp89Eq251PhysicalCoordinateLine nu z w k).re
    have hpw : ∀ k, |pw k| ≤ Real.pi := by
      intro k
      by_cases hk : k = nu
      · subst k
        have hbounds : -Real.pi ≤ -Real.pi + w.re ∧
            -Real.pi + w.re ≤ Real.pi := by
          constructor <;> linarith [Real.pi_pos]
        rw [abs_le]
        simpa [pw, cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
          hreal nu, hface] using hbounds
      · simpa [pw, cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk,
          hreal k] using hp k
    have himagW : ∀ k,
        |(cmp89Eq251PhysicalCoordinateLine nu z w k).im| ≤ rho := by
      intro k
      by_cases hk : k = nu
      · subst k
        simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
          hnuImag] using hyAbs.trans heta
      · simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk]
          using himag k
    have houter : DifferentiableAt ℂ
        (fun q : Fin 4 → ℂ =>
          cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
            L j mass a q mu endpointU)
        (cmp89Eq251PhysicalCoordinateLine nu z w) :=
      differentiableAt_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_massUniform_draft
        ha hrho hamplitude hradius hwindow hmass hpw (fun _ => rfl) himagW
          mu endpointU
    have hinner : DifferentiableAt ℂ
        (cmp89Eq251PhysicalCoordinateLine nu z) w := by
      simpa [cmp89Eq251PhysicalCoordinateLine] using
        ((hasFDerivAt_single (𝕜 := ℂ) (i := nu) w).const_add z).differentiableAt
    simpa [f] using (houter.comp w hinner).differentiableWithinAt
  exact intervalIntegral_eq_verticalShift_of_boundary_eq_of_differentiableOn
    f (2 * Real.pi) eta hboundary hdiff

end

end YangMills.RG
