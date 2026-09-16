/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

One-coordinate physical contour shift for the complete Holder integrand under
the mass-uniform common window.  It uses H3a holomorphy and the H3a boundary
seam and therefore retains no positive-mass premise.  This is one coordinate
only; no product telescope, bound, owner dictionary, regional B0, window-15
claim or terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP89Eq251OneCoordinateContourShift
import YangMills.RG.BalabanCMP89Eq251CompleteHolderMassUniformHolomorphy

namespace YangMills.RG

noncomputable section

/-- Shift one physical Brillouin coordinate through the mass-uniform common
strip.  Previously shifted coordinates may already lie on their signed
vertical faces. -/
theorem
    intervalIntegral_cmp89Eq251ComplexStabilizedIntegrand_coordinateShift_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a alpha rho eta : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (heta : |eta| ≤ rho)
    (nu mu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho) (hnuImag : (z nu).im = 0)
    (holderU transportU : Fin 4 → ℤ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (cmp89Eq251PhysicalCoordinateLine nu z (x : ℂ)) mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU)) =
      ∫ x : ℝ in 0..2 * Real.pi,
        cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
          (cmp89Eq251PhysicalCoordinateLine nu z
            ((x : ℂ) + eta * Complex.I)) mu
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) transportU) := by
  let f : ℂ → ℂ := fun w =>
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
      (cmp89Eq251PhysicalCoordinateLine nu z w) mu
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (((L ^ j : ℕ) : ℝ)⁻¹) transportU)
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
      cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolder_boundarySeam_massUniform_draft
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
        (rho := rho) ha hrho hamplitude hradius hwindow hmass nu mu hp hface
        hrealY (himag_of_mem y hy) holderU transportU
    unfold f
    convert hseam using 1
    exact congrArg
      (fun q : Fin 4 → ℂ =>
        cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha q mu
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) transportU))
      (cmp89Eq251PhysicalCoordinateLine_two_pi_add nu z
        (y * Complex.I))
  have hdiff : DifferentiableOn ℂ f
      (Set.uIcc 0 (2 * Real.pi) ×ℂ Set.uIcc 0 eta) := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    have hx : 0 ≤ w.re ∧ w.re ≤ 2 * Real.pi := by
      have hx' := hw.1
      rw [Set.uIcc_of_le (mul_nonneg (by norm_num) Real.pi_pos.le)] at hx'
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
          cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha q mu
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((L ^ j : ℕ) : ℝ)⁻¹) transportU))
        (cmp89Eq251PhysicalCoordinateLine nu z w) :=
      differentiableAt_cmp89Eq251ComplexStabilizedIntegrand_of_commonRadius_massUniform_draft
        ha hrho hamplitude hradius hwindow hmass hpw
          (fun _ => rfl) himagW
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) transportU)
    have hinner : DifferentiableAt ℂ
        (cmp89Eq251PhysicalCoordinateLine nu z) w := by
      simpa [cmp89Eq251PhysicalCoordinateLine] using
        ((hasFDerivAt_single (𝕜 := ℂ) (i := nu) w).const_add z).differentiableAt
    simpa [f] using (houter.comp w hinner).differentiableWithinAt
  exact intervalIntegral_eq_verticalShift_of_boundary_eq_of_differentiableOn
    f (2 * Real.pi) eta hboundary hdiff

end

end YangMills.RG
