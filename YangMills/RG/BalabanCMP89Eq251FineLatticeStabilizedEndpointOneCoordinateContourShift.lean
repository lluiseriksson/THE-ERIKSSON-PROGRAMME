/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251FineLatticeStabilizedEndpointBoundarySeam
import YangMills.RG.BalabanCMP89Eq251OneCoordinateContourShift
import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointHolomorphy

/-!
# Cold-sealed one-coordinate shift for a fine-lattice endpoint

Compiler-verified at exact source checkpoint
`290d546550a55511d7677ce67066ca403afdc393` by cold GitHub Actions run
`31339761858`. Restoration and saving of `.lake/build` were skipped. The focal
and audit exited zero; the audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`.

This module specializes the rectangular Cauchy route to the literal endpoint
displacement `u/(L^j)` at `alpha = 0`.  Holomorphy is constructed from the
sealed common-radius producer and the vertical-face equality is the sealed
full-polydisc fine-lattice seam.  Coordinates other than the active one may
already lie on signed imaginary faces.

This proves one coordinate integral equality only.  Product integrability,
iteration over all four coordinates, normalized integration, physical `B0`,
window-15 attainment and terminal fields remain open.
-/

namespace YangMills.RG

noncomputable section

/-- Shift one physical Brillouin coordinate of a stabilized endpoint with
fine-lattice displacement `u/(L^j)` through the common analytic strip. -/
theorem intervalIntegral_cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_physicalFine_coordinateShift
    {L j : ℕ} [NeZero L] {mass a rho eta : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (heta : |eta| ≤ rho)
    (nu mu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho) (hnuImag : (z nu).im = 0)
    (holderDisplacement : Fin 4 → ℝ) (endpointU : Fin 4 → ℤ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
        (cmp89Eq251PhysicalCoordinateLine nu z (x : ℂ)) mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)) =
      ∫ x : ℝ in 0..2 * Real.pi,
        cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
          (cmp89Eq251PhysicalCoordinateLine nu z
            ((x : ℂ) + eta * Complex.I)) mu
          holderDisplacement
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
  let endpointDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (((L ^ j : ℕ) : ℝ)⁻¹) endpointU
  let f : ℂ → ℂ := fun w =>
    cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
      (cmp89Eq251PhysicalCoordinateLine nu z w) mu holderDisplacement
      endpointDisplacement
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
      cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_physicalFine_boundarySeam
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hmassPos hrho hamplitude hradius hwindow hmass nu mu hp hface
          hrealY (himag_of_mem y hy) holderDisplacement endpointU
    unfold f
    convert hseam using 1
    exact congrArg
      (fun q : Fin 4 → ℂ =>
        cmp89Eq251ComplexStabilizedEndpointIntegrand
          4 L j mass a 0 q mu holderDisplacement endpointDisplacement)
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
          cmp89Eq251ComplexStabilizedEndpointIntegrand
            4 L j mass a 0 q mu holderDisplacement endpointDisplacement)
        (cmp89Eq251PhysicalCoordinateLine nu z w) :=
      differentiableAt_cmp89Eq251ComplexStabilizedEndpointIntegrand_of_commonRadius
        ha hmassPos hrho hamplitude hradius hwindow hmass hpw
          (fun _ => rfl) himagW
    have hinner : DifferentiableAt ℂ
        (cmp89Eq251PhysicalCoordinateLine nu z) w := by
      simpa [cmp89Eq251PhysicalCoordinateLine] using
        ((hasFDerivAt_single (𝕜 := ℂ) (i := nu) w).const_add z).differentiableAt
    simpa [f] using (houter.comp w hinner).differentiableWithinAt
  exact intervalIntegral_eq_verticalShift_of_boundary_eq_of_differentiableOn
    f (2 * Real.pi) eta hboundary hdiff

end

end YangMills.RG
