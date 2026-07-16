/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.KernelDecay
import YangMills.RG.PhysicalBondDistance
import YangMills.RG.PhysicalCoerciveCombesThomas

/-!
# Composition of exponentially localized physical kernels

This module proves the physical, block-valued counterpart of the scalar
exponential-kernel convolution theorem.  If two operators have kernel decay
at rate `κ`, their composition has decay at rate `κ - σ`; the only geometric
cost is the volume-uniform exponential sum

`sup_x ∑_z exp (-σ dist(x,z))`.

The proof decomposes an intermediate physical cochain by bonds, but never by
Lie-algebra coordinates.  Consequently there is no spurious factor
`Nc² - 1` and no ambient-volume factor.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

/-- Elementary geometric domination used to turn polynomial bond-ball growth
into a geometric shell bound. -/
theorem nat_succ_le_two_pow (k : ℕ) :
    k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- Explicit volume-uniform exponential summability for the physical bond
metric.  The deliberately coarse geometric shell constants

`C = 2^d d`, `r = 2^d`

come directly from the already-proved physical bond-ball estimate. -/
theorem physicalBondDist_exp_sum_le_geometric
    (x : PhysicalBond d N) {σ : ℝ}
    (hlt : ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ) < 1) :
    ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (physicalBondDist x z : ℝ))) ≤
      (((2 ^ d) * d : ℕ) : ℝ) *
        (1 - ((2 ^ d : ℕ) : ℝ) * Real.exp (-σ))⁻¹ := by
  have hshell : ∀ k,
      ((Finset.univ.filter
        (fun z : PhysicalBond d N => physicalBondDist x z = k)).card : ℝ) ≤
        (((2 ^ d) * d : ℕ) : ℝ) * (((2 ^ d : ℕ) : ℝ) ^ k) := by
    intro k
    have hshellBall :
        (Finset.univ.filter
          (fun z : PhysicalBond d N => physicalBondDist x z = k)).card ≤
          (Finset.univ.filter
            (fun z : PhysicalBond d N => physicalBondDist x z ≤ k)).card := by
      apply Finset.card_le_card
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.le⟩
    have hball := physicalBondDist_ball_card_le x k
    have hsucc : k + 1 ≤ 2 ^ k := nat_succ_le_two_pow k
    have hgeomNat :
        (2 * (k + 1)) ^ d * d ≤
          ((2 ^ d) * d) * (2 ^ d) ^ k := by
      calc
        (2 * (k + 1)) ^ d * d
            ≤ (2 * 2 ^ k) ^ d * d :=
          Nat.mul_le_mul_right d (Nat.pow_le_pow_left
            (Nat.mul_le_mul_left 2 hsucc) d)
        _ = ((2 ^ d) * d) * (2 ^ d) ^ k := by
          rw [mul_pow, ← pow_mul]
          ring
    exact_mod_cast hshellBall.trans (hball.trans hgeomNat)
  simpa only [neg_mul] using
    (lattice_exp_sum_le_geometric
      (ℓ := fun z : PhysicalBond d N => physicalBondDist x z)
      (σ := σ)
      (C := (((2 ^ d) * d : ℕ) : ℝ))
      (r := ((2 ^ d : ℕ) : ℝ))
      (by positivity) hshell hlt)

/-- Exponential kernel decay is stable under weakening the decay rate. -/
theorem physicalCovarianceExponentialKernelBound_mono_rate
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A κ κ' : ℝ}
    (hκ' : 0 < κ')
    (hκ : κ' ≤ κ)
    (C : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hC : PhysicalCovarianceExponentialKernelBound C dist A κ) :
    PhysicalCovarianceExponentialKernelBound C dist A κ' := by
  refine ⟨hC.1, hκ', ?_⟩
  intro source target v
  refine le_trans (hC.2.2 source target v) ?_
  have hdist : (0 : ℝ) ≤ (dist target source : ℝ) := by positivity
  have hexp :
      Real.exp (-(κ * (dist target source : ℝ))) ≤
        Real.exp (-(κ' * (dist target source : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp hC.1) (norm_nonneg v)

/-- Nonnegative scalar multiplication preserves the decay rate and scales the
kernel amplitude exactly. -/
theorem physicalCovarianceExponentialKernelBound_smul
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A κ r : ℝ}
    (hr : 0 ≤ r)
    (C : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hC : PhysicalCovarianceExponentialKernelBound C dist A κ) :
    PhysicalCovarianceExponentialKernelBound (r • C) dist (r * A) κ := by
  refine ⟨mul_nonneg hr hC.1, hC.2.1, ?_⟩
  intro source target v
  change
    ‖r • C
      (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) source v) target‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg hr]
  calc
    r * ‖C
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) source v) target‖
        ≤ r * (A * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hC.2.2 source target v) hr
    _ = (r * A) * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ := by
      ring

/-- Composition of two exponentially localized physical operators.

The intermediate cochain is decomposed only over physical bonds.  Each block
estimate acts on the full Lie-coordinate vector at that bond, so the
composition constant is `A * B * S`, with no internal-dimension loss. -/
theorem physicalCovarianceExponentialKernelBound_comp
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {A B κ σ S : ℝ}
    (hσ : 0 ≤ σ)
    (hσκ : σ < κ)
    (hS : 0 ≤ S)
    (Left Right : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hLeft : PhysicalCovarianceExponentialKernelBound Left dist A κ)
    (hRight : PhysicalCovarianceExponentialKernelBound Right dist B κ)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ S) :
    PhysicalCovarianceExponentialKernelBound
      (Left.comp Right) dist (A * B * S) (κ - σ) := by
  classical
  refine
    ⟨mul_nonneg (mul_nonneg hLeft.1 hRight.1) hS,
      sub_pos.mpr hσκ, ?_⟩
  intro source target v
  let δ :=
    singlePhysicalBondCochain
      (d := d) (N := N) (Nc := Nc) source v
  have hdecomp :
      Right δ =
        ∑ z : PhysicalBond d N,
          singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) z (Right δ z) :=
    (sum_singlePhysicalBondCochain_eq (Right δ)).symm
  have happ :
      (Left.comp Right) δ target =
        ∑ z : PhysicalBond d N,
          Left
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) z (Right δ z))
            target := by
    calc
      (Left.comp Right) δ target = Left (Right δ) target := rfl
      _ =
          Left
            (∑ z : PhysicalBond d N,
              singlePhysicalBondCochain
                (d := d) (N := N) (Nc := Nc) z (Right δ z))
            target :=
        congrArg (fun w => Left w target) hdecomp
      _ = ∑ z : PhysicalBond d N,
          Left
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) z (Right δ z))
            target := by
        rw [map_sum, physicalCochain_sum_apply]
  let E := Real.exp (-((κ - σ) * (dist target source : ℝ)))
  have hterm : ∀ z : PhysicalBond d N,
      ‖Left
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) z (Right δ z))
          target‖ ≤
        (A * B * E) *
          Real.exp (-(σ * (dist target z : ℝ))) * ‖v‖ := by
    intro z
    have hL := hLeft.2.2 z target (Right δ z)
    have hR := hRight.2.2 source z v
    have hcoeff :
        A * Real.exp (-(κ * (dist target z : ℝ))) *
            (B * Real.exp (-(κ * (dist z source : ℝ)))) ≤
          (A * B * E) *
            Real.exp (-(σ * (dist target z : ℝ))) := by
      have hκσ : 0 ≤ κ - σ := (sub_pos.mpr hσκ).le
      have hdist_zs : (0 : ℝ) ≤ (dist z source : ℝ) := by positivity
      have htriangle :
          (dist target source : ℝ) ≤
            (dist target z : ℝ) + (dist z source : ℝ) := by
        exact_mod_cast htri target source z
      have hexp :
          Real.exp (-(κ * (dist target z : ℝ))) *
              Real.exp (-(κ * (dist z source : ℝ))) ≤
            E * Real.exp (-(σ * (dist target z : ℝ))) := by
        dsimp [E]
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [
          mul_le_mul_of_nonneg_left htriangle hκσ,
          mul_nonneg hσ hdist_zs]
      calc
        A * Real.exp (-(κ * (dist target z : ℝ))) *
              (B * Real.exp (-(κ * (dist z source : ℝ))))
            =
          (A * B) *
            (Real.exp (-(κ * (dist target z : ℝ))) *
              Real.exp (-(κ * (dist z source : ℝ)))) := by ring
        _ ≤ (A * B) *
            (E * Real.exp (-(σ * (dist target z : ℝ)))) :=
          mul_le_mul_of_nonneg_left hexp
            (mul_nonneg hLeft.1 hRight.1)
        _ = (A * B * E) *
            Real.exp (-(σ * (dist target z : ℝ))) := by ring
    calc
      ‖Left
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) z (Right δ z))
          target‖
          ≤
        A * Real.exp (-(κ * (dist target z : ℝ))) * ‖Right δ z‖ := hL
      _ ≤
        A * Real.exp (-(κ * (dist target z : ℝ))) *
          (B * Real.exp (-(κ * (dist z source : ℝ))) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hR
          (mul_nonneg hLeft.1 (Real.exp_pos _).le)
      _ =
        (A * Real.exp (-(κ * (dist target z : ℝ))) *
          (B * Real.exp (-(κ * (dist z source : ℝ))))) * ‖v‖ := by ring
      _ ≤
        ((A * B * E) *
          Real.exp (-(σ * (dist target z : ℝ)))) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hcoeff (norm_nonneg v)
      _ =
        (A * B * E) *
          Real.exp (-(σ * (dist target z : ℝ))) * ‖v‖ := by ring
  calc
    ‖(Left.comp Right) δ target‖
        = ‖∑ z : PhysicalBond d N,
            Left
              (singlePhysicalBondCochain
                (d := d) (N := N) (Nc := Nc) z (Right δ z))
              target‖ := by rw [happ]
    _ ≤ ∑ z : PhysicalBond d N,
          ‖Left
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) z (Right δ z))
            target‖ := norm_sum_le _ _
    _ ≤ ∑ z : PhysicalBond d N,
          (A * B * E) *
            Real.exp (-(σ * (dist target z : ℝ))) * ‖v‖ :=
      Finset.sum_le_sum fun z _ => hterm z
    _ =
        (A * B * E * ‖v‖) *
          ∑ z : PhysicalBond d N,
            Real.exp (-(σ * (dist target z : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ (A * B * E * ‖v‖) * S :=
      mul_le_mul_of_nonneg_left (hsum target)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hLeft.1 hRight.1) (Real.exp_pos _).le)
          (norm_nonneg v))
    _ = (A * B * S) *
        Real.exp (-((κ - σ) * (dist target source : ℝ))) * ‖v‖ := by
      dsimp [E]
      ring

/-- Three-factor physical kernel composition.  Two intermediate bond sums
cost two copies of the geometric constant and reduce the rate from `κ` to
`κ - 2σ`. -/
theorem physicalCovarianceExponentialKernelBound_comp_three
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {A B C κ σ S : ℝ}
    (hσ : 0 ≤ σ)
    (h2σκ : 2 * σ < κ)
    (hS : 0 ≤ S)
    (Left Middle Right : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hLeft : PhysicalCovarianceExponentialKernelBound Left dist A κ)
    (hMiddle : PhysicalCovarianceExponentialKernelBound Middle dist B κ)
    (hRight : PhysicalCovarianceExponentialKernelBound Right dist C κ)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ S) :
    PhysicalCovarianceExponentialKernelBound
      (Left.comp (Middle.comp Right)) dist
      (A * (B * C * S) * S) ((κ - σ) - σ) := by
  have hσκ : σ < κ := by linarith
  have hσ_remain : σ < κ - σ := by linarith
  have hLeftWeak :
      PhysicalCovarianceExponentialKernelBound Left dist A (κ - σ) :=
    physicalCovarianceExponentialKernelBound_mono_rate
      dist (sub_pos.mpr hσκ) (by linarith) Left hLeft
  have hMiddleRight :
      PhysicalCovarianceExponentialKernelBound
        (Middle.comp Right) dist (B * C * S) (κ - σ) :=
    physicalCovarianceExponentialKernelBound_comp
      dist htri hσ hσκ hS Middle Right hMiddle hRight hsum
  exact physicalCovarianceExponentialKernelBound_comp
    dist htri hσ hσ_remain hS
    Left (Middle.comp Right) hLeftWeak hMiddleRight hsum

end

end YangMills.RG
