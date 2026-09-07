/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.KernelDecay
import YangMills.RG.PhysicalBondDistance
import YangMills.RG.PhysicalCoerciveCombesThomas
import YangMills.RG.PhysicalGaugeCMP116OperatorTransport
import YangMills.RG.PhysicalGramKernel

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

/-- Negation preserves exponential localization. -/
theorem physicalCovarianceExponentialKernelBound_neg
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A κ : ℝ}
    (C : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hC : PhysicalCovarianceExponentialKernelBound C dist A κ) :
    PhysicalCovarianceExponentialKernelBound (-C) dist A κ := by
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro source target v
  change ‖-C
    (singlePhysicalBondCochain
      (d := d) (N := N) (Nc := Nc) source v) target‖ ≤ _
  rw [norm_neg]
  exact hC.2.2 source target v

/-- Addition preserves the decay rate and adds amplitudes. -/
theorem physicalCovarianceExponentialKernelBound_add
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A B κ : ℝ}
    (Left Right : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hLeft : PhysicalCovarianceExponentialKernelBound Left dist A κ)
    (hRight : PhysicalCovarianceExponentialKernelBound Right dist B κ) :
    PhysicalCovarianceExponentialKernelBound
      (Left + Right) dist (A + B) κ := by
  refine ⟨add_nonneg hLeft.1 hRight.1, hLeft.2.1, ?_⟩
  intro source target v
  change
    ‖Left
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) source v) target +
      Right
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) source v) target‖ ≤ _
  calc
    _ ≤
        ‖Left
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v) target‖ +
        ‖Right
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v) target‖ :=
      norm_add_le _ _
    _ ≤
        A * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ +
        B * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ :=
      add_le_add
        (hLeft.2.2 source target v)
        (hRight.2.2 source target v)
    _ = (A + B) *
        Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ := by ring

/-- A finite-range physical block kernel is exponentially localized at every
positive rate, with the standard support cost `exp(κR)`. -/
theorem physicalCovarianceExponentialKernelBound_of_finiteRange
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {M κ : ℝ} {R : ℕ}
    (hM : 0 ≤ M) (hκ : 0 < κ)
    (C : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hrange : PhysicalCovarianceFiniteRange C dist R)
    (hbound : PhysicalCovarianceKernelBound C (fun _ _ => M)) :
    PhysicalCovarianceExponentialKernelBound
      C dist (M * Real.exp (κ * (R : ℝ))) κ := by
  refine
    ⟨mul_nonneg hM (Real.exp_pos _).le, hκ, ?_⟩
  intro source target v
  by_cases hfar : R < dist target source
  · rw [hrange source target v hfar, norm_zero]
    positivity
  · have hnear : (dist target source : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast le_of_not_gt hfar
    have hexp :
        1 ≤ Real.exp (κ * (R : ℝ)) *
          Real.exp (-(κ * (dist target source : ℝ))) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      ‖C
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v) target‖
          ≤ M * ‖v‖ := hbound source target v
      _ = (M * ‖v‖) * 1 := by ring
      _ ≤ (M * ‖v‖) *
          (Real.exp (κ * (R : ℝ)) *
            Real.exp (-(κ * (dist target source : ℝ)))) :=
        mul_le_mul_of_nonneg_left hexp
          (mul_nonneg hM (norm_nonneg v))
      _ = (M * Real.exp (κ * (R : ℝ))) *
          Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ := by ring

/-- The adjoint of an exponentially localized physical block operator has
the same bound when the distance is symmetric. -/
theorem physicalCovarianceExponentialKernelBound_adjoint
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    {A κ : ℝ}
    (C : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hC : PhysicalCovarianceExponentialKernelBound C dist A κ) :
    PhysicalCovarianceExponentialKernelBound C.adjoint dist A κ := by
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro source target v
  let y :=
    C.adjoint
      (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) source v) target
  have hinner :
      inner ℝ y y =
        inner ℝ v
          (C
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) target y) source) := by
    calc
      inner ℝ y y =
          inner ℝ
            (C.adjoint
              (singlePhysicalBondCochain
                (d := d) (N := N) (Nc := Nc) source v))
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) target y) := by
        rw [inner_singlePhysicalBondCochain_right]
      _ =
          inner ℝ
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) source v)
            (C
              (singlePhysicalBondCochain
                (d := d) (N := N) (Nc := Nc) target y)) := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ =
          inner ℝ v
            (C
              (singlePhysicalBondCochain
                (d := d) (N := N) (Nc := Nc) target y) source) := by
        rw [real_inner_comm,
          inner_singlePhysicalBondCochain_right,
          real_inner_comm]
  have hblock := hC.2.2 target source y
  rw [hsymm source target] at hblock
  let coeff :=
    A * Real.exp (-(κ * (dist target source : ℝ)))
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    exact mul_nonneg hC.1 (Real.exp_pos _).le
  have hsq :
      ‖y‖ ^ 2 ≤ (coeff * ‖v‖) * ‖y‖ := by
    calc
      ‖y‖ ^ 2 = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ =
          inner ℝ v
            (C
              (singlePhysicalBondCochain
                (d := d) (N := N) (Nc := Nc) target y) source) :=
        hinner
      _ ≤ ‖v‖ *
          ‖C
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) target y) source‖ :=
        real_inner_le_norm _ _
      _ ≤ ‖v‖ * (coeff * ‖y‖) :=
        mul_le_mul_of_nonneg_left hblock (norm_nonneg v)
      _ = (coeff * ‖v‖) * ‖y‖ := by ring
  rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hy0
  · rw [← hy0]
    exact mul_nonneg hcoeff (norm_nonneg v)
  · have hcancel :
        ‖y‖ * ‖y‖ ≤ (coeff * ‖v‖) * ‖y‖ := by
      simpa [pow_two] using hsq
    exact le_of_mul_le_mul_right hcancel hy0

/-- A coordinate projection is ultralocal, hence exponentially localized at
every positive rate with unit amplitude. -/
theorem physicalBondProjection_exponentialKernelBound
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hself : ∀ p, dist p p = 0)
    (S : Finset (PhysicalBond d N))
    {κ : ℝ} (hκ : 0 < κ) :
    PhysicalCovarianceExponentialKernelBound
      (physicalBondProjection S :
        PhysicalGaugeOneCochain d N Nc →L[ℝ]
          PhysicalGaugeOneCochain d N Nc)
      dist 1 κ := by
  refine ⟨zero_le_one, hκ, ?_⟩
  intro source target v
  by_cases hts : target = source
  · subst target
    rw [hself source]
    by_cases hs : source ∈ S
    · rw [physicalBondProjection_apply_mem S hs,
        singlePhysicalBondCochain_self]
      simp
    · rw [physicalBondProjection_apply_not_mem S hs]
      simp
  · have hzero :
        physicalBondProjection S
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) source v) target = 0 := by
      by_cases ht : target ∈ S
      · rw [physicalBondProjection_apply_mem S ht,
          singlePhysicalBondCochain_of_ne v hts]
      · exact physicalBondProjection_apply_not_mem S ht _
    rw [hzero, norm_zero]
    positivity

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
