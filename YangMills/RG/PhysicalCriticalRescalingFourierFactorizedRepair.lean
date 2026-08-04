/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCriticalRescalingFourierPostconditionedNoGo

/-!
# Factor-through-kernel no-go and an exact repair budget

The obstruction is not tied to a linear postconditioner.  Any scalar penalty
which factors through the original block variable and vanishes at the coarse
zero field also vanishes on the exact-kernel Fourier witness.  No regularity,
linearity, positivity, or growth bound is required of that penalty.

For proposed repairs, this file also machine-checks the exact Rayleigh identity
and the resulting necessary budget when the block map is replaced and a fine
linear term is added.  Positivity of the added term is recorded separately:
it is physically relevant, but the algebraic identity itself does not need it.
-/

namespace YangMills.RG

open Matrix Module

/-- A full-space flat Poincare estimate with an arbitrary real-valued penalty
that factors through the coarse block variable. -/
def FactorizedFlatGaugeHodgePoincare
    (d L N' Nc : ℕ)
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Φ : CoarsePhysicalOneCochain d N' Nc → ℝ)
    (CP : ℝ) : Prop :=
  0 < CP ∧
    ∀ A : FinePhysicalOneCochain d L N' Nc,
      ‖A‖ ^ 2 ≤
        CP *
          (inner ℝ A (flatGaugeHodgeK0CLM d (L * N') Nc ρ A)
            + Φ (flatBlockConstraintQCLM
                (d := d) (Nc := Nc) L N' A))

/-- Every factorized penalty with `Φ 0 = 0` gives the same Fourier lower
bound, even when `Φ` is nonlinear or discontinuous. -/
theorem factorizedFlatPoincare_fourier_lower_bound
    (L N' Nc : ℕ) [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (Φ : CoarsePhysicalOneCochain 4 N' Nc → ℝ)
    (hΦ0 : Φ 0 = 0) (CP : ℝ)
    (hP : FactorizedFlatGaugeHodgePoincare
      4 L N' Nc ρ Φ CP) :
    1 ≤ CP * blockFourierEigenvalue L := by
  let i : Fin 4 := ⟨0, by omega⟩
  let j : Fin 4 := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let A : FinePhysicalOneCochain 4 L N' Nc :=
    blockFourierModeCochain 4 L N' Nc hNc i j
  have hnorm : ‖A‖ ^ 2 = (((L * N' : ℕ) : ℝ) ^ 4) := by
    dsimp [A]
    exact norm_sq_blockFourierModeCochain 4 L N' Nc hNc i j
  have hH :
      inner ℝ A (flatGaugeHodgeK0CLM 4 (L * N') Nc ρ A) =
        (((L * N' : ℕ) : ℝ) ^ 4) * blockFourierEigenvalue L := by
    dsimp [A]
    exact flatGaugeHodgeK0_inner_blockFourierModeCochain_of_ne
      4 L N' Nc ρ hL hNc i j hij
  have hQ :
      flatBlockConstraintQCLM (d := 4) (Nc := Nc) L N' A = 0 := by
    dsimp [A]
    exact flatBlockConstraintQCLM_blockFourierMode_eq_zero
      hL hNc i j hij
  have hmain := hP.2 A
  rw [hQ, hΦ0, add_zero, hH, hnorm] at hmain
  have hvol : (0 : ℝ) < (((L * N' : ℕ) : ℝ) ^ 4) := by
    have hLN : 0 < L * N' := Nat.mul_pos
      (Nat.pos_of_ne_zero (NeZero.ne L))
      (Nat.pos_of_ne_zero (NeZero.ne N'))
    positivity
  have hfactored :
      (1 : ℝ) * (((L * N' : ℕ) : ℝ) ^ 4) ≤
        (CP * blockFourierEigenvalue L) *
          (((L * N' : ℕ) : ℝ) ^ 4) := by
    convert hmain using 1 <;> ring
  exact (mul_le_mul_iff_of_pos_right hvol).mp hfactored

/-- The constant-before-volume gate for an arbitrary scale-dependent family
of penalties which factor through the original block variable. -/
def VolumeUniformFactorizedFlatPoincareGate
    (N' Nc : ℕ) [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Φ : ℕ → CoarsePhysicalOneCochain 4 N' Nc → ℝ) : Prop :=
  ∃ CP : ℝ, 0 < CP ∧
    (∀ k : ℕ, Φ k 0 = 0) ∧
    ∀ k : ℕ,
      FactorizedFlatGaugeHodgePoincare
        4 (k + 1) N' Nc ρ (Φ k) CP

/-- **Factor-through-kernel all-scales no-go.**  No family of penalties
depending only on the original coarse block field and vanishing at zero can
restore a volume-uniform full-space Poincare constant. -/
theorem volumeUniformFactorizedFlatPoincareGate_fourier_false
    {N' Nc : ℕ} [NeZero N'] [NeZero Nc]
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (Φ : ℕ → CoarsePhysicalOneCochain 4 N' Nc → ℝ) :
    ¬ VolumeUniformFactorizedFlatPoincareGate N' Nc ρ Φ := by
  rintro ⟨CP, hCP, hΦ0, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * Real.pi ^ 2 * CP)
  let L := n + 2
  have hL : 2 ≤ L := by simp [L]
  haveI : NeZero L := ⟨by omega⟩
  let k := L - 1
  have hk : k + 1 = L := by
    dsimp [k]
    omega
  have hP : FactorizedFlatGaugeHodgePoincare
      4 L N' Nc ρ (Φ k) CP := by
    simpa only [hk] using hall k
  have hone : 1 ≤ CP * blockFourierEigenvalue L :=
    factorizedFlatPoincare_fourier_lower_bound
      L N' Nc ρ hL hNc (Φ k) (hΦ0 k) CP hP
  have hlambda : blockFourierEigenvalue L ≤ (2 * Real.pi / L) ^ 2 :=
    blockFourierEigenvalue_le L
  have hone' : 1 ≤ CP * (2 * Real.pi / (L : ℝ)) ^ 2 :=
    le_trans hone (mul_le_mul_of_nonneg_left hlambda (le_of_lt hCP))
  have hLR : (0 : ℝ) < (L : ℝ) := by positivity
  have hLRne : (L : ℝ) ≠ 0 := ne_of_gt hLR
  have hscaled := mul_le_mul_of_nonneg_right hone' (sq_nonneg (L : ℝ))
  have hupper : (L : ℝ) ^ 2 ≤ 4 * Real.pi ^ 2 * CP := by
    calc
      (L : ℝ) ^ 2 = 1 * (L : ℝ) ^ 2 := by ring
      _ ≤ (CP * (2 * Real.pi / (L : ℝ)) ^ 2) * (L : ℝ) ^ 2 := hscaled
      _ = 4 * Real.pi ^ 2 * CP := by
        field_simp
        ring
  have hnR : 4 * Real.pi ^ 2 * CP < (n : ℝ) := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hbig : 4 * Real.pi ^ 2 * CP < (L : ℝ) ^ 2 := by
    dsimp [L]
    push_cast
    nlinarith
  linarith

/-- A linear fine-space term has nonnegative quadratic form.  Self-adjointness
is not needed for the witness identity, so positivity is kept as an explicit
and independently checkable hypothesis. -/
def FineQuadraticPositiveSemidefinite
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (V : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc) : Prop :=
  ∀ A, 0 ≤ inner ℝ A (V A)

/-- A proposed repaired full-space estimate: the block measurement may be
changed before postconditioning and a fine-space linear term may be added. -/
def RepairedFlatGaugeHodgePoincare
    (d L N' Nc : ℕ)
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Qtilde : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc)
    (T : CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc)
    (V : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (CP : ℝ) : Prop :=
  0 < CP ∧
    ∀ A : FinePhysicalOneCochain d L N' Nc,
      ‖A‖ ^ 2 ≤
        CP *
          (inner ℝ A (flatGaugeHodgeK0CLM d (L * N') Nc ρ A)
            + ‖T (Qtilde A)‖ ^ 2
            + inner ℝ A (V A))

/-- Exact normalized energy of the Fourier witness for a changed block map,
an arbitrary linear postconditioner, and an arbitrary fine linear term. -/
theorem repairedFlatPoincare_blockFourier_rayleigh_eq
    (L N' Nc : ℕ) [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (Qtilde : FinePhysicalOneCochain 4 L N' Nc →L[ℝ]
      CoarsePhysicalOneCochain 4 N' Nc)
    (T : CoarsePhysicalOneCochain 4 N' Nc →L[ℝ]
      CoarsePhysicalOneCochain 4 N' Nc)
    (V : FinePhysicalOneCochain 4 L N' Nc →L[ℝ]
      FinePhysicalOneCochain 4 L N' Nc) :
    let i : Fin 4 := ⟨0, by omega⟩
    let j : Fin 4 := ⟨1, by omega⟩
    let A : FinePhysicalOneCochain 4 L N' Nc :=
      blockFourierModeCochain 4 L N' Nc hNc i j
    (inner ℝ A (flatGaugeHodgeK0CLM 4 (L * N') Nc ρ A)
        + ‖T (Qtilde A)‖ ^ 2 + inner ℝ A (V A)) / ‖A‖ ^ 2 =
      blockFourierEigenvalue L
        + ‖T (Qtilde A)‖ ^ 2 / (((L * N' : ℕ) : ℝ) ^ 4)
        + inner ℝ A (V A) / (((L * N' : ℕ) : ℝ) ^ 4) := by
  dsimp only
  let i : Fin 4 := ⟨0, by omega⟩
  let j : Fin 4 := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have hnorm :
      ‖blockFourierModeCochain 4 L N' Nc hNc i j‖ ^ 2 =
        (((L * N' : ℕ) : ℝ) ^ 4) := by
    exact norm_sq_blockFourierModeCochain 4 L N' Nc hNc i j
  have hH :
      inner ℝ (blockFourierModeCochain 4 L N' Nc hNc i j)
          (flatGaugeHodgeK0CLM 4 (L * N') Nc ρ
            (blockFourierModeCochain 4 L N' Nc hNc i j)) =
        (((L * N' : ℕ) : ℝ) ^ 4) * blockFourierEigenvalue L := by
    exact flatGaugeHodgeK0_inner_blockFourierModeCochain_of_ne
      4 L N' Nc ρ hL hNc i j hij
  rw [hH, hnorm]
  have hvol : (0 : ℝ) < (((L * N' : ℕ) : ℝ) ^ 4) := by
    have hLN : 0 < L * N' := Nat.mul_pos
      (Nat.pos_of_ne_zero (NeZero.ne L))
      (Nat.pos_of_ne_zero (NeZero.ne N'))
    positivity
  have hbase : (((L * N' : ℕ) : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num)] at hvol
    linarith
  field_simp [hbase]

/-- Any full-space repaired estimate must pay the exact normalized witness
budget.  This is the machine-checked necessary half of the repair criterion. -/
theorem repairedFlatPoincare_blockFourier_budget
    (L N' Nc : ℕ) [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (Qtilde : FinePhysicalOneCochain 4 L N' Nc →L[ℝ]
      CoarsePhysicalOneCochain 4 N' Nc)
    (T : CoarsePhysicalOneCochain 4 N' Nc →L[ℝ]
      CoarsePhysicalOneCochain 4 N' Nc)
    (V : FinePhysicalOneCochain 4 L N' Nc →L[ℝ]
      FinePhysicalOneCochain 4 L N' Nc)
    (CP : ℝ)
    (hP : RepairedFlatGaugeHodgePoincare
      4 L N' Nc ρ Qtilde T V CP) :
    let i : Fin 4 := ⟨0, by omega⟩
    let j : Fin 4 := ⟨1, by omega⟩
    let A : FinePhysicalOneCochain 4 L N' Nc :=
      blockFourierModeCochain 4 L N' Nc hNc i j
    1 ≤ CP *
      (blockFourierEigenvalue L
        + ‖T (Qtilde A)‖ ^ 2 / (((L * N' : ℕ) : ℝ) ^ 4)
        + inner ℝ A (V A) / (((L * N' : ℕ) : ℝ) ^ 4)) := by
  dsimp only
  let i : Fin 4 := ⟨0, by omega⟩
  let j : Fin 4 := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let A : FinePhysicalOneCochain 4 L N' Nc :=
    blockFourierModeCochain 4 L N' Nc hNc i j
  have hnorm : ‖A‖ ^ 2 = (((L * N' : ℕ) : ℝ) ^ 4) := by
    dsimp [A]
    exact norm_sq_blockFourierModeCochain 4 L N' Nc hNc i j
  have hH :
      inner ℝ A (flatGaugeHodgeK0CLM 4 (L * N') Nc ρ A) =
        (((L * N' : ℕ) : ℝ) ^ 4) * blockFourierEigenvalue L := by
    dsimp [A]
    exact flatGaugeHodgeK0_inner_blockFourierModeCochain_of_ne
      4 L N' Nc ρ hL hNc i j hij
  have hmain := hP.2 A
  rw [hnorm, hH] at hmain
  have hvol : (0 : ℝ) < (((L * N' : ℕ) : ℝ) ^ 4) := by
    have hLN : 0 < L * N' := Nat.mul_pos
      (Nat.pos_of_ne_zero (NeZero.ne L))
      (Nat.pos_of_ne_zero (NeZero.ne N'))
    positivity
  have hfactored :
      (1 : ℝ) * (((L * N' : ℕ) : ℝ) ^ 4) ≤
        (CP *
          (blockFourierEigenvalue L
            + ‖T (Qtilde A)‖ ^ 2 / (((L * N' : ℕ) : ℝ) ^ 4)
            + inner ℝ A (V A) / (((L * N' : ℕ) : ℝ) ^ 4))) *
          (((L * N' : ℕ) : ℝ) ^ 4) := by
    calc
      (1 : ℝ) * (((L * N' : ℕ) : ℝ) ^ 4) =
          (((L * N' : ℕ) : ℝ) ^ 4) := by ring
      _ ≤ CP *
          ((((L * N' : ℕ) : ℝ) ^ 4) * blockFourierEigenvalue L
            + ‖T (Qtilde A)‖ ^ 2 + inner ℝ A (V A)) := hmain
      _ = (CP *
          (blockFourierEigenvalue L
            + ‖T (Qtilde A)‖ ^ 2 / (((L * N' : ℕ) : ℝ) ^ 4)
            + inner ℝ A (V A) / (((L * N' : ℕ) : ℝ) ^ 4))) *
          (((L * N' : ℕ) : ℝ) ^ 4) := by
            have hbase : (((L * N' : ℕ) : ℝ)) ≠ 0 := by
              intro hzero
              rw [hzero, zero_pow (by norm_num)] at hvol
              linarith
            field_simp [hbase]
  exact (mul_le_mul_iff_of_pos_right hvol).mp hfactored

end YangMills.RG
