import YangMills.RG.BalabanCMP89NeumannRectangleActiveRegion
import YangMills.RG.BalabanCMP99SourceRegionalLiftTower

/-!
# Complete-block lift of the CMP89 half-open rectangle

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

This module proves that the generated regional lift preserves the literal
half-open rectangular shape and constructs its terminal site equivalence
without accepting an arbitrary geometric dictionary.
-/

namespace YangMills.RG

noncomputable section

/-- Multiplication of every integer side length by one block scale. -/
def cmp89SourceNeumannScaleRectangleSide
    (M : ℕ) (m : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun mu => (M : ℤ) * m mu

/-- Multiplication of every side length by the complete depth scale. -/
def cmp89SourceNeumannScaleRectangleSidePow
    (M depth : ℕ) (m : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun mu => ((M ^ depth : ℕ) : ℤ) * m mu

/-- A complete-block lift of a half-open rectangle is exactly the half-open
rectangle whose side lengths have been multiplied by the block scale. -/
theorem cmp99LiftActiveRegion_cmp89Rectangle_eq
    {M N : ℕ} [NeZero M] [NeZero N]
    {m : Fin 4 → ℤ} (hm : ∀ mu, 0 < m mu) :
    cmp99LiftActiveRegion (M := M)
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m) =
      cmp89SourceNeumannRectangleActiveRegion (N := M * N)
        (cmp89SourceNeumannScaleRectangleSide M m) := by
  apply ActiveGaugeRegion.ext
  ext x
  rw [mem_cmp99LiftActiveRegion_sites_iff]
  rw [mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff]
  rw [mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff]
  apply forall_congr'
  intro mu
  rw [blockSite_val]
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hm0 : 0 ≤ m mu := (hm mu).le
  have hscaled0 : 0 ≤ (M : ℤ) * m mu :=
    mul_nonneg (by exact_mod_cast hM.le) hm0
  have hmcast : (Int.toNat (m mu) : ℤ) = m mu :=
    Int.toNat_of_nonneg hm0
  have hscaledcast :
      (Int.toNat ((M : ℤ) * m mu) : ℤ) = (M : ℤ) * m mu :=
    Int.toNat_of_nonneg hscaled0
  have hscalednat :
      Int.toNat ((M : ℤ) * m mu) = M * Int.toNat (m mu) := by
    exact_mod_cast (show
      (Int.toNat ((M : ℤ) * m mu) : ℤ) =
        ((M * Int.toNat (m mu) : ℕ) : ℤ) by
      calc
        (Int.toNat ((M : ℤ) * m mu) : ℤ) = (M : ℤ) * m mu := hscaledcast
        _ = (M : ℤ) * (Int.toNat (m mu) : ℤ) := by rw [hmcast]
        _ = ((M * Int.toNat (m mu) : ℕ) : ℤ) := by norm_num)
  rw [hscalednat, Nat.div_lt_iff_lt_mul hM]
  simp only [Nat.mul_comm]

/-- The entire generated lift tower retains the literal rectangular shape;
the terminal sides are multiplied by the exact depth scale. -/
theorem cmp99IteratedLiftActiveRegion_cmp89Rectangle_eq
    {M N : ℕ} [NeZero M] [NeZero N]
    {m : Fin 4 → ℤ} (hm : ∀ mu, 0 < m mu) (depth : ℕ) :
    cmp99IteratedLiftActiveRegion (M := M)
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m) depth =
      cmp89SourceNeumannRectangleActiveRegion
        (N := cmp99RegionalLatticeSize M N depth)
        (cmp89SourceNeumannScaleRectangleSidePow M depth m) := by
  induction depth with
  | zero =>
      have hside : cmp89SourceNeumannScaleRectangleSidePow M 0 m = m := by
        funext mu
        simp [cmp89SourceNeumannScaleRectangleSidePow]
      exact (congrArg
        (cmp89SourceNeumannRectangleActiveRegion (N := N)) hside).symm
  | succ depth ih =>
      rw [cmp99IteratedLiftActiveRegion_succ, ih]
      have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
      have hpow : 0 < M ^ depth := pow_pos hM depth
      have hscaled : ∀ mu,
          0 < cmp89SourceNeumannScaleRectangleSidePow M depth m mu := by
        intro mu
        dsimp [cmp89SourceNeumannScaleRectangleSidePow]
        exact mul_pos (by exact_mod_cast hpow) (hm mu)
      rw [cmp99LiftActiveRegion_cmp89Rectangle_eq hscaled]
      have hside :
          cmp89SourceNeumannScaleRectangleSide M
              (cmp89SourceNeumannScaleRectangleSidePow M depth m) =
            cmp89SourceNeumannScaleRectangleSidePow M (depth + 1) m := by
        funext mu
        simp only [cmp89SourceNeumannScaleRectangleSide,
          cmp89SourceNeumannScaleRectangleSidePow, pow_succ, Nat.cast_mul]
        ring
      simpa only [cmp99RegionalLatticeSize_succ] using congrArg
        (cmp89SourceNeumannRectangleActiveRegion
          (N := M * cmp99RegionalLatticeSize M N depth)) hside

/-- Canonical source-site equivalence for the full generated rectangle lift;
the only geometric input is the visible coarse rectangle and its fit. -/
noncomputable def cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
    {M N : ℕ} [NeZero M] [NeZero N]
    {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (depth : ℕ) :
    CMP89SourceNeumannIntegerRectanglePoint
        (cmp89SourceNeumannScaleRectangleSidePow M depth m) ≃
      ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M)
          (cmp89SourceNeumannRectangleActiveRegion (N := N) m) depth) := by
  rw [cmp99IteratedLiftActiveRegion_cmp89Rectangle_eq hm depth]
  apply cmp89SourceNeumannRectangleSiteEquiv
  · intro mu
    dsimp [cmp89SourceNeumannScaleRectangleSidePow]
    exact mul_pos
      (by exact_mod_cast
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne M)) depth))
      (hm mu)
  · intro mu
    dsimp [cmp89SourceNeumannScaleRectangleSidePow]
    rw [cmp99RegionalLatticeSize_eq_pow_mul]
    norm_num only [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (hfit mu) (by positivity)

/-- The one-scale lifted rectangle therefore has a canonical source-site
equivalence; no arbitrary equivalence is accepted. -/
noncomputable def cmp89SourceNeumannLiftedRectangleSiteEquiv
    {M N : ℕ} [NeZero M] [NeZero N]
    {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu ≤ (N : ℤ)) :
    CMP89SourceNeumannIntegerRectanglePoint
        (cmp89SourceNeumannScaleRectangleSide M m) ≃
      ActiveGaugeRegion.Site
        (cmp99LiftActiveRegion (M := M)
          (cmp89SourceNeumannRectangleActiveRegion (N := N) m)) := by
  rw [cmp99LiftActiveRegion_cmp89Rectangle_eq hm]
  apply cmp89SourceNeumannRectangleSiteEquiv
  · intro mu
    exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)) (hm mu)
  · intro mu
    dsimp [cmp89SourceNeumannScaleRectangleSide]
    have hM0 : (0 : ℤ) ≤ M := by exact_mod_cast (Nat.zero_le M)
    exact mul_le_mul_of_nonneg_left (hfit mu) hM0

end

end YangMills.RG
