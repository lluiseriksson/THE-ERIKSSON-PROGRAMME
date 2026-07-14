/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalPoincareSectorQuotient

/-!
# W-3a — the lowest-mode family: the falsifier's witness cochain
(`hRpoly` campaign — the W-3 ladder over Addenda 495/499/501)

W-3 is the registered ONE-SIDED falsifier of the quotient Poincaré gate
(`VolumeUniformQuotientPoincareGate`, Addendum 499; epistemics corrected
in Addendum 501): it can REFUTE the gate if an explicit fluctuation
family has vanishing Rayleigh quotient; a bounded quotient on the family
only removes one counter-witness candidate and keeps the gate open —
proving the gate would additionally require an all-modes estimate or a
spectral-minimality theorem, and NO such claim is made anywhere in this
ladder.

This brick (W-3a) delivers the FAMILY and its two exact identities:

* **`squareSign`** — the half-period ±1 square profile on the even
  circle `Fin (M + M)`: `+1` on `[0, M)`, `−1` on `[M, 2M)`.  The
  lowest genuinely non-constant profile in the square-wave basis: ONE
  sign change per half-torus (two jump slices).  Chosen over the cosine
  because every sum below is an EXACT finite ±1 identity — no trigonometry,
  no approximation (the dictamen's instruction 2).  Parameterization
  choices, declared: (a) only EVEN side lengths `N = M + M` are covered
  (an odd-side lowest mode cannot be orthogonal to constants by a pure
  sign profile; the odd case is out of scope for the falsifier, which
  only needs SOME volume sequence `L → ∞`); (b) `M ≥ 1` (`NeZero M`)
  excludes the degenerate empty circle.
* **`squareModeCochain d M Nc i j w`** — the mode: oscillation in the
  spatial direction `j`, supported on bonds of direction `i`, internal
  vector `w`:  `A (x, k) = (if k = i then squareSign M (x j) • w else 0)`.
* **`squareModeCochain_isFluctuation`** — orthogonality to EVERY
  constant generator, by the exact zero-sum identity
  `∑ m, squareSign M m = 0` (`sum_squareSign`, proved by the
  `finSumFinEquiv` reindex: `M·(+1) + M·(−1) = 0`), lifted through the
  box by a fiberwise product split (`sum_finBox_squareSign`).
* **`norm_sq_squareModeCochain`** — the EXACT norm:
  `‖A‖² = (M+M)^d · ‖w‖²` (the profile squares to `1` bond-wise).
* **`fluctuation_constant_eq_zero`** + **`squareModeCochain_ne_constant`**
  — the mode is genuinely non-constant: a fluctuation cochain that IS
  constant must vanish, and the mode has positive norm for `w ≠ 0`.
* **`exists_nonzero_fluctuation`** — non-vacuity of the fluctuation
  space itself (`Nc ≥ 2`, same witness discipline as W-1).

**What this brick does NOT do (registered ladder).**  It does not
evaluate the quadratic form: W-3b computes the Hodge term
`⟪A, K₀ A⟫ = ‖curl A‖² + ‖div A‖²` on the mode (expected: exactly two
jump slices contribute — the near-harmonicity), and W-3c computes the
block term `‖Q A‖²` and assembles the physical Rayleigh quotient
`R_L = (⟪A,K₀A⟫ + ‖QA‖²)/‖A‖²` WITHOUT normalizations that silently
cancel `L`-dependence, then decides: EITHER a sequence `L_k → ∞` with
`R → 0` and the formal `¬ VolumeUniformQuotientPoincareGate` (second
wall), OR a positive lower bound on THIS mode only — declared as
candidate-eliminated, gate still open.  The mechanism separation
(Hodge degeneration vs block response vs `(L, N', d, direction)`
dependence) is an explicit W-3c obligation.  NOT `hRpoly`, NOT the
mass gap; Clay distance unchanged, ~0% (<0.1%).

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module

/-- Even side lengths are nonzero when the half-period is. -/
instance (M : ℕ) [NeZero M] : NeZero (M + M) :=
  ⟨by have h := NeZero.ne M; omega⟩

/-! ## The half-period square profile -/

/-- The ±1 half-period square profile on the even circle `Fin (M + M)`:
`+1` on the first half, `−1` on the second.  The lowest genuinely
non-constant square-wave profile (one sign change per half-torus). -/
def squareSign (M : ℕ) (m : Fin (M + M)) : ℝ :=
  if (m : ℕ) < M then 1 else -1

theorem squareSign_sq (M : ℕ) (m : Fin (M + M)) :
    squareSign M m ^ 2 = 1 := by
  unfold squareSign
  split <;> norm_num

/-- **The exact zero-sum identity**: the profile is orthogonal to
constants on the circle.  Proof by the `finSumFinEquiv` reindex —
`M` terms `+1` plus `M` terms `−1`. -/
theorem sum_squareSign (M : ℕ) :
    ∑ m : Fin (M + M), squareSign M m = 0 := by
  rw [← finSumFinEquiv.sum_comp (fun m : Fin (M + M) => squareSign M m)]
  rw [Fintype.sum_sum_type]
  have h1 : ∀ a : Fin M,
      squareSign M (finSumFinEquiv (Sum.inl a)) = 1 := by
    intro a
    have ha : ((finSumFinEquiv (Sum.inl a) : Fin (M + M)) : ℕ) < M := by
      rw [finSumFinEquiv_apply_left]
      simp only [Fin.val_castAdd]
      exact a.isLt
    unfold squareSign
    rw [if_pos ha]
  have h2 : ∀ b : Fin M,
      squareSign M (finSumFinEquiv (Sum.inr b)) = -1 := by
    intro b
    have hb : ¬ ((finSumFinEquiv (Sum.inr b) : Fin (M + M)) : ℕ) < M := by
      rw [finSumFinEquiv_apply_right]
      simp only [Fin.val_natAdd]
      omega
    unfold squareSign
    rw [if_neg hb]
  rw [Finset.sum_congr rfl (fun a _ => h1 a),
    Finset.sum_congr rfl (fun b _ => h2 b)]
  simp

/-- The zero-sum identity lifted through the box: summing the profile of
one coordinate over all sites vanishes (the other `d − 1` coordinates
contribute a common fiber factor that multiplies zero). -/
theorem sum_finBox_squareSign (d M : ℕ) (j : Fin d) :
    ∑ x : FinBox d (M + M), squareSign M (x j) = 0 := by
  classical
  have hsplit :
      ∑ x : FinBox d (M + M), squareSign M (x j)
        = ∑ p : Fin (M + M) × ({k : Fin d // k ≠ j} → Fin (M + M)),
            squareSign M p.1 := by
    rw [← Equiv.sum_comp (Equiv.piSplitAt j (fun _ : Fin d => Fin (M + M)))
      (fun p => squareSign M p.1)]
    rfl
  rw [hsplit, Fintype.sum_prod_type]
  simp only [Finset.sum_const]
  rw [← Finset.smul_sum, sum_squareSign, smul_zero]

/-! ## The mode cochain -/

/-- **The lowest-mode witness cochain**: oscillation in the spatial
direction `j`, supported on bonds of direction `i`, internal vector `w`. -/
noncomputable def squareModeCochain (d M Nc : ℕ) [NeZero M]
    (i j : Fin d) (w : SUNLieCoord Nc) :
    PhysicalGaugeOneCochain d (M + M) Nc :=
  WithLp.toLp 2 fun b : PhysicalBond d (M + M) =>
    if b.2 = i then squareSign M (b.1 j) • w else 0

@[simp]
theorem squareModeCochain_apply {d M Nc : ℕ} [NeZero M]
    (i j : Fin d) (w : SUNLieCoord Nc) (b : PhysicalBond d (M + M)) :
    squareModeCochain d M Nc i j w b
      = if b.2 = i then squareSign M (b.1 j) • w else 0 := rfl

/-- **Orthogonality to every constant generator** — the mode is a
fluctuation cochain, by the exact zero-sum identity (no approximation). -/
theorem squareModeCochain_isFluctuation (d M Nc : ℕ) [NeZero M]
    (i j : Fin d) (w : SUNLieCoord Nc) :
    IsFluctuationCochain (squareModeCochain d M Nc i j w) := by
  classical
  intro v
  rw [PiLp.inner_apply]
  have hterm : ∀ b : PhysicalBond d (M + M),
      (inner ℝ (constantPhysicalGaugeOneCochain
          (d := d) (N := M + M) (Nc := Nc) v b)
        (squareModeCochain d M Nc i j w b) : ℝ)
        = if b.2 = i
            then squareSign M (b.1 j) * (inner ℝ (v i) w : ℝ)
            else 0 := by
    intro b
    rw [constantPhysicalGaugeOneCochain_apply, squareModeCochain_apply]
    by_cases hb : b.2 = i
    · rw [if_pos hb, if_pos hb, hb, real_inner_smul_right]
    · rw [if_neg hb, if_neg hb, inner_zero_right]
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ x : FinBox d (M + M),
      (∑ k : Fin d, if k = i
          then squareSign M (x j) * (inner ℝ (v i) w : ℝ) else 0)
        = squareSign M (x j) * (inner ℝ (v i) w : ℝ) :=
    fun x => Finset.sum_ite_eq' Finset.univ i
      (fun _ => squareSign M (x j) * (inner ℝ (v i) w : ℝ))
      |>.trans (if_pos (Finset.mem_univ i))
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [← Finset.sum_mul, sum_finBox_squareSign, zero_mul]

/-- **The exact norm of the mode**: `‖A‖² = (M+M)^d · ‖w‖²`. -/
theorem norm_sq_squareModeCochain (d M Nc : ℕ) [NeZero M]
    (i j : Fin d) (w : SUNLieCoord Nc) :
    ‖squareModeCochain d M Nc i j w‖ ^ 2
      = ((M + M : ℕ) : ℝ) ^ d * ‖w‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  have hterm : ∀ b : PhysicalBond d (M + M),
      ‖squareModeCochain d M Nc i j w b‖ ^ 2
        = if b.2 = i then ‖w‖ ^ 2 else 0 := by
    intro b
    rw [squareModeCochain_apply]
    by_cases hb : b.2 = i
    · rw [if_pos hb, if_pos hb, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, squareSign_sq, one_mul]
    · rw [if_neg hb, if_neg hb, norm_zero]
      norm_num
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ _x : FinBox d (M + M),
      (∑ k : Fin d, if k = i then ‖w‖ ^ 2 else 0) = ‖w‖ ^ 2 :=
    fun _x => (Finset.sum_ite_eq' Finset.univ i (fun _ => ‖w‖ ^ 2)).trans
      (if_pos (Finset.mem_univ i))
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [Finset.sum_const, Finset.card_univ, card_finBox, nsmul_eq_mul]
  push_cast
  ring

/-! ## Genuine non-constancy -/

/-- A fluctuation cochain that IS a constant cochain must vanish: it is
orthogonal to itself. -/
theorem fluctuation_constant_eq_zero {d N Nc : ℕ} [NeZero N]
    (v : Fin d → SUNLieCoord Nc)
    (h : IsFluctuationCochain
      (constantPhysicalGaugeOneCochain (d := d) (N := N) (Nc := Nc) v)) :
    constantPhysicalGaugeOneCochain (d := d) (N := N) (Nc := Nc) v = 0 := by
  have hself := h v
  rw [real_inner_self_eq_norm_sq] at hself
  have hnorm : ‖constantPhysicalGaugeOneCochain
      (d := d) (N := N) (Nc := Nc) v‖ = 0 := by
    have := sq_eq_zero_iff.mp hself
    exact this
  exact norm_eq_zero.mp hnorm

/-- **The mode is genuinely non-constant** (`w ≠ 0`): it cannot equal any
constant cochain — a fluctuation cochain that is constant vanishes, but
the mode has positive norm. -/
theorem squareModeCochain_ne_constant (d M Nc : ℕ) [NeZero M]
    (i j : Fin d) {w : SUNLieCoord Nc} (hw : w ≠ 0)
    (v : Fin d → SUNLieCoord Nc) :
    squareModeCochain d M Nc i j w
      ≠ constantPhysicalGaugeOneCochain (d := d) (N := M + M) (Nc := Nc) v := by
  intro heq
  have hfluct : IsFluctuationCochain
      (constantPhysicalGaugeOneCochain (d := d) (N := M + M) (Nc := Nc) v) := by
    rw [← heq]
    exact squareModeCochain_isFluctuation d M Nc i j w
  have hzero := fluctuation_constant_eq_zero v hfluct
  rw [hzero] at heq
  have hnorm := norm_sq_squareModeCochain d M Nc i j w
  rw [heq] at hnorm
  have hMpos : (0 : ℝ) < ((M + M : ℕ) : ℝ) := by
    have h := NeZero.ne M
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hwpos : (0 : ℝ) < ‖w‖ ^ 2 := by
    have : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    positivity
  have hpos : (0 : ℝ) < ((M + M : ℕ) : ℝ) ^ d * ‖w‖ ^ 2 := by
    have hpow : (0 : ℝ) < ((M + M : ℕ) : ℝ) ^ d := pow_pos hMpos d
    exact mul_pos hpow hwpos
  rw [← hnorm] at hpos
  simp at hpos

/-! ## Non-vacuity of the fluctuation space -/

/-- The fluctuation space contains a NONZERO cochain (`Nc ≥ 2`; the
internal witness is the same `EuclideanSpace.single` discipline as W-1). -/
theorem exists_nonzero_fluctuation (d M Nc : ℕ) [NeZero M]
    (i j : Fin d) (hNc : 2 ≤ Nc) :
    ∃ A : PhysicalGaugeOneCochain d (M + M) Nc,
      IsFluctuationCochain A ∧ A ≠ 0 := by
  have hdim : 0 < Nc ^ 2 - 1 := by
    have h4 : 2 * 2 ≤ Nc * Nc := Nat.mul_le_mul hNc hNc
    have hsq : Nc ^ 2 = Nc * Nc := by ring
    omega
  set w : SUNLieCoord Nc := EuclideanSpace.single ⟨0, hdim⟩ (1 : ℝ) with hw
  have hwne : w ≠ 0 := by
    intro h0
    have h1 : ‖w‖ = 1 := by
      rw [hw, EuclideanSpace.norm_single]
      norm_num
    rw [h0, norm_zero] at h1
    norm_num at h1
  refine ⟨squareModeCochain d M Nc i j w,
    squareModeCochain_isFluctuation d M Nc i j w, ?_⟩
  intro h0
  have hnorm := norm_sq_squareModeCochain d M Nc i j w
  rw [h0] at hnorm
  have hMpos : (0 : ℝ) < ((M + M : ℕ) : ℝ) := by
    have h := NeZero.ne M
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hwpos : (0 : ℝ) < ‖w‖ ^ 2 := by
    have : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hwne
    positivity
  have hpos : (0 : ℝ) < ((M + M : ℕ) : ℝ) ^ d * ‖w‖ ^ 2 :=
    mul_pos (pow_pos hMpos d) hwpos
  rw [← hnorm] at hpos
  simp at hpos

end YangMills.RG
