/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.LinearAveraging

/-!
# ℓ² Cauchy–Schwarz bound for the linear operator Q (gauge-RG, UV-U1 brick S1)

`docs/UV-U1-SMALL-FIELD-PLAN.md` S1.  The block-averaging operator
`Q = linAvg` at a coarse bond is an `L^{-d}`-normalised sum, over the
`L^d`-point source block, of the `L`-step fine line integrals.  This
file proves the **Cauchy–Schwarz mean-square bound**
`‖linAvg A c‖² ≤ L^{1-d}·∑_{(x,k)} ‖A⟨shiftᵏ x,dir,+⟩‖²` — the standard
ℓ²-type operator estimate the small-field analysis consumes.

**Honest calibration (not a standalone contraction).**  This bound is
*not* by itself a contraction: the line integral sums `L` fine bonds, so
on a constant field of size `ε` the right side is `L^{1-d}·L^{d+1}·ε²`,
giving `‖linAvg A c‖ ≤ L·ε` — coarse-bond *growth* by `L`, which is
correct (a coarse bond spans `L` fine bonds).  Bałaban's per-scale
contraction emerges only after the RG **field rescaling** and the
**ℓ²(lattice) operator assembly with multiplicity accounting** (brick
S2) — it is a property of the rescaled covariance, not of this single
estimate.  S1 is the certified Cauchy–Schwarz input to that analysis.

**Source.** T. Bałaban, CMP 95 (1984); strategy/framing Lluis Eriksson
(ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

open scoped BigOperators

variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

open scoped Classical in
/-- **ℓ² Cauchy–Schwarz bound for `Q`** (brick S1): the squared norm of
the block average at a coarse bond is bounded by `(L^d)⁻¹·L = L^{1-d}`
times the sum of squared fine-bond norms over the block,
`‖linAvg A c‖² ≤ (L^d)⁻¹·L · ∑_{(x,k)} ‖A⟨shiftᵏ x, dir, +⟩‖²`.
Cauchy–Schwarz on the `L^d`-fold average of the `L`-term line integrals.
(This is the certified ℓ²-type operator input; it is *not* a standalone
contraction — see the module docstring — the per-scale contraction needs
the RG rescaling + ℓ² assembly of brick S2.) -/
theorem norm_linAvg_sq_le (L N' : ℕ) [NeZero L] [NeZero N']
    (A : ConcreteEdge d (L * N') → V) (c : ConcreteEdge d N') :
    ‖linAvg L N' A c‖ ^ 2
      ≤ ((L : ℝ) ^ d)⁻¹ * (L : ℝ)
        * ∑ p ∈ blockOf L N' c.source ×ˢ Finset.range L,
            ‖A ⟨(fun y => FinBox.shift y c.dir)^[p.2] p.1, c.dir, true⟩‖ ^ 2 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hLd : (L : ℝ) ^ d ≠ 0 := pow_ne_zero d hL
  set s : Finset (FinBox d (L * N') × ℕ) :=
    blockOf L N' c.source ×ˢ Finset.range L with hs
  set g : FinBox d (L * N') × ℕ → V :=
    fun p => A ⟨(fun y => FinBox.shift y c.dir)^[p.2] p.1, c.dir, true⟩ with hg
  -- the block double-sum collapses to a single sum over the product
  have hS : ∑ x ∈ blockOf L N' c.source, fineLineSum L N' A c.dir x
      = ∑ p ∈ s, g p := by
    rw [hs, Finset.sum_product]
    rfl
  -- ℓ¹ bound via triangle inequality
  have h1 : ‖linAvg L N' A c‖ ≤ ((L : ℝ) ^ d)⁻¹ * ∑ p ∈ s, ‖g p‖ := by
    rw [linAvg, hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact norm_sum_le _ _
  -- Cauchy–Schwarz: (∑‖g‖)² ≤ #s · ∑‖g‖²
  have hCS : (∑ p ∈ s, ‖g p‖) ^ 2 ≤ (s.card : ℝ) * ∑ p ∈ s, ‖g p‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : (s.card : ℝ) = (L : ℝ) ^ d * (L : ℝ) := by
    rw [hs, Finset.card_product, blockOf_card, Finset.card_range]
    push_cast; ring
  calc ‖linAvg L N' A c‖ ^ 2
      ≤ (((L : ℝ) ^ d)⁻¹ * ∑ p ∈ s, ‖g p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (((L : ℝ) ^ d)⁻¹) ^ 2 * (∑ p ∈ s, ‖g p‖) ^ 2 := by rw [mul_pow]
    _ ≤ (((L : ℝ) ^ d)⁻¹) ^ 2 * ((s.card : ℝ) * ∑ p ∈ s, ‖g p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = ((L : ℝ) ^ d)⁻¹ * (L : ℝ) * ∑ p ∈ s, ‖g p‖ ^ 2 := by
        rw [hcard]; field_simp

open scoped Classical in
/-- **Blocks tile the fine lattice**: summing over each coarse block and
then over coarse sites recovers the sum over all fine sites (the blocks
are the fibers of `blockSite`). -/
theorem sum_blockOf {M : Type*} [AddCommMonoid M] (L N' : ℕ) [NeZero L]
    (g : FinBox d (L * N') → M) :
    ∑ y' : FinBox d N', ∑ x ∈ blockOf L N' y', g x
      = ∑ x : FinBox d (L * N'), g x := by
  simp only [blockOf]
  exact Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ _) g

/-- `y ↦ shift y μ` is a bijection of the fine torus (two-sided inverse
`shiftBack`). -/
theorem shift_bijective (N : ℕ) [NeZero N] (μ : Fin d) :
    Function.Bijective (fun y : FinBox d N => FinBox.shift y μ) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun y => FinBox.shiftBack y μ,
      fun y => FinBox.shiftBack_shift y μ, fun y => FinBox.shift_shiftBack y μ⟩

/-- Iterated shift is a bijection (iterate of a bijection). -/
theorem iterShift_bijective (N : ℕ) [NeZero N] (μ : Fin d) (k : ℕ) :
    Function.Bijective ((fun y : FinBox d N => FinBox.shift y μ)^[k]) :=
  (shift_bijective N μ).iterate k

open scoped Classical in
/-- **ℓ²(lattice) operator bound for `Q`** (UV-U1, brick S1', the genuine
deterministic contraction): summing the per-bond Cauchy–Schwarz bound
over all positively-oriented bonds, each fine bond is hit by exactly `L`
of the block/line triples (blocks tile the lattice, the shift is a
bijection), so
`∑_bonds ‖Q A‖² ≤ (L^d)⁻¹·L² · ∑_bonds ‖A‖² = L^{2-d}·∑_bonds ‖A‖²`.
The factor `L^{2-d}` is `< 1` for `d ≥ 3` (in particular the physical
`d = 4`): the bare averaging operator is an **ℓ²-contraction** — the
deterministic backbone of Bałaban's small-field RG step (before field
rescaling and the Gaussian covariance analysis, brick S2). -/
theorem linAvg_l2_le (L N' : ℕ) [NeZero L] [NeZero N']
    (A : ConcreteEdge d (L * N') → V) :
    ∑ y' : FinBox d N', ∑ μ : Fin d, ‖linAvg L N' A ⟨y', μ, true⟩‖ ^ 2
      ≤ ((L : ℝ) ^ d)⁻¹ * (L : ℝ) ^ 2
        * ∑ z : FinBox d (L * N'), ∑ μ : Fin d, ‖A ⟨z, μ, true⟩‖ ^ 2 := by
  -- per-bond Cauchy–Schwarz bound (S1), as a double sum over block × line
  have hpb : ∀ (y' : FinBox d N') (μ : Fin d),
      ‖linAvg L N' A ⟨y', μ, true⟩‖ ^ 2
        ≤ ((L : ℝ) ^ d)⁻¹ * L * ∑ x ∈ blockOf L N' y', ∑ k ∈ Finset.range L,
            ‖A ⟨(fun y => FinBox.shift y μ)^[k] x, μ, true⟩‖ ^ 2 := by
    intro y' μ
    have h := norm_linAvg_sq_le L N' A ⟨y', μ, true⟩
    rwa [Finset.sum_product] at h
  -- reindex the inner double sum to all fine bonds: each fine bond is hit L times
  have hreindex : ∀ μ : Fin d,
      ∑ x : FinBox d (L * N'), ∑ k ∈ Finset.range L,
          ‖A ⟨(fun y => FinBox.shift y μ)^[k] x, μ, true⟩‖ ^ 2
        = (L : ℝ) * ∑ z : FinBox d (L * N'), ‖A ⟨z, μ, true⟩‖ ^ 2 := by
    intro μ
    rw [Finset.sum_comm]
    have hbij : ∀ k ∈ Finset.range L,
        ∑ x : FinBox d (L * N'),
            ‖A ⟨(fun y => FinBox.shift y μ)^[k] x, μ, true⟩‖ ^ 2
          = ∑ z : FinBox d (L * N'), ‖A ⟨z, μ, true⟩‖ ^ 2 := fun k _ =>
      (iterShift_bijective (L * N') μ k).sum_comp
        (fun z => ‖A ⟨z, μ, true⟩‖ ^ 2)
    rw [Finset.sum_congr rfl hbij, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  calc ∑ y' : FinBox d N', ∑ μ : Fin d, ‖linAvg L N' A ⟨y', μ, true⟩‖ ^ 2
      ≤ ∑ y' : FinBox d N', ∑ μ : Fin d, ((L : ℝ) ^ d)⁻¹ * L
          * ∑ x ∈ blockOf L N' y', ∑ k ∈ Finset.range L,
              ‖A ⟨(fun y => FinBox.shift y μ)^[k] x, μ, true⟩‖ ^ 2 := by
        gcongr with y' _ μ _
        exact hpb y' μ
    _ = ((L : ℝ) ^ d)⁻¹ * L * ∑ μ : Fin d, ∑ x : FinBox d (L * N'),
          ∑ k ∈ Finset.range L,
            ‖A ⟨(fun y => FinBox.shift y μ)^[k] x, μ, true⟩‖ ^ 2 := by
        simp only [← Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun μ _ => ?_
        exact sum_blockOf L N' _
    _ = ((L : ℝ) ^ d)⁻¹ * L
          * ∑ μ : Fin d, (L : ℝ) * ∑ z : FinBox d (L * N'), ‖A ⟨z, μ, true⟩‖ ^ 2 := by
        rw [Finset.sum_congr rfl fun μ _ => hreindex μ]
    _ = ((L : ℝ) ^ d)⁻¹ * (L : ℝ) ^ 2
          * ∑ z : FinBox d (L * N'), ∑ μ : Fin d, ‖A ⟨z, μ, true⟩‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        ring

open scoped Classical in
/-- **Explicit ℓ²-contraction ratio** (UV-U1, brick S1′ corollary): in
dimension `d ≥ 3` (the physical `d = 4`), the averaging operator `Q`
contracts the bond ℓ²-norm by a factor of at least `1/L`,
`∑_bonds ‖Q A‖² ≤ L⁻¹ · ∑_bonds ‖A‖²`.  Since `L⁻¹ < 1` for `L ≥ 2`,
this is the clean geometric-contraction seed the per-scale RG decay
(`uv_geometric_summation`, UV plan U3) consumes.  From `linAvg_l2_le`
and `L^{2-d} ≤ L^{-1}` (i.e. `L³ ≤ L^d`). -/
theorem linAvg_l2_contraction (L N' : ℕ) [NeZero L] [NeZero N']
    (hd : 3 ≤ d) (A : ConcreteEdge d (L * N') → V) :
    ∑ y' : FinBox d N', ∑ μ : Fin d, ‖linAvg L N' A ⟨y', μ, true⟩‖ ^ 2
      ≤ (L : ℝ)⁻¹
        * ∑ z : FinBox d (L * N'), ∑ μ : Fin d, ‖A ⟨z, μ, true⟩‖ ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hLpos : (0 : ℝ) < L := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLne : (L : ℝ) ≠ 0 := hLpos.ne'
  have hconst : ((L : ℝ) ^ d)⁻¹ * (L : ℝ) ^ 2 ≤ (L : ℝ)⁻¹ := by
    have heq : ((L : ℝ) ^ 3)⁻¹ * (L : ℝ) ^ 2 = (L : ℝ)⁻¹ := by
      field_simp
    calc ((L : ℝ) ^ d)⁻¹ * (L : ℝ) ^ 2
        ≤ ((L : ℝ) ^ 3)⁻¹ * (L : ℝ) ^ 2 := by gcongr <;> assumption
      _ = (L : ℝ)⁻¹ := heq
  calc ∑ y' : FinBox d N', ∑ μ : Fin d, ‖linAvg L N' A ⟨y', μ, true⟩‖ ^ 2
      ≤ ((L : ℝ) ^ d)⁻¹ * (L : ℝ) ^ 2
          * ∑ z : FinBox d (L * N'), ∑ μ : Fin d, ‖A ⟨z, μ, true⟩‖ ^ 2 :=
        linAvg_l2_le L N' A
    _ ≤ (L : ℝ)⁻¹
          * ∑ z : FinBox d (L * N'), ∑ μ : Fin d, ‖A ⟨z, μ, true⟩‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hconst (by positivity)

end YangMills.RG
