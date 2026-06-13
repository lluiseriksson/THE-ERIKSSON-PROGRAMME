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

end YangMills.RG
