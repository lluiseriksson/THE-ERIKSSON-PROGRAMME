/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalShellLocalityDiv

/-!
# Concrete locality of the block-constraint term `Q†Q`
(`hRpoly` campaign — P4-CT, owner obligation 2, third and last shell term)

The long stencil: `Q = flatBlockConstraintQCLM L N'` averages fine bonds
over block lines of length `L` (`linAvg`/`fineLineSum`).  For the bond probe
`δ_p v`:

* the probe image at a coarse bond `(c, μ)` is nonzero only if `μ = p.2` and
  `p.1 = shift^[k] x` for some `x` in block `c` and `k < L`; two such fine
  bonds for a common coarse bond lie within Chebyshev distance
  `(L−1) + (L−1) + (L−1) ≤ 3L` (line reach + block diameter + line reach),
  giving Gram orthogonality beyond `3L`;
* summing the sampling indicators over ALL coarse bonds uses that blocks
  PARTITION the fine lattice, and each of the `L` line offsets has exactly
  one preimage (`shift^[k]` is bijective), so `‖Q δ_p v‖ ≤ L^{1−d}‖v‖ ≤ L‖v‖`
  — no block-counting needed for the norm.

Endpoints through the Addendum-263 Gram calculus, then the FULL free-shell
assembly:

* `blockQ_adjointCompSelf_finiteRange` — `FiniteRange (Q†Q) physicalBondDist (3L)`;
* `blockQ_adjointCompSelf_kernelBound` — `KernelBound (Q†Q) (fun _ _ => L²)`;
* `flatBasePrecision_finiteRange` / `flatBasePrecision_kernelBound` — the
  base precision `K₀ + a·Q†Q` at range `3L` and bound `(4d)² + 4 + |a|·L²`
  (owner obligation 2 COMPLETE);
* `flatGaugeFixedPrecisionCLM_zeroSigma_eq_base` — the free shell
  `Sigma := (Empty elim)` IS the base precision (owner obligation 3,
  named `zeroSigma` as required: the empty-family tsum vanishes
  definitionally, no norm-as-locality anywhere).

**Honest scope.**  Obligations 2–3.  Remaining: CT3, CT4 at `r := source`,
the positive-`θ` witness, and the `CT_fixedVolume` endpoint on
`flatGaugeFixedCovarianceCLM`.  Constants crude by design.  Not `hRpoly`,
not mass gap, not Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

variable {d L N' Nc : ℕ} [NeZero L] [NeZero N']

/-! ## Geometry: iterated shifts, value windows, block diameter -/

/-- Torus distance is bounded by the truncated value difference (either
orientation). -/
theorem finTorusDist_le_val_sub {N : ℕ} [NeZero N] (a b : Fin N)
    (h : b.val ≤ a.val) :
    finTorusDist a b ≤ a.val - b.val := by
  unfold finTorusDist zmodCircDist
  have hcast : ((a.val : ℕ) : ZMod N) - ((b.val : ℕ) : ZMod N)
      = (((a.val - b.val : ℕ)) : ZMod N) := by
    rw [Nat.cast_sub h]
  rw [hcast]
  calc zmodCircVal (((a.val - b.val : ℕ)) : ZMod N)
      ≤ (((a.val - b.val : ℕ)) : ZMod N).val := zmodCircVal_le_val _
    _ = (a.val - b.val) % N := ZMod.val_natCast N _
    _ ≤ a.val - b.val := Nat.mod_le _ _

/-- Torus distance from a symmetric value window. -/
theorem finTorusDist_le_of_window {N : ℕ} [NeZero N] (a b : Fin N) (W : ℕ)
    (h1 : a.val ≤ b.val + W) (h2 : b.val ≤ a.val + W) :
    finTorusDist a b ≤ W := by
  rcases le_total b.val a.val with h | h
  · calc finTorusDist a b ≤ a.val - b.val := finTorusDist_le_val_sub a b h
      _ ≤ W := by omega
  · calc finTorusDist a b = finTorusDist b a := finTorusDist_comm a b
      _ ≤ b.val - a.val := finTorusDist_le_val_sub b a h
      _ ≤ W := by omega

/-- Two sites of the same block lie within Chebyshev distance `L − 1`. -/
theorem finBoxDist_le_of_same_block (x x' : FinBox d (L * N'))
    (hb : blockSite L N' x = blockSite L N' x') :
    finBoxDist x x' ≤ L - 1 := by
  unfold finBoxDist
  apply Finset.sup_le
  intro i _
  have hq : (x i).val / L = (x' i).val / L := by
    have := congrFun hb i
    have h1 : (blockSite L N' x i).val = (blockSite L N' x' i).val := by
      rw [this]
    simpa using h1
  have hL : 0 < L := NeZero.pos L
  have h1 : (x i).val = L * ((x i).val / L) + (x i).val % L :=
    (Nat.div_add_mod _ _).symm
  have h2 : (x' i).val = L * ((x' i).val / L) + (x' i).val % L :=
    (Nat.div_add_mod _ _).symm
  have hmx : (x i).val % L < L := Nat.mod_lt _ hL
  have hmx' : (x' i).val % L < L := Nat.mod_lt _ hL
  rw [hq] at h1
  set r1 := (x i).val % L with hr1
  set r2 := (x' i).val % L with hr2
  set Q := (x' i).val / L with hQdef
  have key : (x i).val + r2 = (x' i).val + r1 := by
    rw [h1, h2]
    ring
  apply finTorusDist_le_of_window
  · omega
  · omega

/-- Iterated shifts move a site by at most the iteration count. -/
theorem finBoxDist_iterate_shift_le {N : ℕ} [NeZero N]
    (x : FinBox d N) (j : Fin d) (k : ℕ) :
    finBoxDist x ((fun z => FinBox.shift z j)^[k] x) ≤ k := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, finBoxDist_self]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc finBoxDist x (FinBox.shift ((fun z => FinBox.shift z j)^[n] x) j)
        ≤ finBoxDist x ((fun z => FinBox.shift z j)^[n] x) +
          finBoxDist ((fun z => FinBox.shift z j)^[n] x)
            (FinBox.shift ((fun z => FinBox.shift z j)^[n] x) j) :=
          finBoxDist_triangle _ _ _
      _ ≤ n + 1 := Nat.add_le_add ih (finBoxDist_shift_le _ j)

/-- Two line samples over a common block lie within Chebyshev distance
`3L`. -/
theorem sample_sites_dist_le (x₁ x₂ : FinBox d (L * N')) (j : Fin d)
    (k₁ k₂ : ℕ) (hk₁ : k₁ < L) (hk₂ : k₂ < L)
    (hb : blockSite L N' x₁ = blockSite L N' x₂) :
    finBoxDist ((fun z => FinBox.shift z j)^[k₁] x₁)
      ((fun z => FinBox.shift z j)^[k₂] x₂) ≤ 3 * L := by
  have h1 : finBoxDist ((fun z => FinBox.shift z j)^[k₁] x₁) x₁ ≤ k₁ := by
    rw [finBoxDist_comm]
    exact finBoxDist_iterate_shift_le x₁ j k₁
  have h2 : finBoxDist x₁ x₂ ≤ L - 1 := finBoxDist_le_of_same_block x₁ x₂ hb
  have h3 : finBoxDist x₂ ((fun z => FinBox.shift z j)^[k₂] x₂) ≤ k₂ :=
    finBoxDist_iterate_shift_le x₂ j k₂
  calc finBoxDist ((fun z => FinBox.shift z j)^[k₁] x₁)
        ((fun z => FinBox.shift z j)^[k₂] x₂)
      ≤ finBoxDist ((fun z => FinBox.shift z j)^[k₁] x₁) x₁ +
        finBoxDist x₁ ((fun z => FinBox.shift z j)^[k₂] x₂) :=
        finBoxDist_triangle _ _ _
    _ ≤ finBoxDist ((fun z => FinBox.shift z j)^[k₁] x₁) x₁ +
        (finBoxDist x₁ x₂ +
          finBoxDist x₂ ((fun z => FinBox.shift z j)^[k₂] x₂)) :=
        Nat.add_le_add_left (finBoxDist_triangle _ _ _) _
    _ ≤ k₁ + ((L - 1) + k₂) := by
        apply Nat.add_le_add h1
        exact Nat.add_le_add h2 h3
    _ ≤ 3 * L := by omega

section BlockQ

variable [NeZero d] [NeZero Nc]

/-! ## The probe image of the block constraint -/

/-- The block-constraint image of a single-bond probe, sample by sample. -/
theorem flatBlockConstraint_single_apply
    (p : PhysicalBond d (L * N')) (v : SUNLieCoord Nc)
    (b : PhysicalBond d N') :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v) b =
      ((L : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
          (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
              PhysicalBond d (L * N')) = p then v else 0) := by
  rw [flatBlockConstraintQCLM_apply]
  unfold linAvg fineLineSum
  rfl

/-- If no line sample of the coarse bond `b` equals `p`, the probe image
vanishes at `b`. -/
theorem flatBlockConstraint_single_eq_zero
    (p : PhysicalBond d (L * N')) (v : SUNLieCoord Nc)
    (b : PhysicalBond d N')
    (h : ∀ x ∈ blockOf L N' b.1, ∀ k ∈ Finset.range L,
      (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
        PhysicalBond d (L * N')) ≠ p) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v) b
      = 0 := by
  rw [flatBlockConstraint_single_apply]
  have hz : ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
      (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
          PhysicalBond d (L * N')) = p then v else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg (h x hx k hk)]
  rw [hz, smul_zero]

/-- **Gram orthogonality for the block constraint**: probes at bond distance
`> 3L` have orthogonal images. -/
theorem flatBlockConstraint_gram_orthogonal
    (p q : PhysicalBond d (L * N')) (v w : SUNLieCoord Nc)
    (hfar : 3 * L < physicalBondDist q p) :
    inner ℝ (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v))
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) q w)) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hp : ∀ x ∈ blockOf L N' b.1, ∀ k ∈ Finset.range L,
      (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
        PhysicalBond d (L * N')) ≠ p
  · rw [flatBlockConstraint_single_eq_zero p v b hp, inner_zero_left]
  · by_cases hq : ∀ x ∈ blockOf L N' b.1, ∀ k ∈ Finset.range L,
        (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
          PhysicalBond d (L * N')) ≠ q
    · rw [flatBlockConstraint_single_eq_zero q w b hq, inner_zero_right]
    · exfalso
      push_neg at hp hq
      obtain ⟨x₁, hx₁, k₁, hk₁, hpe⟩ := hp
      obtain ⟨x₂, hx₂, k₂, hk₂, hqe⟩ := hq
      have hb₁ : blockSite L N' x₁ = b.1 := by
        have := hx₁
        rw [mem_blockOf] at this
        exact this
      have hb₂ : blockSite L N' x₂ = b.1 := by
        have := hx₂
        rw [mem_blockOf] at this
        exact this
      have hsites : finBoxDist ((fun z => FinBox.shift z b.2)^[k₂] x₂)
          ((fun z => FinBox.shift z b.2)^[k₁] x₁) ≤ 3 * L := by
        rw [finBoxDist_comm]
        exact sample_sites_dist_le x₁ x₂ b.2 k₁ k₂
          (Finset.mem_range.mp hk₁) (Finset.mem_range.mp hk₂)
          (hb₁.trans hb₂.symm)
      have hd : physicalBondDist q p ≤ 3 * L := by
        rw [← hpe, ← hqe]
        apply max_le
        · exact hsites
        · calc (if ((((fun z => FinBox.shift z b.2)^[k₂] x₂, b.2) :
                PhysicalBond d (L * N')).2 =
                (((fun z => FinBox.shift z b.2)^[k₁] x₁, b.2) :
                PhysicalBond d (L * N')).2) then 0 else 1)
              = 0 := by rw [if_pos rfl]
            _ ≤ 3 * L := Nat.zero_le _
      omega

/-! ## Probe-image norm bound -/

/-- Blocks partition the fine lattice: summing a function over all blocks
equals summing it over all fine sites. -/
theorem sum_blocks_eq_sum_sites (F : FinBox d (L * N') → ℝ) :
    ∑ c : FinBox d N', ∑ x ∈ blockOf L N' c, F x
      = ∑ x : FinBox d (L * N'), F x := by
  classical
  calc ∑ c : FinBox d N', ∑ x ∈ blockOf L N' c, F x
      = ∑ c : FinBox d N', ∑ x : FinBox d (L * N'),
          (if blockSite L N' x = c then F x else 0) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [← Finset.sum_filter]
        rfl
    _ = ∑ x : FinBox d (L * N'), ∑ c : FinBox d N',
          (if blockSite L N' x = c then F x else 0) := Finset.sum_comm
    _ = ∑ x : FinBox d (L * N'), F x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_ite_eq Finset.univ (blockSite L N' x)]
        rw [if_pos (Finset.mem_univ _)]

/-- **Probe-image norm bound for the block constraint**:
`‖Q δ_p v‖ ≤ L·‖v‖` (block partition + bijectivity of the line shifts; the
`L^{-d}` normalization is dropped crudely as `≤ 1`). -/
theorem flatBlockConstraint_single_norm_le
    (p : PhysicalBond d (L * N')) (v : SUNLieCoord Nc) :
    ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v)‖ ≤
      (L : ℝ) * ‖v‖ := by
  classical
  have hLpos : (0:ℝ) < (L : ℝ) ^ d := by
    have : (0:ℝ) < (L : ℝ) := by exact_mod_cast NeZero.pos L
    positivity
  have hinv_le_one : ((L : ℝ) ^ d)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    have hL1 : (1:ℝ) ≤ (L : ℝ) := by exact_mod_cast NeZero.one_le
    calc (1:ℝ) = 1 ^ d := (one_pow d).symm
      _ ≤ (L : ℝ) ^ d := by
          apply pow_le_pow_left₀ (by norm_num) hL1
  -- per-bond bound
  have hbond : ∀ b : PhysicalBond d N',
      ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
          (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v) b‖
        ≤ ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then ‖v‖ else 0) := by
    intro b
    rw [flatBlockConstraint_single_apply, norm_smul]
    have habs : ‖((L : ℝ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [habs]
    calc ((L : ℝ) ^ d)⁻¹ *
          ‖∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then v else 0)‖
        ≤ 1 * ‖∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then v else 0)‖ := by
          apply mul_le_mul_of_nonneg_right hinv_le_one (norm_nonneg _)
      _ = ‖∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then v else 0)‖ := one_mul _
      _ ≤ ∑ x ∈ blockOf L N' b.1, ‖∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then v else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            ‖(if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then v else 0)‖ :=
          Finset.sum_le_sum (fun x _ => norm_sum_le _ _)
      _ = ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then ‖v‖ else 0) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          refine Finset.sum_congr rfl (fun k _ => ?_)
          by_cases h : (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
              PhysicalBond d (L * N')) = p
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, norm_zero]
  -- assemble over all coarse bonds
  calc ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v)‖
      ≤ ∑ b : PhysicalBond d N',
          ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
            (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v) b‖ :=
        piLp_norm_le_sum_norm _
    _ ≤ ∑ b : PhysicalBond d N',
          ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then ‖v‖ else 0) :=
        Finset.sum_le_sum (fun b _ => hbond b)
    _ = ∑ c : FinBox d N', ∑ μ : Fin d,
          ∑ x ∈ blockOf L N' c, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
                PhysicalBond d (L * N')) = p then ‖v‖ else 0) :=
        Fintype.sum_prod_type _
    _ = ∑ μ : Fin d, ∑ c : FinBox d N',
          ∑ x ∈ blockOf L N' c, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
                PhysicalBond d (L * N')) = p then ‖v‖ else 0) :=
        Finset.sum_comm
    _ = ∑ μ : Fin d, ∑ k ∈ Finset.range L, ∑ x : FinBox d (L * N'),
          (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
              PhysicalBond d (L * N')) = p then ‖v‖ else 0) := by
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        rw [sum_blocks_eq_sum_sites
          (F := fun x => ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
                PhysicalBond d (L * N')) = p then ‖v‖ else 0))]
        exact Finset.sum_comm
    _ ≤ ∑ μ : Fin d, ∑ k ∈ Finset.range L,
          (if μ = p.2 then ‖v‖ else 0) := by
        refine Finset.sum_le_sum (fun μ _ => ?_)
        refine Finset.sum_le_sum (fun k _ => ?_)
        by_cases hμ : μ = p.2
        · rw [if_pos hμ]
          have hbij : Function.Bijective
              (fun x : FinBox d (L * N') => (fun z => FinBox.shift z μ)^[k] x) :=
            Function.Bijective.iterate (FinBox.shift_bijective μ) k
          calc ∑ x : FinBox d (L * N'),
                (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
                    PhysicalBond d (L * N')) = p then ‖v‖ else 0)
              ≤ ∑ x : FinBox d (L * N'),
                (if (fun z => FinBox.shift z μ)^[k] x = p.1 then ‖v‖ else 0) := by
                refine Finset.sum_le_sum (fun x _ => ?_)
                by_cases h : (((fun z => FinBox.shift z μ)^[k] x, μ) :
                    PhysicalBond d (L * N')) = p
                · rw [if_pos h, if_pos (congrArg Prod.fst h)]
                · by_cases h2 : (fun z => FinBox.shift z μ)^[k] x = p.1
                  · rw [if_neg h, if_pos h2]
                    exact norm_nonneg v
                  · rw [if_neg h, if_neg h2]
            _ = ∑ y : FinBox d (L * N'), (if y = p.1 then ‖v‖ else 0) :=
                hbij.sum_comp (fun y => if y = p.1 then ‖v‖ else 0)
            _ = ‖v‖ := by
                rw [Finset.sum_ite_eq' Finset.univ p.1]
                rw [if_pos (Finset.mem_univ _)]
        · rw [if_neg hμ]
          apply le_of_eq
          apply Finset.sum_eq_zero
          intro x _
          rw [if_neg]
          intro h
          exact hμ (congrArg Prod.snd h)
    _ = (L : ℝ) * ‖v‖ := by
        rw [Finset.sum_comm]
        have hinner : ∀ k ∈ Finset.range L,
            ∑ μ : Fin d, (if μ = p.2 then ‖v‖ else 0) = ‖v‖ := by
          intro k _
          rw [Finset.sum_ite_eq' Finset.univ p.2]
          rw [if_pos (Finset.mem_univ _)]
        rw [Finset.sum_congr rfl hinner]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Gram-package endpoints and the full free-shell assembly -/

/-- **Concrete finite range of the block-constraint term**:
`Q†Q` has kernel range `3L` in `physicalBondDist`. -/
theorem blockQ_adjointCompSelf_finiteRange :
    PhysicalCovarianceFiniteRange
      ((flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').adjoint.comp
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'))
      physicalBondDist (3 * L) :=
  adjointCompSelf_finiteRange _ physicalBondDist
    (fun p q v w hR => flatBlockConstraint_gram_orthogonal p q v w hR)

/-- **Concrete kernel bound of the block-constraint term**:
`Q†Q` has entrywise block bound `L²`. -/
theorem blockQ_adjointCompSelf_kernelBound :
    PhysicalCovarianceKernelBound
      ((flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').adjoint.comp
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'))
      (fun _ _ => (L : ℝ) ^ 2) :=
  adjointCompSelf_kernelBound _
    (fun p v => flatBlockConstraint_single_norm_le p v)

/-- The base precision IS `K₀ + a·Q†Q`, definitionally. -/
theorem gaugeFixedBasePrecision_flat_eq (ρ : SUNAdjointModel Nc) (a : ℝ) :
    gaugeFixedBasePrecisionCLM
        (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a
      = flatGaugeHodgeK0CLM d (L * N') Nc ρ
        + a • ((flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').adjoint.comp
            (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')) := rfl

/-- **Owner obligation 2, COMPLETE — finite range of the full base
precision**: `K₀ + a·Q†Q` has kernel range `3L` in `physicalBondDist`
(the `K₀` range 2 is lifted to the common range by monotonicity;
`2 ≤ 3L` since `L ≥ 1`). -/
theorem flatBasePrecision_finiteRange (ρ : SUNAdjointModel Nc) (a : ℝ) :
    PhysicalCovarianceFiniteRange
      (gaugeFixedBasePrecisionCLM
        (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a)
      physicalBondDist (3 * L) := by
  rw [gaugeFixedBasePrecision_flat_eq]
  apply physicalCovarianceFiniteRange_add physicalBondDist
  · apply physicalCovarianceFiniteRange_mono physicalBondDist
      (show 2 ≤ 3 * L by have := NeZero.one_le (n := L); omega)
    exact flatGaugeHodgeK0_finiteRange ρ
  · exact physicalCovarianceFiniteRange_smul physicalBondDist a
      blockQ_adjointCompSelf_finiteRange

/-- **Owner obligation 2, COMPLETE — kernel bound of the full base
precision**: `K₀ + a·Q†Q` has entrywise block bound `(4d)² + 4 + |a|·L²`. -/
theorem flatBasePrecision_kernelBound (ρ : SUNAdjointModel Nc) (a : ℝ) :
    PhysicalCovarianceKernelBound
      (gaugeFixedBasePrecisionCLM
        (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a)
      (fun _ _ => (((4 * d : ℕ) : ℝ) ^ 2 + (2 : ℝ) ^ 2) + |a| * (L : ℝ) ^ 2) := by
  rw [gaugeFixedBasePrecision_flat_eq]
  exact physicalCovarianceKernelBound_add
    (flatGaugeHodgeK0_kernelBound ρ)
    (physicalCovarianceKernelBound_smul a blockQ_adjointCompSelf_kernelBound)

/-- **Owner obligation 3 — the free shell, named**: with the EMPTY `Sigma`
family (`zeroSigma`), the flat gauge-fixed precision IS the base precision:
the empty tsum vanishes and nothing is hidden in a norm hypothesis. -/
theorem flatGaugeFixedPrecisionCLM_zeroSigma_eq_base
    [NeZero (L * N')] (ρ : SUNAdjointModel Nc) (a : ℝ) :
    flatGaugeFixedPrecisionCLM d L N' Nc ρ a
        (fun i : Empty => i.elim)
      = gaugeFixedBasePrecisionCLM
          (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
          (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a := by
  unfold flatGaugeFixedPrecisionCLM gaugeFixedPrecisionCLM
  rw [tsum_empty, sub_zero]

end BlockQ

end YangMills.RG
