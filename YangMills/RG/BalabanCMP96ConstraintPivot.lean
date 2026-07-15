/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BlockMaps
import YangMills.RG.PhysicalShellLocalityQ

/-!
# The distinguished constraint bond `b₀(c)`

Bałaban's constrained fluctuation coordinates remove one fine bond `b₀(c)`
for every coarse positive bond `c`.  The removed bond is the last positive
bond in the straight length-`L` corridor based at the lower corner of the
source block.  This choice is important: every path in the source-block
average ending at this bond stays in the same block.

This module fixes that bond literally and proves the elementary geometry
needed by the forthcoming right inverse of the flat block constraint.  It
does not yet construct the elimination operator `C`.

**Source.** T. Bałaban, *Propagators and Renormalization Transformations for
Lattice Gauge Theories. II*, Commun. Math. Phys. **99** (1985), the
constraint-coordinate construction surrounding the definition
`B = C \widetilde B` and the distinguished bond `b₀(c)`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

set_option maxHeartbeats 2000000

variable {d L N' : ℕ} [NeZero L] [NeZero N']

/-- Source of the distinguished fine bond for a coarse positive bond: the
lower block corner advanced `L-1` steps in the coarse-bond direction. -/
def cmp96ConstraintPivotSource (c : PhysicalBond d N') :
    FinBox d (L * N') :=
  (fun x => FinBox.shift x c.2)^[L - 1] (blockBasepoint L N' c.1)

/-- The distinguished positive fine bond `b₀(c)`. -/
def cmp96ConstraintPivotBond (c : PhysicalBond d N') :
    PhysicalBond d (L * N') :=
  (cmp96ConstraintPivotSource c, c.2)

/-- The start of the length-`k` terminal segment ending at `b₀(c)`. -/
def cmp96ConstraintPivotPredecessor (c : PhysicalBond d N') (k : ℕ) :
    FinBox d (L * N') :=
  (fun x => FinBox.shift x c.2)^[L - 1 - k] (blockBasepoint L N' c.1)

/-- The distinguished source remains in the source block of the coarse bond. -/
theorem blockSite_cmp96ConstraintPivotSource (c : PhysicalBond d N') :
    blockSite L N' (cmp96ConstraintPivotSource c) = c.1 := by
  rw [blockSite_eq_iff_cube]
  intro i
  by_cases hi : i = c.2
  · subst i
    rw [cmp96ConstraintPivotSource, iterShift_apply_self]
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    have hy : (c.1 c.2).val + 1 ≤ N' := Nat.succ_le_iff.mpr (c.1 c.2).isLt
    have htop : L * ((c.1 c.2).val + 1) ≤ L * N' :=
      Nat.mul_le_mul_left L hy
    have hval :
        (L * (c.1 c.2).val + (L - 1)) % (L * N') =
          L * (c.1 c.2).val + (L - 1) := by
      apply Nat.mod_eq_of_lt
      calc
        L * (c.1 c.2).val + (L - 1) <
            L * (c.1 c.2).val + L := by omega
        _ = L * ((c.1 c.2).val + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ ≤ L * N' := htop
    rw [blockBasepoint, hval]
    omega
  · rw [cmp96ConstraintPivotSource, iterShift_apply_ne _ _ _ hi]
    change L * (c.1 i).val ≤ L * (c.1 i).val ∧
      L * (c.1 i).val < L * (c.1 i).val + L
    exact ⟨le_rfl, Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero (NeZero.ne L))⟩

/-- Every terminal-segment predecessor with `k < L` lies in the same source
block. -/
theorem blockSite_cmp96ConstraintPivotPredecessor (c : PhysicalBond d N')
    {k : ℕ} (hk : k < L) :
    blockSite L N' (cmp96ConstraintPivotPredecessor c k) = c.1 := by
  rw [blockSite_eq_iff_cube]
  intro i
  by_cases hi : i = c.2
  · subst i
    rw [cmp96ConstraintPivotPredecessor, iterShift_apply_self]
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    have hy : (c.1 c.2).val + 1 ≤ N' := Nat.succ_le_iff.mpr (c.1 c.2).isLt
    have htop : L * ((c.1 c.2).val + 1) ≤ L * N' :=
      Nat.mul_le_mul_left L hy
    have hval :
        (L * (c.1 c.2).val + (L - 1 - k)) % (L * N') =
          L * (c.1 c.2).val + (L - 1 - k) := by
      apply Nat.mod_eq_of_lt
      calc
        L * (c.1 c.2).val + (L - 1 - k) <
            L * (c.1 c.2).val + L := by omega
        _ = L * ((c.1 c.2).val + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ ≤ L * N' := htop
    rw [blockBasepoint, hval]
    omega
  · rw [cmp96ConstraintPivotPredecessor, iterShift_apply_ne _ _ _ hi]
    change L * (c.1 i).val ≤ L * (c.1 i).val ∧
      L * (c.1 i).val < L * (c.1 i).val + L
    exact ⟨le_rfl, Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero (NeZero.ne L))⟩

/-- Advancing the predecessor by `k < L` steps reaches the distinguished
source exactly. -/
theorem iterShift_cmp96ConstraintPivotPredecessor (c : PhysicalBond d N')
    {k : ℕ} (hk : k < L) :
    (fun x => FinBox.shift x c.2)^[k]
        (cmp96ConstraintPivotPredecessor
          (d := d) (L := L) (N' := N') c k) =
      cmp96ConstraintPivotSource (d := d) (L := L) (N' := N') c := by
  rw [cmp96ConstraintPivotPredecessor, cmp96ConstraintPivotSource]
  rw [← Function.iterate_add_apply
    (fun x : FinBox d (L * N') => FinBox.shift x c.2) k (L - 1 - k)]
  congr 2
  omega

/-- Distinct coarse positive bonds have distinct distinguished fine bonds. -/
theorem cmp96ConstraintPivotBond_injective :
    Function.Injective
      (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N')) := by
  intro c b h
  have hdir : c.2 = b.2 := by
    simpa [cmp96ConstraintPivotBond] using
      congrArg (fun p : PhysicalBond d (L * N') => p.2) h
  have hsrc :
      cmp96ConstraintPivotSource (d := d) (L := L) (N' := N') c =
        cmp96ConstraintPivotSource (d := d) (L := L) (N' := N') b :=
    by
      simpa [cmp96ConstraintPivotBond] using
        congrArg (fun p : PhysicalBond d (L * N') => p.1) h
  apply Prod.ext
  · rw [← blockSite_cmp96ConstraintPivotSource (L := L) c,
      ← blockSite_cmp96ConstraintPivotSource (L := L) b, hsrc]
  · exact hdir

/-- Exact recognition of a sample hitting `b₀(c)`: the coarse bond is `c`
and the starting site is the unique terminal-segment predecessor. -/
theorem cmp96ConstraintSample_eq_pivot_iff
    (b c : PhysicalBond d N') (x : FinBox d (L * N')) {k : ℕ}
    (hk : k < L) (hx : blockSite L N' x = b.1) :
    (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
        PhysicalBond d (L * N')) = cmp96ConstraintPivotBond c ↔
      b = c ∧ x = cmp96ConstraintPivotPredecessor c k := by
  constructor
  · intro hsample
    have hdir : b.2 = c.2 := by
      simpa [cmp96ConstraintPivotBond] using
        congrArg (fun p : PhysicalBond d (L * N') => p.2) hsample
    have hshift :
        (fun z => FinBox.shift z c.2)^[k] x =
          cmp96ConstraintPivotSource (d := d) (L := L) (N' := N') c := by
      simpa [cmp96ConstraintPivotBond, hdir] using
        congrArg (fun p : PhysicalBond d (L * N') => p.1) hsample
    have hxpred :
        x = cmp96ConstraintPivotPredecessor
          (d := d) (L := L) (N' := N') c k := by
      apply (iterShift_bijective (d := d) (L * N') c.2 k).1
      rw [hshift]
      exact (iterShift_cmp96ConstraintPivotPredecessor (L := L) c hk).symm
    have hsource : b.1 = c.1 := by
      rw [← hx, hxpred, blockSite_cmp96ConstraintPivotPredecessor (L := L) c hk]
    exact ⟨Prod.ext hsource hdir, hxpred⟩
  · rintro ⟨hbc, hxpred⟩
    subst b
    subst x
    apply Prod.ext
    · exact iterShift_cmp96ConstraintPivotPredecessor (L := L) c hk
    · rfl

/-- At a fixed path position `k < L`, exactly one starting site in the source
block reaches the distinguished bond. -/
theorem sum_block_probe_pivot
    {Nc : ℕ} [NeZero Nc] (c : PhysicalBond d N') (v : SUNLieCoord Nc)
    {k : ℕ} (hk : k < L) :
    (∑ x ∈ blockOf L N' c.1,
      (if (((fun z => FinBox.shift z c.2)^[k] x, c.2) :
          PhysicalBond d (L * N')) = cmp96ConstraintPivotBond c
        then v else 0)) = v := by
  classical
  rw [Finset.sum_eq_single
    (cmp96ConstraintPivotPredecessor
      (d := d) (L := L) (N' := N') c k)]
  · rw [if_pos]
    exact (cmp96ConstraintSample_eq_pivot_iff c c _ hk
      (blockSite_cmp96ConstraintPivotPredecessor (L := L) c hk)).mpr
        ⟨rfl, rfl⟩
  · intro x hx hxne
    rw [if_neg]
    intro heq
    exact hxne ((cmp96ConstraintSample_eq_pivot_iff c c x hk
      ((mem_blockOf L N' c.1 x).mp hx)).mp heq).2
  · intro hnot
    exact False.elim (hnot ((mem_blockOf L N' c.1 _).mpr
      (blockSite_cmp96ConstraintPivotPredecessor (L := L) c hk)))

/-- A nonmatching coarse row has no path sample equal to `b₀(c)`. -/
theorem sum_block_probe_pivot_eq_zero_of_ne
    {Nc : ℕ} [NeZero Nc] (b c : PhysicalBond d N') (hbc : b ≠ c)
    (v : SUNLieCoord Nc) :
    (∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
      (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
          PhysicalBond d (L * N')) = cmp96ConstraintPivotBond c
        then v else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg]
  intro heq
  have hmatch := (cmp96ConstraintSample_eq_pivot_iff b c x
    (Finset.mem_range.mp hk) ((mem_blockOf L N' b.1 x).mp hx)).mp heq
  exact hbc hmatch.1

/-- The block constraint sees its distinguished single-bond probe only in
the matching coarse row, with exactly the `L` path multiplicity dictated by
the source-block average. -/
theorem flatBlockConstraint_pivot_probe_apply
    {Nc : ℕ} [NeZero d] [NeZero Nc]
    (c b : PhysicalBond d N') (v : SUNLieCoord Nc) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c) v) b =
      if b = c then
        ((L : ℝ) ^ d)⁻¹ • ((L : ℝ) • v)
      else 0 := by
  rw [flatBlockConstraint_single_apply]
  by_cases hbc : b = c
  · subst b
    rw [if_pos rfl]
    congr 1
    rw [Finset.sum_comm]
    calc
      (∑ k ∈ Finset.range L, ∑ x ∈ blockOf L N' c.1,
          (if (((fun z => FinBox.shift z c.2)^[k] x, c.2) :
              PhysicalBond d (L * N')) = cmp96ConstraintPivotBond c
            then v else 0)) = ∑ _k ∈ Finset.range L, v := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkL := Finset.mem_range.mp hk
        exact sum_block_probe_pivot c v hkL
      _ = (L : ℝ) • v := by
        rw [Finset.sum_const, Finset.card_range]
        exact (Nat.cast_smul_eq_nsmul ℝ L v).symm
  · rw [if_neg hbc]
    have hzero := sum_block_probe_pivot_eq_zero_of_ne
      (d := d) (L := L) (N' := N') (Nc := Nc) b c hbc v
    rw [hzero, smul_zero]

end YangMills.RG
