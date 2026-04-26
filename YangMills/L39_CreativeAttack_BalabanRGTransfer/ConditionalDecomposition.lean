/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Conditional decomposition (Phase 375)

The decomposition of the partition function into block-conditional
measures.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L39_CreativeAttack_BalabanRGTransfer

/-! ## §1. Block conditional structure -/

/-- **Block-conditional measure data**: a family of conditional
    distributions on each block, plus a marginal on block boundaries. -/
structure BlockConditional where
  /-- Number of blocks. -/
  numBlocks : ℕ
  /-- The conditional LSI constant per block. -/
  c_per_block : ℝ
  /-- The constant is positive. -/
  c_per_block_pos : 0 < c_per_block

/-! ## §2. Tensor product structure -/

/-- **Tensor product LSI constant**: for independent blocks,
    `c_total = c_per_block` (no degradation under tensorisation). -/
def tensorLSIConstant (BC : BlockConditional) : ℝ := BC.c_per_block

theorem tensorLSIConstant_pos (BC : BlockConditional) :
    0 < tensorLSIConstant BC := BC.c_per_block_pos

#print axioms tensorLSIConstant_pos

/-! ## §3. Coupled-block bound -/

/-- **Coupled-block LSI constant**: with coupling, the constant is
    multiplied by the number of blocks (worst case). -/
def coupledLSIConstant (BC : BlockConditional) : ℝ :=
  (BC.numBlocks : ℝ) * BC.c_per_block

theorem coupledLSIConstant_nonneg (BC : BlockConditional) :
    0 ≤ coupledLSIConstant BC := by
  unfold coupledLSIConstant
  exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt BC.c_per_block_pos)

end YangMills.L39_CreativeAttack_BalabanRGTransfer
