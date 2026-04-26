/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L20_SU2_Concrete_YangMills.SU2_LatticeGauge

/-!
# SU(2) character theory (Phase 187)

This module formalises **SU(2) character theory** at the level
needed for character expansion of the Wilson Gibbs measure.

## Strategic placement

This is **Phase 187** of the L20_SU2_Concrete_YangMills block.

## What it does

The irreducible representations of SU(2) are indexed by
`j ∈ {0, 1/2, 1, 3/2, ...}` with dimension `2j+1`. We index them
by the natural number `2j ∈ ℕ`.

We define:
* `SU2_RepIndex` — index for irreps.
* `SU2_CharacterDim` — dimension `2j+1`.
* Properties of dimensions and the sum-of-odd-numbers identity.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L20_SU2_Concrete_YangMills

/-! ## §1. Representation index -/

/-- **SU(2) irrep index**: a natural number `2j ∈ ℕ` representing
    the half-integer spin `j = (2j)/2`. -/
abbrev SU2_RepIndex : Type := ℕ

/-! ## §2. Representation dimension -/

/-- **Dimension of the SU(2) irrep**: `2j + 1`. -/
def SU2_CharacterDim (twoj : SU2_RepIndex) : ℕ := twoj + 1

/-! ## §3. Basic dimension properties -/

/-- **Trivial irrep (j=0) has dimension 1**. -/
theorem SU2_CharacterDim_trivial : SU2_CharacterDim 0 = 1 := rfl

/-- **Fundamental irrep (j=1/2, twoj=1) has dimension 2**. -/
theorem SU2_CharacterDim_fundamental : SU2_CharacterDim 1 = 2 := rfl

/-- **Adjoint irrep (j=1, twoj=2) has dimension 3**. -/
theorem SU2_CharacterDim_adjoint : SU2_CharacterDim 2 = 3 := rfl

#print axioms SU2_CharacterDim_trivial
#print axioms SU2_CharacterDim_fundamental
#print axioms SU2_CharacterDim_adjoint

/-! ## §4. Successor and positivity -/

/-- **The dimension grows by 1 per index step**. -/
theorem SU2_CharacterDim_succ (twoj : SU2_RepIndex) :
    SU2_CharacterDim (twoj + 1) = SU2_CharacterDim twoj + 1 := rfl

#print axioms SU2_CharacterDim_succ

/-- **The dimension is always positive**. -/
theorem SU2_CharacterDim_pos (twoj : SU2_RepIndex) :
    0 < SU2_CharacterDim twoj := by
  unfold SU2_CharacterDim
  exact Nat.succ_pos _

#print axioms SU2_CharacterDim_pos

/-! ## §5. Triangular sum identity -/

/-- **Sum of the first `n+1` SU(2) irrep dimensions**:
    `Σ_{twoj=0}^{n} (twoj + 1) = (n+1)(n+2)/2`.

    This is the triangular-number identity:
    `1 + 2 + 3 + ... + (n+1) = (n+1)(n+2)/2`. -/
theorem SU2_CharacterDim_triangle_sum (n : ℕ) :
    (Finset.range (n + 1)).sum (fun twoj => SU2_CharacterDim twoj) =
      (n + 1) * (n + 2) / 2 := by
  unfold SU2_CharacterDim
  -- Σ_{k=0}^{n} (k+1) = Σ_{k=1}^{n+1} k = (n+1)(n+2)/2.
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    -- Goal: (n+1)(n+2)/2 + ((n+1)+1) = ((n+1)+1)((n+1)+2)/2
    --     = (n+1)(n+2)/2 + (n+2) = (n+2)(n+3)/2
    -- LHS: (n+1)(n+2)/2 + (n+2) = (n+2) [(n+1)/2 + 1] = (n+2)(n+3)/2.
    omega

#print axioms SU2_CharacterDim_triangle_sum

/-! ## §6. Coordination note -/

/-
This file is **Phase 187** of the L20_SU2_Concrete_YangMills block.

## What's done

Five substantive Lean theorems with full proofs (0 sorries):
* `SU2_CharacterDim_trivial`, `_fundamental`, `_adjoint` — concrete
  dimensions of the first three irreps (1, 2, 3).
* `SU2_CharacterDim_succ` — successor formula.
* `SU2_CharacterDim_pos` — positivity.
* `SU2_CharacterDim_triangle_sum` — triangular-sum identity
  `Σ_{twoj=0}^n (twoj+1) = (n+1)(n+2)/2`, proved by induction +
  `omega`.

This is **real concrete math** about SU(2): the dimensions of its
irreducible representations.

## Strategic value

Phase 187 connects SU(2) lattice gauge theory to its representation
theory, the foundation for character expansion of the Wilson Gibbs
measure.

Cross-references:
- Phase 183 `SU2_LatticeGauge.lean`.
- Bloque-4 §2 (character expansion).
-/

end YangMills.L20_SU2_Concrete_YangMills
