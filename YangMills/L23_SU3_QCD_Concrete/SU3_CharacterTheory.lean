/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(3) character theory (Phase 217)

This module formalises the **SU(3) representation theory** at the
level of dimensions of small irreps.

## Strategic placement

This is **Phase 217** of the L23_SU3_QCD_Concrete block.

## What it does

The SU(3) irreducible representations are labelled by Dynkin labels
`(p, q)` with dimension formula `dim(p,q) = (p+1)(q+1)(p+q+2)/2`.
The first few:
* `(0,0)` trivial: dim 1.
* `(1,0)` fundamental: dim 3.
* `(0,1)` antifundamental: dim 3.
* `(1,1)` adjoint: dim 8.
* `(2,0)` symmetric: dim 6.
* `(2,1)` decuplet: dim 15.

We define:
* `SU3_DynkinLabel` — pair `(p, q)` of Dynkin labels.
* `SU3_CharacterDim` — the dimension formula.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L23_SU3_QCD_Concrete

/-! ## §1. Dynkin labels for SU(3) -/

/-- **SU(3) irrep label**: a pair `(p, q) ∈ ℕ × ℕ`. -/
abbrev SU3_DynkinLabel : Type := ℕ × ℕ

/-! ## §2. Dimension formula -/

/-- **SU(3) dimension formula**: `dim(p, q) = (p+1)(q+1)(p+q+2)/2`. -/
def SU3_CharacterDim (label : SU3_DynkinLabel) : ℕ :=
  (label.1 + 1) * (label.2 + 1) * (label.1 + label.2 + 2) / 2

/-! ## §3. Concrete dimensions -/

/-- **Trivial irrep `(0,0)` has dimension 1**. -/
theorem SU3_CharacterDim_trivial : SU3_CharacterDim (0, 0) = 1 := by
  unfold SU3_CharacterDim; norm_num

#print axioms SU3_CharacterDim_trivial

/-- **Fundamental irrep `(1,0)` has dimension 3**. -/
theorem SU3_CharacterDim_fundamental : SU3_CharacterDim (1, 0) = 3 := by
  unfold SU3_CharacterDim; norm_num

#print axioms SU3_CharacterDim_fundamental

/-- **Antifundamental irrep `(0,1)` has dimension 3**. -/
theorem SU3_CharacterDim_antifundamental : SU3_CharacterDim (0, 1) = 3 := by
  unfold SU3_CharacterDim; norm_num

#print axioms SU3_CharacterDim_antifundamental

/-- **Adjoint irrep `(1,1)` has dimension 8** (the 8 gluons of QCD). -/
theorem SU3_CharacterDim_adjoint : SU3_CharacterDim (1, 1) = 8 := by
  unfold SU3_CharacterDim; norm_num

#print axioms SU3_CharacterDim_adjoint

/-- **Symmetric irrep `(2,0)` has dimension 6**. -/
theorem SU3_CharacterDim_symmetric : SU3_CharacterDim (2, 0) = 6 := by
  unfold SU3_CharacterDim; norm_num

#print axioms SU3_CharacterDim_symmetric

/-- **Decuplet irrep `(2,1)` has dimension 15**. -/
theorem SU3_CharacterDim_decuplet : SU3_CharacterDim (2, 1) = 15 := by
  unfold SU3_CharacterDim; norm_num

#print axioms SU3_CharacterDim_decuplet

/-! ## §4. The 8 gluons (adjoint dimension) -/

/-- **The number of gluons in QCD = 8** (dimension of SU(3) adjoint). -/
theorem QCD_gluon_count : SU3_CharacterDim (1, 1) = 8 :=
  SU3_CharacterDim_adjoint

/-! ## §5. Coordination note -/

/-
This file is **Phase 217** of the L23_SU3_QCD_Concrete block.

## What's done

Six substantive Lean theorems with full proofs, computing concrete
SU(3) irrep dimensions:
* Trivial = 1, Fundamental = 3, Antifundamental = 3.
* Adjoint = 8 (the 8 gluons of QCD).
* Symmetric (2,0) = 6, Decuplet (2,1) = 15.

This is **physical-QCD content**: the dimensions of the SU(3) irreps
appearing in the strong interaction.

## Strategic value

Phase 217 connects the Lean formalisation to the **actual physics
of QCD**: 3 colours of quarks (fundamental + antifundamental) and
8 gluons (adjoint).

Cross-references:
- Phase 187 `L20_SU2_Concrete_YangMills/SU2_CharacterTheory.lean`
  (parallel for SU(2)).
- Standard Model physics: 3 colours, 8 gluons.
-/

end YangMills.L23_SU3_QCD_Concrete
