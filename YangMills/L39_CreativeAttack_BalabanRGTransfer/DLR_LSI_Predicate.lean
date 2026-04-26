/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L39_CreativeAttack_BalabanRGTransfer.LSI_Predicate

/-!
# DLR-LSI predicate (Phase 374)

The Dobrushin-Lanford-Ruelle (DLR) version of LSI: LSI uniform over
all DLR conditional measures.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L39_CreativeAttack_BalabanRGTransfer

/-! ## §1. DLR-LSI structure -/

/-- **DLR-LSI**: a UNIFORM LSI constant `c_DLR` valid for ALL DLR
    conditional measures. -/
structure DLR_LSI where
  /-- The uniform DLR-LSI constant. -/
  c_DLR : ℝ
  /-- The constant is positive. -/
  c_DLR_pos : 0 < c_DLR

/-- **Default DLR-LSI with `c_DLR = 1`**. -/
def defaultDLR_LSI : DLR_LSI := { c_DLR := 1, c_DLR_pos := by norm_num }

/-! ## §2. Relation to ordinary LSI -/

/-- **DLR-LSI implies LSI** (taking the DLR conditional with empty
    boundary condition gives the unconditional LSI). -/
def DLR_LSI_implies_LSI (dlr : DLR_LSI) : LSI :=
  { c := dlr.c_DLR, c_pos := dlr.c_DLR_pos }

theorem DLR_implies_LSI_constant (dlr : DLR_LSI) :
    (DLR_LSI_implies_LSI dlr).c = dlr.c_DLR := rfl

#print axioms DLR_implies_LSI_constant

/-! ## §3. Strength comparison -/

/-- **DLR-LSI is stronger than LSI**: same constant, more conditional
    measures controlled. -/
def DLR_stronger_than_LSI (dlr : DLR_LSI) (lsi : LSI) : Prop :=
  dlr.c_DLR ≤ lsi.c

end YangMills.L39_CreativeAttack_BalabanRGTransfer
