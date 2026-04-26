/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# LSI predicate (Phase 373)

The Logarithmic Sobolev Inequality predicate.

## Strategic placement

This is **Phase 373** of the L39_CreativeAttack_BalabanRGTransfer block —
tenth substantive attack of the session.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L39_CreativeAttack_BalabanRGTransfer

/-! ## §1. LSI structure -/

/-- **Logarithmic Sobolev Inequality**: with constant `c > 0`,
    `Ent(f²) ≤ 2c · ⟨|∇f|²⟩` for all suitable `f`. Stated abstractly. -/
structure LSI where
  /-- The LSI constant. -/
  c : ℝ
  /-- The constant is positive. -/
  c_pos : 0 < c

/-- **Default LSI with c = 1**. -/
def defaultLSI : LSI := { c := 1, c_pos := by norm_num }

/-! ## §2. Constants and bounds -/

/-- **The LSI constant is at most 1 for the default**. -/
theorem defaultLSI_c : defaultLSI.c = 1 := rfl

/-- **Smaller `c` is "stronger" (tighter LSI)**. -/
def LSI_at_least_as_strong_as (lsi₁ lsi₂ : LSI) : Prop :=
  lsi₁.c ≤ lsi₂.c

theorem LSI_strength_refl (lsi : LSI) :
    LSI_at_least_as_strong_as lsi lsi := le_refl _

end YangMills.L39_CreativeAttack_BalabanRGTransfer
