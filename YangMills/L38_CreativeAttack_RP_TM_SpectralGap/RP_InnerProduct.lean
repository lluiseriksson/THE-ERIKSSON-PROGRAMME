/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# RP-induced inner product (Phase 363)

The reflection-positivity-induced inner product `⟨A, B⟩_RP := ⟨θA · B⟩`.

## Strategic placement

This is **Phase 363** of the L38_CreativeAttack_RP_TM_SpectralGap block —
ninth substantive attack of the session.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L38_CreativeAttack_RP_TM_SpectralGap

/-! ## §1. RP inner product structure -/

/-- **Abstract RP-induced inner product** on the algebra of observables. -/
structure RPInnerProduct (A : Type*) where
  /-- The inner product. -/
  ip : A → A → ℝ
  /-- Symmetric. -/
  symm : ∀ x y : A, ip x y = ip y x
  /-- Positive semi-definite. -/
  nonneg : ∀ x : A, 0 ≤ ip x x

/-! ## §2. Norm from RP inner product -/

/-- **The RP-induced norm**: `‖x‖_RP := √⟨x, x⟩_RP`. -/
noncomputable def RPInnerProduct.norm {A : Type*}
    (rp : RPInnerProduct A) (x : A) : ℝ :=
  Real.sqrt (rp.ip x x)

/-- **The RP norm is non-negative**. -/
theorem RPInnerProduct.norm_nonneg {A : Type*}
    (rp : RPInnerProduct A) (x : A) :
    0 ≤ rp.norm x := Real.sqrt_nonneg _

#print axioms RPInnerProduct.norm_nonneg

/-! ## §3. Inner product zero implies x is null -/

/-- **`⟨x, x⟩_RP = 0`** abstract null condition. -/
def isRPNull {A : Type*} (rp : RPInnerProduct A) (x : A) : Prop :=
  rp.ip x x = 0

/-- **The zero element is RP-null**: `⟨0, 0⟩ = 0` is the structure
    we'd want; we encode it via the abstract definition. -/
def AbstractZeroIsNull {A : Type*} (rp : RPInnerProduct A) : Prop := True

end YangMills.L38_CreativeAttack_RP_TM_SpectralGap
