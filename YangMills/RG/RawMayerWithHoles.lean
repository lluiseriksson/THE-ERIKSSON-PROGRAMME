/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.LocalFunctional

/-!
# Raw Mayer transform for type-local activities

This file adds the first transparent map consumed by a Dimock-F.1-style
with-holes construction: the raw Mayer transform

`H ↦ exp H - 1`.

It is defined on the type-local substrates from `LocalFunctional.lean`, so it
preserves supports by construction and inherits off-support invariance from the
typed locality bridge.  The only analytic estimate here is the elementary
small-activity bound `‖exp z - 1‖ ≤ 2 ‖z‖` for `‖z‖ ≤ 1`, already available in
Mathlib.

Honest scope: this is not Dimock Appendix F, not the Ω-connected cover
compiler, not ultralocal integration, and not the Yang--Mills activity-decay
bound.  It is the local `H_X ↦ m_X` substrate those later constructions should
consume.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

namespace LocalFunctional

variable {Site : Type*} {V : Site → Type*}

/-- Raw Mayer transform of a scalar complex local functional:
`H ↦ exp H - 1`. -/
noncomputable def rawMayer (F : LocalFunctional Site V ℂ) :
    LocalFunctional Site V ℂ :=
  F.map fun z => Complex.exp z - 1

@[simp] theorem rawMayer_support (F : LocalFunctional Site V ℂ) :
    F.rawMayer.support = F.support := rfl

@[simp] theorem globalEval_rawMayer (F : LocalFunctional Site V ℂ)
    (φ : ∀ x, V x) :
    F.rawMayer.globalEval φ = Complex.exp (F.globalEval φ) - 1 := rfl

/-- The raw Mayer transform remains insensitive to changes off the declared
support. -/
theorem rawMayer_globalEval_eq_of_agreeOn (F : LocalFunctional Site V ℂ)
    {φ ψ : ∀ x, V x} (h : AgreeOn F.support φ ψ) :
    F.rawMayer.globalEval φ = F.rawMayer.globalEval ψ :=
  F.rawMayer.globalEval_eq_of_agreeOn h

/-- Small-activity bound for the raw Mayer transform. -/
theorem norm_globalEval_rawMayer_le_two
    (F : LocalFunctional Site V ℂ) (φ : ∀ x, V x)
    (hsmall : ‖F.globalEval φ‖ ≤ 1) :
    ‖F.rawMayer.globalEval φ‖ ≤ 2 * ‖F.globalEval φ‖ := by
  change ‖Complex.exp (F.globalEval φ) - 1‖ ≤ 2 * ‖F.globalEval φ‖
  exact Complex.norm_exp_sub_one_le hsmall

end LocalFunctional

namespace LocalActivity

variable {Site : Type*} {Ψ Φ : Site → Type*}

/-- Raw Mayer transform of a two-field scalar complex local activity:
`H ↦ exp H - 1`. -/
noncomputable def rawMayer (F : LocalActivity Site Ψ Φ ℂ) :
    LocalActivity Site Ψ Φ ℂ :=
  F.map fun z => Complex.exp z - 1

@[simp] theorem rawMayer_spectatorSupport (F : LocalActivity Site Ψ Φ ℂ) :
    F.rawMayer.spectatorSupport = F.spectatorSupport := rfl

@[simp] theorem rawMayer_fluctuationSupport (F : LocalActivity Site Ψ Φ ℂ) :
    F.rawMayer.fluctuationSupport = F.fluctuationSupport := rfl

@[simp] theorem globalEval_rawMayer (F : LocalActivity Site Ψ Φ ℂ)
    (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x) :
    F.rawMayer.globalEval ψ φ = Complex.exp (F.globalEval ψ φ) - 1 := rfl

/-- The two-field raw Mayer transform remains insensitive to off-support
changes in both the spectator and fluctuation fields. -/
theorem rawMayer_globalEval_eq_of_agreeOn (F : LocalActivity Site Ψ Φ ℂ)
    {ψ₁ ψ₂ : ∀ x, Ψ x} {φ₁ φ₂ : ∀ x, Φ x}
    (hψ : AgreeOn F.spectatorSupport ψ₁ ψ₂)
    (hφ : AgreeOn F.fluctuationSupport φ₁ φ₂) :
    F.rawMayer.globalEval ψ₁ φ₁ = F.rawMayer.globalEval ψ₂ φ₂ :=
  F.rawMayer.globalEval_eq_of_agreeOn hψ hφ

/-- Small-activity bound for the two-field raw Mayer transform. -/
theorem norm_globalEval_rawMayer_le_two
    (F : LocalActivity Site Ψ Φ ℂ) (ψ : ∀ x, Ψ x) (φ : ∀ x, Φ x)
    (hsmall : ‖F.globalEval ψ φ‖ ≤ 1) :
    ‖F.rawMayer.globalEval ψ φ‖ ≤ 2 * ‖F.globalEval ψ φ‖ := by
  change ‖Complex.exp (F.globalEval ψ φ) - 1‖ ≤ 2 * ‖F.globalEval ψ φ‖
  exact Complex.norm_exp_sub_one_le hsmall

end LocalActivity

end YangMills.RG
