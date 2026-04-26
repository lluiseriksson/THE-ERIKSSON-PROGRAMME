/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Discrete Laplacian definition (Phase 324)

The 1D discrete Laplacian: `Δ_a f(x) = (f(x+a) + f(x-a) - 2f(x))/a²`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L34_CreativeAttack_WilsonCoeff

/-! ## §1. Discrete Laplacian (1D) -/

/-- **1D discrete Laplacian**: `Δ_a f(x) = (f(x+a) + f(x-a) - 2 f(x)) / a²`. -/
def discreteLaplacian (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (f (x + a) + f (x - a) - 2 * f x) / a ^ 2

/-! ## §2. At zero spacing (well-defined) -/

/-- **Zero-divisor convention**: at `a = 0`, the Laplacian is `0/0 = 0`
    by Lean's convention. -/
theorem discreteLaplacian_at_zero_a (f : ℝ → ℝ) (x : ℝ) :
    discreteLaplacian f 0 x = (f x + f x - 2 * f x) / 0 := by
  unfold discreteLaplacian
  simp

/-! ## §3. Linearity in `f` -/

/-- **Discrete Laplacian is linear in `f`**: `Δ(f + g) = Δf + Δg`. -/
theorem discreteLaplacian_add (f g : ℝ → ℝ) (a x : ℝ) (ha : a ≠ 0) :
    discreteLaplacian (fun y => f y + g y) a x =
      discreteLaplacian f a x + discreteLaplacian g a x := by
  unfold discreteLaplacian
  field_simp
  ring

#print axioms discreteLaplacian_add

/-- **Scaling**: `Δ(c · f) = c · Δf`. -/
theorem discreteLaplacian_smul (f : ℝ → ℝ) (c : ℝ) (a x : ℝ) :
    discreteLaplacian (fun y => c * f y) a x =
      c * discreteLaplacian f a x := by
  unfold discreteLaplacian
  ring

end YangMills.L34_CreativeAttack_WilsonCoeff
