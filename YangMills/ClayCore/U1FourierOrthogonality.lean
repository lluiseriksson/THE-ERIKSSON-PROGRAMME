/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# U(1) character orthogonality — the first exact non-vacuous value

`SUOneDegenerate.lean` showed that modelling U(1) as `SU(1)` is degenerate (the
group is trivial).  The **correct** U(1) is the circle group, which Mathlib
realises as `AddCircle T = ℝ/Tℤ` with:

* `AddCircle.haarAddCircle` — the normalized (probability) Haar measure, and
* `fourier n : AddCircle T → ℂ` — the characters `x ↦ e^{2πi n x / T}`.

On this — the *real* U(1) — the abelian analogue of the SU(N) centre rules is the
**complete Fourier orthogonality**, and unlike the centre rules it pins the
non-zero value as well:

  `∫ fourier n dHaar = (if n = 0 then 1 else 0).`

This is the **first honestly non-vacuous exact value in the project**: a genuine
`= 1` (not merely `= 0`).  U(1) is special precisely because it is its own
centre — there are no centre-blind non-trivial irreducibles (contrast SU(N),
N ≥ 2, where the adjoint and other zero-N-ality characters require Peter–Weyl /
Schur to integrate to zero; see `HORIZON.md §3.1`).

## Proof — the same eigenfunction principle, in additive form

`fourier 0 = 1`, so the `n = 0` integral is the total mass `1`.

For `n ≠ 0`, translation by the *half-index* element `a = T/2/n` negates the
character: `fourier n (x + a) = − fourier n x` (`fourier_add_half_inv_index`).
So `fourier n` is an eigenfunction of additive translation with eigenvalue
`c = −1 ≠ 1`.  Additive left-invariance of Haar (`integral_add_left_eq_self`)
gives `J = −J`, hence `J = 0`.  This is the additive incarnation of
`LeftInvariantVanishing.integral_eq_zero_of_left_invariant_eigenfunction`, here on
the genuine U(1).

This realises node **F0–F1 for U(1)** of `HORIZON.md §5`, the bypass of the
Peter–Weyl bottleneck for the abelian warm-up.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no new axioms.
(Pending a `lake build` pass.  All lemmas used were checked against the Mathlib
source: `fourier_add_half_inv_index`, `integral_add_left_eq_self`, `fourier_zero`.)
-/

namespace YangMills

open MeasureTheory AddCircle Complex ComplexConjugate

noncomputable section

/-! ## Vanishing of non-trivial characters -/

/-- For `n ≠ 0`, the Haar integral of the character `fourier n` over the circle
vanishes.  Proved from the half-index translation (eigenvalue `−1`) and additive
left-invariance of Haar — the abelian form of the centre-vanishing engine. -/
theorem integral_fourier_eq_zero
    {T : ℝ} [hT : Fact (0 < T)] {n : ℤ} (hn : n ≠ 0) :
    ∫ x : AddCircle T, fourier n x ∂haarAddCircle = 0 := by
  set J : ℂ := ∫ x : AddCircle T, fourier n x ∂haarAddCircle with hJ
  -- Additive left-invariance: translating by the half-index does not change ∫.
  have hinv : J = ∫ x, fourier n ((↑(T / 2 / n) : AddCircle T) + x) ∂haarAddCircle := by
    rw [hJ]; symm
    exact integral_add_left_eq_self (fun x => fourier n x) (↑(T / 2 / n) : AddCircle T)
  -- That translation negates the character: eigenvalue −1.
  have hpt : (fun x : AddCircle T => fourier n ((↑(T / 2 / n) : AddCircle T) + x))
           = (fun x => (-1 : ℂ) * fourier n x) := by
    funext x
    rw [add_comm, fourier_add_half_inv_index hn hT.out x]
    ring
  have hcm : (∫ x : AddCircle T, (-1 : ℂ) * fourier n x ∂haarAddCircle) = (-1 : ℂ) * J := by
    rw [hJ]; exact integral_const_mul (-1) (fun x => fourier n x)
  rw [hpt, hcm] at hinv
  -- `J = −1 · J` forces `2J = 0`, hence `J = 0`.
  have h2 : (2 : ℂ) * J = 0 := by linear_combination hinv
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (by norm_num)
  · exact h

/-! ## The trivial character integrates to one -/

/-- `fourier 0 = 1`, so its Haar integral is the total mass `1`.  This is the
first genuine non-zero exact value. -/
theorem integral_fourier_zero
    {T : ℝ} [Fact (0 < T)] :
    ∫ _x : AddCircle T, fourier 0 _x ∂haarAddCircle = 1 := by
  simp

/-! ## Complete U(1) character orthogonality -/

/-- **U(1) character orthogonality.**

`∫ fourier n dHaar = δ_{n,0}` on the circle: `1` for the trivial character,
`0` for every non-trivial one.  The first non-vacuous exact value in the project
(the `n = 0` case is a genuine `= 1`). -/
theorem integral_fourier_eq_indicator
    {T : ℝ} [Fact (0 < T)] (n : ℤ) :
    ∫ x : AddCircle T, fourier n x ∂haarAddCircle = (if n = 0 then 1 else 0) := by
  by_cases h : n = 0
  · subst h; rw [if_pos rfl]; exact integral_fourier_zero
  · rw [if_neg h]; exact integral_fourier_eq_zero h

/-- Restated as orthogonality of distinct characters: the Haar inner product of
`fourier m` and `fourier n` is `δ_{m,n}`.  (Uses `fourier (n−m)` and the
indicator form; the `m = n` value is `1`, the off-diagonal is `0`.) -/
theorem integral_fourier_sub_eq_indicator
    {T : ℝ} [Fact (0 < T)] (m n : ℤ) :
    ∫ x : AddCircle T, fourier (n - m) x ∂haarAddCircle = (if n = m then 1 else 0) := by
  rw [integral_fourier_eq_indicator]
  simp only [sub_eq_zero]

/-- **U(1) character orthonormality** (the abelian Peter–Weyl / Schur relation).

`⟨fourier m, fourier n⟩_{L²(Haar)} = ∫ fourier m · conj(fourier n) dHaar = δ_{m,n}`.
This is the complete statement that the circle characters form an orthonormal
family — the abelian analogue of the SU(N) Schur orthogonality (node F4) that, for
N ≥ 2, still needs Peter–Weyl.  Here it is unconditional. -/
theorem integral_fourier_mul_conj_eq_indicator
    {T : ℝ} [Fact (0 < T)] (m n : ℤ) :
    ∫ x : AddCircle T, fourier m x * conj (fourier n x) ∂haarAddCircle =
      (if m = n then 1 else 0) := by
  have h : (fun x : AddCircle T => fourier m x * conj (fourier n x))
         = (fun x => fourier (m - n) x) := by
    funext x; rw [← fourier_neg, ← fourier_add, sub_eq_add_neg]
  rw [h, integral_fourier_eq_indicator]
  simp only [sub_eq_zero]

end

end YangMills
