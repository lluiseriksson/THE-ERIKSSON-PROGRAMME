/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3j: the gap at every finite volume -- and why that is not the statement one
wants.

Charter: docs/O-BRIDGE-CHARTER.md.
-/

import Mathlib
import YangMills.OS.PerronKernel

/-!
# O-3j — a strict spectral gap at every finite extent

## What this module proves

O-3i supplied the vacuum: a strictly positive eigenvector, unique up to scale,
carrying the spectral radius.  It explicitly did **not** prove that the rest of
the spectrum is strictly below it --- peripheral separation was listed as out of
scope, and without it `|mu| <= lam` leaves `mu = -lam` open, so no gap follows.

This module closes that, and draws the honest consequence.

* `left_eigenvalue_eq` — the positive left eigenvector has the same eigenvalue.
* `subeigen_eq` — a nonnegative `u` with `A u >= lam u` satisfies `A u = lam u`.
  Pairing against the positive left eigenvector turns the inequality into an
  equality, which is the standard device and is what makes the next step cheap.
* `neg_not_eigenvalue` — `-lam` is **not** an eigenvalue.  Proved WITHOUT the
  equality case of the triangle inequality: with `u = |w|`, `p = u - w` and
  `q = u + w` satisfy `A p = lam q` and `A q = lam p`, so if `p` were nonzero
  then `A p > 0` would force `q > 0`, hence `w >= 0`, hence `p = 0`.
* `abs_lt_of_ne_perron` — **THE GAP**: every real eigenvalue other than `lam`
  is strictly smaller in absolute value.
* `unitVacuum` / `unitVacuum_fixed` — the vacuum in Euclidean normalisation,
  `‖Ω‖ = 1` and `T Ω = Ω`, which is the form the Osterwalder--Seiler side asks
  for.
* `symWeighted_symm` — the symmetrised kernel is symmetric, so the bridge to a
  self-adjoint operator is available.

## What is NOT claimed, and it is the whole point of the title

The gap proved here is **strict at each finite extent and carries no bound
uniform in the extent**.  Nothing here contradicts that: `abs_lt_of_ne_perron`
gives `|mu| < lam` with no modulus of separation, and the separation is measured
to collapse as the extent grows outside the disordered region -- see
`docs/O-LANE-CONTINUATION-20260728.md`, where the subdominant ratio runs
`0.9205, 0.9829, 0.9964, 0.9992` at `L = 2,3,4,5`.  A paper that reported only
the positive half of this module would be reporting the half that does not
matter.

Also not claimed: algebraic simplicity; Perron--Frobenius for merely irreducible
kernels; any quantitative bound; anything about `SU(N)`, the continuum limit, or
the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

section Gap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ### §1  The positive left eigenvector, and what it buys -/

/-- The transpose of a strictly positive kernel is strictly positive, so O-3i
supplies a strictly positive **left** eigenvector. -/
theorem exists_pos_left_eigenvector (A : ι → ι → ℝ) (hA : ∀ i j, 0 < A i j) :
    ∃ (φ : ι → ℝ) (nu : ℝ), (∀ i, 0 < φ i) ∧ 0 < nu ∧
      ∀ i, ∑ j, A j i * φ j = nu * φ i := by
  obtain ⟨φ, nu, hpos, -, hnu, hE⟩ :=
    exists_pos_eigenvector (fun i j => A j i) (fun i j => hA j i)
  exact ⟨φ, nu, hpos, hnu, hE⟩

/-- Left and right Perron eigenvalues agree. -/
theorem left_eigenvalue_eq {A : ι → ι → ℝ}
    {v φ : ι → ℝ} {lam nu : ℝ}
    (hv : ∀ i, 0 < v i) (hφ : ∀ i, 0 < φ i)
    (hvE : ∀ i, ∑ j, A i j * v j = lam * v i)
    (hφE : ∀ i, ∑ j, A j i * φ j = nu * φ i) :
    lam = nu := by
  have hS : 0 < ∑ i, φ i * v i :=
    Finset.sum_pos (fun i _ => mul_pos (hφ i) (hv i))
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have h1 : ∑ i, φ i * (∑ j, A i j * v j) = lam * ∑ i, φ i * v i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hvE i]; ring
  have h2 : ∑ i, φ i * (∑ j, A i j * v j) = nu * ∑ i, φ i * v i := by
    calc ∑ i, φ i * (∑ j, A i j * v j)
        = ∑ i, ∑ j, φ i * (A i j * v j) := by
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, φ i * (A i j * v j) := Finset.sum_comm
      _ = ∑ j, v j * (∑ i, A i j * φ i) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ j, v j * (nu * φ j) := by
          exact Finset.sum_congr rfl fun j _ => by rw [hφE j]
      _ = nu * ∑ i, φ i * v i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have := h1.symm.trans h2
  have hcancel : lam * (∑ i, φ i * v i) = nu * (∑ i, φ i * v i) := this
  exact mul_right_cancel₀ (ne_of_gt hS) hcancel

/-- **A nonnegative sub-eigenvector is an eigenvector.**  Pairing against the
positive left eigenvector turns `A u ≥ lam u` into an equality. -/
theorem subeigen_eq {A : ι → ι → ℝ}
    {φ : ι → ℝ} {lam : ℝ} (hφ : ∀ i, 0 < φ i)
    (hφE : ∀ i, ∑ j, A j i * φ j = lam * φ i)
    {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hsub : ∀ i, lam * u i ≤ ∑ j, A i j * u j) :
    ∀ i, ∑ j, A i j * u j = lam * u i := by
  have hzero : ∑ i, φ i * ((∑ j, A i j * u j) - lam * u i) = 0 := by
    have hexp : ∑ i, φ i * ((∑ j, A i j * u j) - lam * u i)
        = (∑ i, φ i * (∑ j, A i j * u j)) - lam * ∑ i, φ i * u i := by
      calc ∑ i, φ i * ((∑ j, A i j * u j) - lam * u i)
          = ∑ i, (φ i * (∑ j, A i j * u j) - lam * (φ i * u i)) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ = (∑ i, φ i * (∑ j, A i j * u j)) - ∑ i, lam * (φ i * u i) :=
            Finset.sum_sub_distrib _ _
        _ = (∑ i, φ i * (∑ j, A i j * u j)) - lam * ∑ i, φ i * u i := by
            rw [← Finset.mul_sum]
    have hswap : ∑ i, φ i * (∑ j, A i j * u j) = lam * ∑ i, φ i * u i := by
      calc ∑ i, φ i * (∑ j, A i j * u j)
          = ∑ i, ∑ j, φ i * (A i j * u j) := by
            exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
        _ = ∑ j, ∑ i, φ i * (A i j * u j) := Finset.sum_comm
        _ = ∑ j, u j * (∑ i, A i j * φ i) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ j, u j * (lam * φ j) := by
            exact Finset.sum_congr rfl fun j _ => by rw [hφE j]
        _ = lam * ∑ i, φ i * u i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
    rw [hexp, hswap]
    ring
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      0 ≤ φ i * ((∑ j, A i j * u j) - lam * u i) := fun i _ =>
    mul_nonneg (le_of_lt (hφ i)) (sub_nonneg.mpr (hsub i))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero
  intro i
  have h := hall i (Finset.mem_univ i)
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 (ne_of_gt (hφ i))
  · linarith [h1]

/-! ### §2  Peripheral separation, without an equality case -/

/-- **`-lam` is not an eigenvalue.**  The classical proof goes through the
equality case of the triangle inequality; this one does not.  With `u = |w|`,
the vectors `p = u - w` and `q = u + w` satisfy `A p = lam q` and `A q = lam p`,
so a nonzero `p` would make `A p` strictly positive, hence `q` strictly
positive, hence `w` nonnegative, hence `p = 0`. -/
theorem neg_not_eigenvalue {A : ι → ι → ℝ} (hA : ∀ i j, 0 < A i j)
    {φ : ι → ℝ} {lam : ℝ} (hφ : ∀ i, 0 < φ i) (hlam : 0 < lam)
    (hφE : ∀ i, ∑ j, A j i * φ j = lam * φ i)
    {w : ι → ℝ} {i₁ : ι} (hw : w i₁ ≠ 0)
    (hwE : ∀ i, ∑ j, A i j * w j = -lam * w i) : False := by
  set u : ι → ℝ := fun i => |w i| with hudef
  have hu : ∀ i, 0 ≤ u i := fun i => abs_nonneg _
  -- `A u ≥ lam u`
  have hsub : ∀ i, lam * u i ≤ ∑ j, A i j * u j := by
    intro i
    have h1 : |∑ j, A i j * w j| ≤ ∑ j, |A i j * w j| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ j, |A i j * w j| = ∑ j, A i j * u j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [abs_mul, abs_of_pos (hA i j), hudef]
    have h3 : |∑ j, A i j * w j| = lam * u i := by
      rw [hwE i, abs_mul, abs_of_neg (by linarith : -lam < 0), hudef]
      simp
    linarith [h1, h2, h3]
  have hUE : ∀ i, ∑ j, A i j * u j = lam * u i := subeigen_eq hφ hφE hu hsub
  -- `p` and `q`
  set p : ι → ℝ := fun i => u i - w i with hp
  set q : ι → ℝ := fun i => u i + w i with hq
  have hpnn : ∀ i, 0 ≤ p i := fun i => by
    simp only [hp, hudef]
    linarith [le_abs_self (w i)]
  have hApq : ∀ i, ∑ j, A i j * p j = lam * q i := by
    intro i
    have hsplit : ∑ j, A i j * p j = (∑ j, A i j * u j) - ∑ j, A i j * w j := by
      rw [hp]
      calc ∑ j, A i j * (u j - w j)
          = ∑ j, (A i j * u j - A i j * w j) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = _ := Finset.sum_sub_distrib _ _
    rw [hsplit, hUE i, hwE i, hq]
    ring
  by_cases hpz : ∀ i, p i = 0
  · -- then `w = |w| ≥ 0`, so `A w = lam w` and `A w = -lam w`
    have hwu : ∀ i, w i = u i := fun i => by have := hpz i; rw [hp] at this; linarith
    have h1 : ∀ i, ∑ j, A i j * w j = lam * w i := by
      intro i
      rw [Finset.sum_congr rfl fun j _ => by rw [hwu j], hUE i, hwu i]
    have h2 := (h1 i₁).symm.trans (hwE i₁)
    have : lam * w i₁ = -lam * w i₁ := h2
    have hz : w i₁ = 0 := by nlinarith [this, hlam]
    exact hw hz
  · push_neg at hpz
    obtain ⟨i₂, hi₂⟩ := hpz
    have hppos : 0 < p i₂ := lt_of_le_of_ne (hpnn i₂) (Ne.symm hi₂)
    have hqpos : ∀ i, 0 < q i := by
      intro i
      have h1 : 0 < ∑ j, A i j * p j := apply_pos_of_nonneg hA hpnn hppos i
      rw [hApq i] at h1
      nlinarith [h1, hlam]
    -- `q i > 0` forces `w i ≥ 0`, hence `p i = 0` everywhere
    have hwnn : ∀ i, 0 ≤ w i := by
      intro i
      by_contra hneg
      push_neg at hneg
      have : q i = 0 := by
        rw [hq]
        simp only []
        rw [hudef]
        simp only []
        rw [abs_of_neg hneg]
        ring
      exact absurd this (ne_of_gt (hqpos i))
    have : p i₂ = 0 := by
      rw [hp]
      simp only []
      rw [hudef]
      simp only []
      rw [abs_of_nonneg (hwnn i₂)]
      ring
    exact absurd this (ne_of_gt hppos)

/-! ### §3  The gap -/

/-- **THE GAP AT EVERY FINITE EXTENT.**  Every real eigenvalue other than the
Perron eigenvalue is strictly smaller in absolute value.

This is a *strict* separation, not a *quantitative* one: it provides no modulus
of separation, and in particular nothing uniform in the size of `ι`. -/
theorem abs_lt_of_ne_perron {A : ι → ι → ℝ} (hA : ∀ i j, 0 < A i j)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, A i j * v j = lam * v i)
    {w : ι → ℝ} {i₁ : ι} (hw : w i₁ ≠ 0) {mu : ℝ}
    (hwE : ∀ i, ∑ j, A i j * w j = mu * w i) (hne : mu ≠ lam) :
    |mu| < lam := by
  have hA' : ∀ i j, 0 ≤ A i j := fun i j => le_of_lt (hA i j)
  have hlam : 0 < lam := eigenvalue_pos hA hv hvE
  have hle : |mu| ≤ lam :=
    abs_eigenvalue_le_of_pos_eigenvector A hA' v hv lam hvE w i₁ hw mu hwE
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    obtain ⟨φ, nu, hφ, hnu, hφE⟩ := exists_pos_left_eigenvector A hA
    have hnl : lam = nu := left_eigenvalue_eq hv hφ hvE hφE
    subst hnl
    rcases abs_eq (le_of_lt hlam) |>.mp h with hpos | hneg
    · exact hne hpos
    · exact neg_not_eigenvalue hA hφ hlam hφE hw
        (fun i => by rw [hwE i, hneg])

/-! ### §4  The vacuum in Euclidean normalisation -/

/-- The Euclidean norm of a vector on a finite type. -/
noncomputable def eucNorm (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i * v i)

theorem eucNorm_pos {v : ι → ℝ} (hv : ∀ i, 0 < v i) : 0 < eucNorm v := by
  unfold eucNorm
  refine Real.sqrt_pos.mpr ?_
  exact Finset.sum_pos (fun i _ => mul_pos (hv i) (hv i))
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩

/-- The vacuum, Euclidean-normalised. -/
noncomputable def unitVacuum (v : ι → ℝ) (i : ι) : ℝ := v i / eucNorm v

theorem unitVacuum_pos {v : ι → ℝ} (hv : ∀ i, 0 < v i) (i : ι) :
    0 < unitVacuum v i :=
  div_pos (hv i) (eucNorm_pos hv)

/-- `‖Ω‖ = 1` in the Euclidean sense. -/
theorem unitVacuum_norm {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    ∑ i, unitVacuum v i * unitVacuum v i = 1 := by
  have hN : 0 < eucNorm v := eucNorm_pos hv
  have hsq : eucNorm v * eucNorm v = ∑ i, v i * v i := by
    unfold eucNorm
    exact Real.mul_self_sqrt (Finset.sum_nonneg fun i _ =>
      mul_nonneg (le_of_lt (hv i)) (le_of_lt (hv i)))
  have hsum : ∑ i, unitVacuum v i * unitVacuum v i
      = (∑ i, v i * v i) / (eucNorm v * eucNorm v) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by unfold unitVacuum; ring
  rw [hsum, hsq, div_self]
  exact ne_of_gt (Finset.sum_pos (fun i _ => mul_pos (hv i) (hv i))
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩)

/-- **`T Ω = Ω` with `Ω` of unit Euclidean norm** --- the form the
Osterwalder--Seiler side asks for. -/
theorem unitVacuum_fixed {A : ι → ι → ℝ} {v : ι → ℝ} {lam : ℝ}
    (hv : ∀ i, 0 < v i) (hlam : lam ≠ 0)
    (hvE : ∀ i, ∑ j, A i j * v j = lam * v i) :
    ∀ i, ∑ j, normalizedKernel A lam i j * unitVacuum v j = unitVacuum v i := by
  intro i
  have hN : (eucNorm v) ≠ 0 := ne_of_gt (eucNorm_pos hv)
  have hsplit : ∑ j, normalizedKernel A lam i j * unitVacuum v j
      = (∑ j, normalizedKernel A lam i j * v j) / eucNorm v := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold unitVacuum
    ring
  rw [hsplit, normalizedKernel_fixes_eigenvector hlam hvE i]
  unfold unitVacuum
  rfl

/-! ### §5  The symmetrised kernel is symmetric -/

/-- The symmetrised form of a source-weighted kernel. -/
noncomputable def symWeighted {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (σ τ : Fin L → Fin 2) : ℝ :=
  Real.sqrt (w σ) * spatialKernel β σ τ * Real.sqrt (w τ)

/-- **It is symmetric**, because the decoupled kernel is.  This is the bridge to
a self-adjoint operator, and it is the object the next module needs. -/
theorem symWeighted_symm {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (σ τ : Fin L → Fin 2) :
    symWeighted w β σ τ = symWeighted w β τ σ := by
  unfold symWeighted
  rw [spatialKernel_symm]
  ring

theorem symWeighted_pos {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (β : ℝ) (σ τ : Fin L → Fin 2) : 0 < symWeighted w β σ τ := by
  unfold symWeighted
  have h1 : 0 < Real.sqrt (w σ) := Real.sqrt_pos.mpr (hw σ)
  have h2 : 0 < Real.sqrt (w τ) := Real.sqrt_pos.mpr (hw τ)
  have h3 : 0 < spatialKernel β σ τ := spatialKernel_pos β σ τ
  positivity

/-! ### §5b  A real symmetric kernel has real eigenvalues -/

/-- **Every complex eigenvalue of a real symmetric kernel is real.**  Proved
from scratch, by the classical one-line argument: `⟨y, S y⟩` equals its own
conjugate because `S` is real and symmetric, and pairing it against `y` twice
gives `conj mu * N = mu * N` with `N = ∑ ‖y i‖² > 0`. -/
theorem eigenvalue_real_of_symm {S : ι → ι → ℝ} (hsymm : ∀ i j, S i j = S j i)
    {y : ι → ℂ} {i₁ : ι} (hy : y i₁ ≠ 0) {mu : ℂ}
    (hyE : ∀ i, ∑ j, (S i j : ℂ) * y j = mu * y i) :
    (starRingEnd ℂ) mu = mu := by
  set N : ℂ := ∑ i, y i * (starRingEnd ℂ) (y i) with hN
  have hNre : (starRingEnd ℂ) N = N := by
    rw [hN, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Complex.conj_conj]
    ring
  have hNne : N ≠ 0 := by
    rw [hN]
    have hterm : ∀ i, y i * (starRingEnd ℂ) (y i) = ((Complex.normSq (y i) : ℝ) : ℂ) :=
      fun i => Complex.mul_conj (y i)
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [← Complex.ofReal_sum]
    have hpos : 0 < ∑ i, Complex.normSq (y i) := by
      refine Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (y i)) ?_
      exact ⟨i₁, Finset.mem_univ _, Complex.normSq_pos.mpr hy⟩
    exact_mod_cast ne_of_gt hpos
  -- the pairing, computed two ways
  set Q : ℂ := ∑ i, (starRingEnd ℂ) (y i) * (∑ j, (S i j : ℂ) * y j) with hQ
  have hQ1 : Q = mu * N := by
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hyE i]
    ring
  have hQ2 : (starRingEnd ℂ) Q = mu * N := by
    have hstep : (starRingEnd ℂ) Q
        = ∑ i, ∑ j, (S i j : ℂ) * (y i * (starRingEnd ℂ) (y j)) := by
      rw [hQ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Complex.conj_conj, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Complex.conj_ofReal]
      ring
    rw [hstep, Finset.sum_comm]
    have hswap : ∑ j, ∑ i, (S i j : ℂ) * (y i * (starRingEnd ℂ) (y j))
        = ∑ j, (starRingEnd ℂ) (y j) * (∑ i, (S j i : ℂ) * y i) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsymm i j]
      ring
    rw [hswap]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hyE j]
    ring
  have : (starRingEnd ℂ) mu * N = mu * N := by
    have h := hQ2
    rw [hQ1, map_mul, hNre] at h
    exact h
  exact mul_right_cancel₀ hNne this

end Gap

/-! ### §6  The gap for the coupled slice, at every extent -/

/-- **THE COUPLED SLICE HAS A STRICT GAP AT EVERY EXTENT.**  For every `L`,
every `β`, and every strictly positive source weight, every real eigenvalue
other than the Perron one is strictly smaller in absolute value.

No bound uniform in `L` is claimed, and none follows: the statement carries no
modulus of separation. -/
theorem coupled_gap_of_sourceWeight {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ)
    {v : (Fin L → Fin 2) → ℝ} (hv : ∀ σ, 0 < v σ) {lam : ℝ}
    (hvE : ∀ σ, ∑ τ : Fin L → Fin 2, sourceWeightedKernelL w β σ τ * v τ = lam * v σ)
    {u : (Fin L → Fin 2) → ℝ} {σ₁ : Fin L → Fin 2} (hu : u σ₁ ≠ 0) {mu : ℝ}
    (huE : ∀ σ, ∑ τ : Fin L → Fin 2, sourceWeightedKernelL w β σ τ * u τ = mu * u σ)
    (hne : mu ≠ lam) :
    |mu| < lam :=
  abs_lt_of_ne_perron (sourceWeightedKernelL_pos hw β) hv hvE hu huE hne

/-! ### §7  Every eigenvalue of the coupled kernel is real -/

/-- The diagonal similarity: the source-weighted kernel and its symmetrised
form are conjugate by `diag(√w)`, coordinatewise. -/
theorem sourceWeighted_eq_sym {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (σ τ : Fin L → Fin 2) :
    sourceWeightedKernelL w β σ τ
      = Real.sqrt (w σ) * symWeighted w β σ τ / Real.sqrt (w τ) := by
  have hτ : Real.sqrt (w τ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hw τ))
  have hσ : Real.sqrt (w σ) * Real.sqrt (w σ) = w σ :=
    Real.mul_self_sqrt (le_of_lt (hw σ))
  unfold sourceWeightedKernelL symWeighted
  field_simp
  nlinarith [hσ, spatialKernel_pos β σ τ]

/-- **Every complex eigenvalue of the coupled kernel is real.**  The kernel is
conjugate by a positive diagonal to the symmetrised one, which is symmetric, so
the eigenvalue is inherited and `eigenvalue_real_of_symm` applies.  This is what
upgrades the gap of §3 from *real eigenvalues* to *all eigenvalues*. -/
theorem coupled_eigenvalue_real {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ)
    {x : (Fin L → Fin 2) → ℂ} {σ₁ : Fin L → Fin 2} (hx : x σ₁ ≠ 0) {mu : ℂ}
    (hxE : ∀ σ, ∑ τ : Fin L → Fin 2,
      ((sourceWeightedKernelL w β σ τ : ℝ) : ℂ) * x τ = mu * x σ) :
    (starRingEnd ℂ) mu = mu := by
  classical
  set d : (Fin L → Fin 2) → ℝ := fun σ => Real.sqrt (w σ) with hd
  have hdpos : ∀ σ, 0 < d σ := fun σ => Real.sqrt_pos.mpr (hw σ)
  set y : (Fin L → Fin 2) → ℂ := fun σ => x σ / ((d σ : ℝ) : ℂ) with hy
  have hdne : ∀ σ, ((d σ : ℝ) : ℂ) ≠ 0 := fun σ => by
    exact_mod_cast ne_of_gt (hdpos σ)
  have hyne : y σ₁ ≠ 0 := by
    rw [hy]
    exact div_ne_zero hx (hdne σ₁)
  refine eigenvalue_real_of_symm (symWeighted_symm w β) hyne (mu := mu) ?_
  intro σ
  have hstep : ∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * y τ
      = (((d σ : ℝ) : ℂ))⁻¹ *
        ∑ τ : Fin L → Fin 2, ((sourceWeightedKernelL w β σ τ : ℝ) : ℂ) * x τ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [sourceWeighted_eq_sym hw β σ τ, hy]
    simp only [hd]
    have hsg : ((Real.sqrt (w σ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (hw σ))
    have hst : ((Real.sqrt (w τ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (hw τ))
    push_cast
    field_simp
  rw [hstep, hxE σ, hy]
  field_simp

end YangMills.OS
