/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinOscillation

/-!
# D-3b/D-3c — the single-site conditional operator, and the key lemma

Charter: `docs/DOBRUSHIN-D3-CHARTER.md`, Amendment 1.  Gates: J9 of
`scripts/judge_dobrushin_d3.py` (the key lemma as a number, exhaustively over
all Boolean observables on small cells) and J11 of
`scripts/judge_dobrushin_d3b.py` (the orientation, on a cell whose minimal
coefficients are NOT symmetric), both committed before this file.

## The three-way split of Amendment 1, honoured here

* `deltaAt_condExp_self` — `δᵢ (Eᵢ f) = 0` is a SEMANTIC statement.  It rests
  on the locality hypothesis alone (the conditional at `i` does not see the old
  value at `i`) and mentions no matrix.
* `deltaAt_condExp_le` — the transport clause `δₖ (Eᵢ f) ≤ δₖ f + C i k · δᵢ f`
  for `k ≠ i` consumes only that `C i k` DOMINATES the influence of `k` on the
  conditional at `i`.  It never asks `C` to be minimal, which is the same
  distinction that cost two paper versions for `tanh|J|`.
* `deltaAt_condExp_le_matrix` — the vector form, and the ONLY statement in this
  file that assumes `C i i = 0`.  The zero on the diagonal is a DECLARED
  hypothesis of the matrix assembly, never an accident of a physical instance.

## Conventions

`deltaAt i f` is the oscillation of `f` in the single coordinate `i`: the
supremum of `|f η − f η'|` over pairs that agree off `i`.  Every such pair is
`(η, Function.update η i s)` for some `s`, and that is the form the definition
takes.  The DECLARED ORIENTATION (fixed in `judge_dobrushin_d3b.py` before any
Lean): `C i k` bounds the influence OF site `k` ON the conditional AT `i`,
i.e. the total variation moved by changing `η` only at `k`.

## What this file does NOT claim

No measure appears here.  Nothing about a Gibbs weight, nothing about
invariance, nothing about covariance: those are D-3d/D-3e
(`DobrushinComparison.lean`).  Dobrushin's argument is classical (Dobrushin
1968/1970; Simon, *The Statistical Mechanics of Lattice Gases*, Ch. V); nothing
here is presented as new mathematics.  The claim is mechanisation.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : Type*} [Fintype S] [Nonempty S]

/-! ## §0  Update algebra, localised

Only `Function.update_apply` is consumed from the library; the three facts the
file actually uses are derived here once, so that a library rename cannot touch
more than one line. -/

theorem update_self' (η : ι → S) (i : ι) (s : S) :
    Function.update η i s i = s := by
  rw [Function.update_apply, if_pos rfl]

theorem update_other (η : ι → S) (i : ι) (s : S) {j : ι} (hj : j ≠ i) :
    Function.update η i s j = η j := by
  rw [Function.update_apply, if_neg hj]

theorem update_update (η : ι → S) (i : ι) (s t : S) :
    Function.update (Function.update η i s) i t = Function.update η i t := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [update_self', update_self']
  · rw [update_other _ _ _ hj, update_other _ _ _ hj, update_other _ _ _ hj]

/-- The total variation of a distribution against itself vanishes.  Generic,
and consumed by the non-vacuity witness of the comparison module. -/
theorem TV_self (q : S → ℝ) : TV q q = 0 := by
  have h : ∀ x ∈ (Finset.univ : Finset S), |q x - q x| = 0 := by
    intro x _
    rw [sub_self, abs_zero]
  unfold TV
  rw [Finset.sum_eq_zero h, zero_div]

/-! ## §1  The single-coordinate oscillation -/

/-- The oscillation of `f` in the single coordinate `i`: the largest change `f`
can suffer when only the value at `i` moves. -/
noncomputable def deltaAt (i : ι) (f : (ι → S) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun q : (ι → S) × S => |f q.1 - f (Function.update q.1 i q.2)|)

theorem abs_sub_update_le_deltaAt (i : ι) (f : (ι → S) → ℝ) (η : ι → S) (s : S) :
    |f η - f (Function.update η i s)| ≤ deltaAt i f :=
  Finset.le_sup'
    (fun q : (ι → S) × S => |f q.1 - f (Function.update q.1 i q.2)|)
    (Finset.mem_univ (⟨η, s⟩ : (ι → S) × S))

theorem deltaAt_nonneg (i : ι) (f : (ι → S) → ℝ) : 0 ≤ deltaAt i f := by
  obtain ⟨η⟩ : Nonempty (ι → S) := inferInstance
  obtain ⟨s⟩ := ‹Nonempty S›
  exact le_trans (abs_nonneg _) (abs_sub_update_le_deltaAt i f η s)

theorem deltaAt_le (i : ι) (f : (ι → S) → ℝ) {B : ℝ}
    (hB : ∀ (η : ι → S) (s : S), |f η - f (Function.update η i s)| ≤ B) :
    deltaAt i f ≤ B :=
  Finset.sup'_le _ _ fun q _ => hB q.1 q.2

/-- The pair form: two configurations agreeing off `i` differ by at most
`deltaAt i f`. -/
theorem abs_sub_le_deltaAt {i : ι} (f : (ι → S) → ℝ) {η η' : ι → S}
    (h : ∀ j, j ≠ i → η j = η' j) : |f η - f η'| ≤ deltaAt i f := by
  have hη' : η' = Function.update η i (η' i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [update_self']
    · rw [update_other _ _ _ hj]
      exact (h j hj).symm
  rw [hη']
  exact abs_sub_update_le_deltaAt i f η (η' i)

/-- `deltaAt i f` vanishes exactly when `f` does not depend on the coordinate
`i` (the vanishing clause promised by the charter's ladder for D-3a). -/
theorem deltaAt_eq_zero_iff (i : ι) (f : (ι → S) → ℝ) :
    deltaAt i f = 0 ↔ ∀ (η : ι → S) (s : S), f (Function.update η i s) = f η := by
  constructor
  · intro h0 η s
    have h1 := abs_sub_update_le_deltaAt i f η s
    rw [h0] at h1
    have h2 : |f η - f (Function.update η i s)| = 0 :=
      le_antisymm h1 (abs_nonneg _)
    have h3 : f η - f (Function.update η i s) = 0 := abs_eq_zero.mp h2
    linarith
  · intro hind
    refine le_antisymm (deltaAt_le i f fun η s => ?_) (deltaAt_nonneg i f)
    rw [hind η s, sub_self, abs_zero]

/-! ## §2  Oscillation bounds from pairwise bounds -/

/-- A pairwise bound on differences bounds the oscillation.  Stated for an
arbitrary finite nonempty type, so it serves both the single-site sections here
and the full configuration space in `DobrushinComparison.lean`. -/
theorem osc_le_of_pairwise {T : Type*} [Fintype T] [Nonempty T]
    {g : T → ℝ} {B : ℝ} (h : ∀ s t : T, g s - g t ≤ B) : osc g ≤ B := by
  unfold osc
  rw [sub_le_iff_le_add]
  refine Finset.sup'_le _ _ fun s _ => ?_
  have hinf : g s - B ≤ Finset.univ.inf' Finset.univ_nonempty g :=
    Finset.le_inf' _ _ fun t _ => by linarith [h s t]
  linarith

/-- The section of `f` along coordinate `i` at base `η` oscillates at most
`deltaAt i f`.  This is the bridge through which the analytic ingredient of
D-3a (`abs_sum_sub_le_tv_mul_osc`) enters the key lemma. -/
theorem osc_section_le_deltaAt (i : ι) (f : (ι → S) → ℝ) (η : ι → S) :
    osc (fun s => f (Function.update η i s)) ≤ deltaAt i f := by
  refine osc_le_of_pairwise fun s t => ?_
  have hpair := abs_sub_update_le_deltaAt i f (Function.update η i s) t
  rw [update_update] at hpair
  calc f (Function.update η i s) - f (Function.update η i t)
      ≤ |f (Function.update η i s) - f (Function.update η i t)| := le_abs_self _
    _ ≤ deltaAt i f := hpair

/-! ## §3  Algebra of `deltaAt`, for the assembly downstream -/

theorem deltaAt_const (i : ι) (c : ℝ) : deltaAt i (fun _ => c) = 0 :=
  le_antisymm (deltaAt_le i _ fun _ _ => by rw [sub_self, abs_zero])
    (deltaAt_nonneg i _)

theorem deltaAt_add_le (i : ι) (f g : (ι → S) → ℝ) :
    deltaAt i (fun η => f η + g η) ≤ deltaAt i f + deltaAt i g := by
  refine deltaAt_le i _ fun η s => ?_
  have hsplit : f η + g η - (f (Function.update η i s) + g (Function.update η i s))
      = (f η - f (Function.update η i s)) + (g η - g (Function.update η i s)) := by
    ring
  rw [hsplit]
  calc |(f η - f (Function.update η i s)) + (g η - g (Function.update η i s))|
      ≤ |f η - f (Function.update η i s)| + |g η - g (Function.update η i s)| :=
        abs_add _ _
    _ ≤ deltaAt i f + deltaAt i g :=
        add_le_add (abs_sub_update_le_deltaAt i f η s)
          (abs_sub_update_le_deltaAt i g η s)

theorem deltaAt_sum_le (i : ι) {β : Type*} (s : Finset β)
    (F : β → (ι → S) → ℝ) :
    deltaAt i (fun η => ∑ b ∈ s, F b η) ≤ ∑ b ∈ s, deltaAt i (F b) := by
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact le_of_eq (deltaAt_const i 0)
  | cons b s hb ih =>
      simp only [Finset.sum_cons]
      calc deltaAt i (fun η => F b η + ∑ c ∈ s, F c η)
          ≤ deltaAt i (F b) + deltaAt i (fun η => ∑ c ∈ s, F c η) :=
            deltaAt_add_le i _ _
        _ ≤ deltaAt i (F b) + ∑ c ∈ s, deltaAt i (F c) := by linarith [ih]

/-- Division by a positive constant is monotone; derived here from
multiplication so that no library name for the division form is consumed. -/
theorem div_le_div_of_nonneg_right' {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hc))

theorem deltaAt_div_le (i : ι) (f : (ι → S) → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    deltaAt i (fun η => f η / c) ≤ deltaAt i f / c := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0, div_zero]
    refine deltaAt_le i _ fun η s => ?_
    simp only [div_zero, sub_self, abs_zero]
    exact le_refl 0
  · refine deltaAt_le i _ fun η s => ?_
    have hsplit : f η / c - f (Function.update η i s) / c
        = (f η - f (Function.update η i s)) / c := by ring
    rw [hsplit, abs_div, abs_of_pos hcpos]
    exact div_le_div_of_nonneg_right' (abs_sub_update_le_deltaAt i f η s) hcpos

/-! ## §4  D-3b — the single-site conditional operator -/

/-- The single-site conditional operator: average `f` over the value at `i`,
with the single-site kernel `p i η`. -/
noncomputable def condExp (p : ι → (ι → S) → S → ℝ) (i : ι)
    (f : (ι → S) → ℝ) : (ι → S) → ℝ :=
  fun η => ∑ s, p i η s * f (Function.update η i s)

/-- Locality: the kernel at `i` does not see the value at `i`.  Consumed as a
hypothesis everywhere; abbreviated here so that its exact content is written
once. -/
def KernelLocal (p : ι → (ι → S) → S → ℝ) : Prop :=
  ∀ (i : ι) (η η' : ι → S), (∀ j, j ≠ i → η j = η' j) → p i η = p i η'

/-- The conditional at `i` of any observable is invariant under moving the
coordinate `i`: the SEMANTIC half of D-3c, resting on locality alone. -/
theorem condExp_update_self {p : ι → (ι → S) → S → ℝ} (hloc : KernelLocal p)
    (i : ι) (f : (ι → S) → ℝ) (η : ι → S) (s : S) :
    condExp p i f (Function.update η i s) = condExp p i f η := by
  unfold condExp
  have hp : p i (Function.update η i s) = p i η :=
    hloc i _ _ fun j hj => update_other η i s hj
  rw [hp]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [update_update]

/-- **D-3c, the vanishing clause.**  `δᵢ (Eᵢ f) = 0`, semantically, with no
matrix in sight. -/
theorem deltaAt_condExp_self {p : ι → (ι → S) → S → ℝ} (hloc : KernelLocal p)
    (i : ι) (f : (ι → S) → ℝ) : deltaAt i (condExp p i f) = 0 :=
  (deltaAt_eq_zero_iff i _).mpr fun η s => condExp_update_self hloc i f η s

/-- Conditioning does not increase range: pointwise, `Eᵢ f` lies between any
uniform bounds of `f`.  Used by the comparison module to keep iterates
bounded. -/
theorem condExp_le_of_le {p : ι → (ι → S) → S → ℝ}
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (i : ι) {f : (ι → S) → ℝ} {M : ℝ} (hM : ∀ η, f η ≤ M) (η : ι → S) :
    condExp p i f η ≤ M := by
  unfold condExp
  calc ∑ s, p i η s * f (Function.update η i s)
      ≤ ∑ s, p i η s * M :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hM _) (hp0 i η s)
    _ = M := by rw [← Finset.sum_mul, hp1 i η, one_mul]

/-! ## §5  D-3c — THE KEY LEMMA -/

/-- **D-3c, the transport clause.**  For `k ≠ i`, a single-site update at `i`
moves the oscillation at `k` by at most the oscillation already there plus the
influence of `k` on the conditional at `i` times the oscillation at `i`:

    δₖ (Eᵢ f) ≤ δₖ f + C i k · δᵢ f.

`Cik` is consumed as a MAJORANT of the influence — the declared orientation of
`judge_dobrushin_d3b.py`: changing `η` only at `k` moves the conditional AT `i`
by at most `Cik` in total variation.  The proof splits the difference into a
transported term (paying `δₖ f`) and a kernel-variation term, which is a
zero-sum signed mass tested against a section of `f` — exactly the analytic
ingredient `abs_sum_sub_le_tv_mul_osc` of D-3a. -/
theorem deltaAt_condExp_le {p : ι → (ι → S) → S → ℝ}
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    {i k : ι} (hki : k ≠ i) {Cik : ℝ}
    (hC : ∀ η η' : ι → S, (∀ j, j ≠ k → η j = η' j) →
      TV (p i η) (p i η') ≤ Cik)
    (f : (ι → S) → ℝ) :
    deltaAt k (condExp p i f) ≤ deltaAt k f + Cik * deltaAt i f := by
  refine deltaAt_le k _ fun η s => ?_
  set η' := Function.update η k s with hη'def
  have hagree : ∀ j, j ≠ k → η j = η' j := fun j hj =>
    (update_other η k s hj).symm
  -- decompose the difference into transport + kernel variation
  have hdecomp : condExp p i f η - condExp p i f η'
      = (∑ t, p i η t * (f (Function.update η i t) - f (Function.update η' i t)))
        + ∑ t, (p i η t - p i η' t) * f (Function.update η' i t) := by
    unfold condExp
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  -- the transported pair agrees off k (here k ≠ i is load-bearing)
  have hpair : ∀ t : S, ∀ j, j ≠ k →
      Function.update η i t j = Function.update η' i t j := by
    intro t j hj
    by_cases hji : j = i
    · subst hji
      rw [update_self', update_self']
    · rw [update_other _ _ _ hji, update_other _ _ _ hji]
      exact hagree j hj
  -- term 1: transport
  have h1 : |∑ t, p i η t * (f (Function.update η i t) - f (Function.update η' i t))|
      ≤ deltaAt k f := by
    calc |∑ t, p i η t * (f (Function.update η i t) - f (Function.update η' i t))|
        ≤ ∑ t, |p i η t * (f (Function.update η i t) - f (Function.update η' i t))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t, p i η t * |f (Function.update η i t) - f (Function.update η' i t)| :=
          Finset.sum_congr rfl fun t _ => by
            rw [abs_mul, abs_of_nonneg (hp0 i η t)]
      _ ≤ ∑ t, p i η t * deltaAt k f :=
          Finset.sum_le_sum fun t _ =>
            mul_le_mul_of_nonneg_left
              (abs_sub_le_deltaAt f (hpair t)) (hp0 i η t)
      _ = deltaAt k f := by rw [← Finset.sum_mul, hp1 i η, one_mul]
  -- term 2: kernel variation, through the analytic ingredient of D-3a
  have h2 : |∑ t, (p i η t - p i η' t) * f (Function.update η' i t)|
      ≤ Cik * deltaAt i f := by
    have hmass : ∑ t, p i η t = ∑ t, p i η' t := by
      rw [hp1 i η, hp1 i η']
    have hTV : TV (p i η) (p i η') ≤ Cik := hC η η' hagree
    have hosc : osc (fun t => f (Function.update η' i t)) ≤ deltaAt i f :=
      osc_section_le_deltaAt i f η'
    calc |∑ t, (p i η t - p i η' t) * f (Function.update η' i t)|
        ≤ TV (p i η) (p i η') * osc (fun t => f (Function.update η' i t)) :=
          abs_sum_sub_le_tv_mul_osc hmass _
      _ ≤ Cik * deltaAt i f :=
          mul_le_mul hTV hosc (osc_nonneg _) (le_trans (TV_nonneg _ _) hTV)
  calc |condExp p i f η - condExp p i f η'|
      = |(∑ t, p i η t * (f (Function.update η i t) - f (Function.update η' i t)))
          + ∑ t, (p i η t - p i η' t) * f (Function.update η' i t)| := by
        rw [hdecomp]
    _ ≤ |∑ t, p i η t * (f (Function.update η i t) - f (Function.update η' i t))|
          + |∑ t, (p i η t - p i η' t) * f (Function.update η' i t)| := abs_add _ _
    _ ≤ deltaAt k f + Cik * deltaAt i f := add_le_add h1 h2

/-! ## §6  The matrix form — the ONLY statement that assumes `C i i = 0` -/

/-- **D-3c, matrix form** (charter Amendment 1).  With `C i i = 0` declared,
both clauses assemble into a single coordinatewise bound:

    δₖ (Eᵢ f) ≤ (if k = i then 0 else δₖ f) + C i k · δᵢ f.

The diagonal hypothesis enters here and nowhere else. -/
theorem deltaAt_condExp_le_matrix {p : ι → (ι → S) → S → ℝ}
    (hp0 : ∀ i η s, 0 ≤ p i η s) (hp1 : ∀ i η, ∑ s, p i η s = 1)
    (hloc : KernelLocal p)
    (C : Matrix ι ι ℝ) (hCdiag : ∀ i, C i i = 0)
    (hC : ∀ i k, k ≠ i → ∀ η η' : ι → S, (∀ j, j ≠ k → η j = η' j) →
      TV (p i η) (p i η') ≤ C i k)
    (i k : ι) (f : (ι → S) → ℝ) :
    deltaAt k (condExp p i f)
      ≤ (if k = i then 0 else deltaAt k f) + C i k * deltaAt i f := by
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl, hCdiag, zero_mul, add_zero]
    exact le_of_eq (deltaAt_condExp_self hloc _ f)
  · rw [if_neg hk]
    exact deltaAt_condExp_le hp0 hp1 hk (hC i k hk) f

end Dobrushin

end YangMills.OS
