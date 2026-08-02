/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinOscillation

/-!
# D-3c — SOURCE, NOT RESULT

Charter: `docs/DOBRUSHIN-D3-CHARTER.md`, rung D-3c, with Amendment 1 fixing
where the zero diagonal is allowed to enter.  Gate `J9`
(`scripts/judge_dobrushin_d3.py`) was run and committed before this file
(`docs/audits/DOBRUSHIN-D3-GATES-20260802.md`): zero violations over
16 + 256 + 256 Boolean observables.  **J9 licenses ATTEMPTING this rung.  It
proves nothing** — it tests `|S| = 2`, `|ι| ≤ 3` and one explicit kernel against
a statement quantified over all finite systems and all real observables.

## The claim

For a single-site conditional `E i` built from a local kernel,

```
    deltaAt i (E i f) = 0
    deltaAt k (E i f) ≤ deltaAt k f + C i k * deltaAt i f        (k ≠ i)
```

so the Dobrushin matrix is exactly what acts on oscillation vectors under one
site update.  Everything downstream (D-3d, D-3e) is iteration.

## Boundaries, fixed before the proof and not to be relaxed by it

* **`C i k` is a MAJORANT of the influence `k → i`, never assumed minimal.**  The
  hypothesis is `TV (p i ·) ≤ C i k`, an inequality.  This is the same
  distinction that cost two paper versions for `tanh |J|`.
* **Orientation is printed, not inferred:** `C i k` is the influence of site `k`
  on the conditional at site `i`.  It appears transposed in the matrix assembly
  for exactly that reason, and the coordinate formula is proved rather than left
  to emerge from a simplification.
* **Semantic locality is a declared hypothesis:** configurations agreeing off `i`
  give the same conditional at `i`.  `deltaAt i (E i f) = 0` is a theorem of its
  own resting on that and on nothing else — not a by-product of `simp`.
* **`C i i = 0` enters ONLY the matrix assembly** (Amendment 1).  The local
  transport lemma never sees it.
* **The `A + B` split stays visible.**  `A` is controlled by `deltaAt k f`
  through normalisation; `B` is a difference of two conditionals and consumes
  exactly one already-formalised endpoint of D-3a,
  `abs_sum_sub_le_tv_mul_osc`.  `DobrushinGruss` (Popoviciu) is NOT imported and
  is not a dependency.

## Status

`SOURCE, NOT RESULT`.  Elaboration under the owner's named authorisation for
`lake env lean YangMills/OS/DobrushinComparison.lean`.  A green run means source
that elaborated on recorded bytes; it does not confer `Formalized`, which is
conferred only by the external A/B audit protocol that closed D-3a.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : Type*} [Fintype S] [Nonempty S]

/-! ## §1  Oscillation in a single coordinate

The charter states the convention as a supremum over pairs agreeing off `i`.
It is defined here over `(η, s, t)` because `Function.update` is the workhorse of
every proof below, and the two are proved equal in `abs_sub_le_deltaAt` — the
declared convention and the used one must not drift apart. -/

/-- The oscillation of `f` in the single coordinate `i`. -/
noncomputable def deltaAt (i : ι) (f : (ι → S) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun q : (ι → S) × S × S =>
      |f (Function.update q.1 i q.2.1) - f (Function.update q.1 i q.2.2)|)

/-- Every single-coordinate replacement is bounded by `deltaAt`. -/
theorem abs_sub_update_le (i : ι) (f : (ι → S) → ℝ) (η : ι → S) (s t : S) :
    |f (Function.update η i s) - f (Function.update η i t)| ≤ deltaAt i f := by
  unfold deltaAt
  exact Finset.le_sup'
    (fun q : (ι → S) × S × S =>
      |f (Function.update q.1 i q.2.1) - f (Function.update q.1 i q.2.2)|)
    (Finset.mem_univ (η, s, t))

/-- **The convention agrees with the charter's.**  Two configurations that agree
off `i` are bounded by `deltaAt i f`, which is how the charter states it. -/
theorem abs_sub_le_deltaAt (i : ι) (f : (ι → S) → ℝ) {η η' : ι → S}
    (h : ∀ j, j ≠ i → η j = η' j) : |f η - f η'| ≤ deltaAt i f := by
  have h1 : Function.update η i (η i) = η := Function.update_eq_self i η
  have h2 : Function.update η i (η' i) = η' := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact h j hj
  calc |f η - f η'|
      = |f (Function.update η i (η i)) - f (Function.update η i (η' i))| := by
        rw [h1, h2]
    _ ≤ deltaAt i f := abs_sub_update_le i f η (η i) (η' i)

theorem deltaAt_nonneg (i : ι) (f : (ι → S) → ℝ) : 0 ≤ deltaAt i f := by
  obtain ⟨s⟩ := ‹Nonempty S›
  exact le_trans (abs_nonneg _) (abs_sub_update_le i f (fun _ => s) s s)

/-! ## §2  The single-site conditional -/

/-- The charter's `E i f`: average `f` over the value at site `i` under the
single-site kernel `p`. -/
noncomputable def siteExp (p : ι → (ι → S) → S → ℝ) (i : ι)
    (f : (ι → S) → ℝ) (η : ι → S) : ℝ :=
  ∑ s, p i η s * f (Function.update η i s)

/-- **SEMANTIC LOCALITY** — the conditional at `i` does not see the old value at
`i`.  Carried as a hypothesis, never as an axiom. -/
def LocalKernel (p : ι → (ι → S) → S → ℝ) : Prop :=
  ∀ (i : ι) (η η' : ι → S), (∀ j, j ≠ i → η j = η' j) → p i η = p i η'

/-! ## §3  Step 4 of the ladder: the conditional kills its own coordinate -/

/-- **`deltaAt i (E i f) = 0`.**  A theorem in its own right, resting on the
declared exterior locality and on nothing stronger.  `C` does not appear. -/
theorem deltaAt_siteExp_self (p : ι → (ι → S) → S → ℝ) (hloc : LocalKernel p)
    (i : ι) (f : (ι → S) → ℝ) : deltaAt i (siteExp p i f) = 0 := by
  have hconst : ∀ (η : ι → S) (s : S), siteExp p i f (Function.update η i s)
      = siteExp p i f η := by
    intro η s
    have hp : p i (Function.update η i s) = p i η := by
      refine hloc i _ _ fun j hj => ?_
      exact Function.update_of_ne hj _ _
    unfold siteExp
    rw [hp]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Function.update_idem]
  refine le_antisymm ?_ (deltaAt_nonneg i _)
  refine Finset.sup'_le _ _ fun q _ => ?_
  rw [hconst q.1 q.2.1, hconst q.1 q.2.2, sub_self, abs_zero]

/-! ## §4  Step 5: the key transport inequality

The `A + B` split is written out rather than folded into a `calc`, so that the
place where D-3a is consumed is visible at a glance. -/

/-- **THE KEY LEMMA.**  For `k ≠ i`, one site update transports oscillation
exactly as the Dobrushin matrix says.

`hC` is an INEQUALITY: `C i k` majorises the influence of `k` on the conditional
at `i`.  Minimality is never used and must never be added.

**`LocalKernel` is NOT a hypothesis here.**  The first elaboration carried it,
following the charter's ladder, and the linter reported it unused.  It is: the
off-diagonal transport needs only nonnegativity, normalisation and the majorant.
Semantic locality is what `deltaAt_siteExp_self` needs, and only that.  Removing
it makes this statement strictly stronger, and leaving it in would have been a
theorem quietly claiming less than it proves. -/
theorem deltaAt_siteExp_le (p : ι → (ι → S) → S → ℝ) (C : ι → ι → ℝ)
    (hnn : ∀ i η s, 0 ≤ p i η s)
    (hsum : ∀ i η, ∑ s, p i η s = 1)
    (hC : ∀ (i k : ι), k ≠ i → ∀ (η : ι → S) (s t : S),
      TV (p i (Function.update η k s)) (p i (Function.update η k t)) ≤ C i k)
    {i k : ι} (hk : k ≠ i) (f : (ι → S) → ℝ) :
    deltaAt k (siteExp p i f) ≤ deltaAt k f + C i k * deltaAt i f := by
  refine Finset.sup'_le _ _ fun q _ => ?_
  obtain ⟨η, s, t⟩ := q
  set a : ι → S := Function.update η k s with ha
  set b : ι → S := Function.update η k t with hb
  set P : S → ℝ := p i a with hP
  set Q : S → ℝ := p i b with hQ
  set F : S → ℝ := fun u => f (Function.update a i u) with hF
  set G : S → ℝ := fun u => f (Function.update b i u) with hG
  -- the decomposition, kept explicit
  have hsplit : (∑ u, P u * F u) - (∑ u, Q u * G u)
      = (∑ u, P u * (F u - G u)) + ∑ u, (P u - Q u) * G u := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  -- PART A: same kernel, two configurations differing only at k
  have hA : |∑ u, P u * (F u - G u)| ≤ deltaAt k f := by
    have hbound : ∀ u : S, |F u - G u| ≤ deltaAt k f := by
      intro u
      have h1 : Function.update a i u = Function.update (Function.update η i u) k s := by
        rw [ha]; exact (Function.update_comm (Ne.symm hk) u s η).symm
      have h2 : Function.update b i u = Function.update (Function.update η i u) k t := by
        rw [hb]; exact (Function.update_comm (Ne.symm hk) u t η).symm
      rw [hF, hG]
      simp only [h1, h2]
      exact abs_sub_update_le k f (Function.update η i u) s t
    calc |∑ u, P u * (F u - G u)|
        ≤ ∑ u, |P u * (F u - G u)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ u, P u * |F u - G u| := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [abs_mul, abs_of_nonneg (hnn i a u)]
      _ ≤ ∑ u, P u * deltaAt k f :=
          Finset.sum_le_sum fun u _ =>
            mul_le_mul_of_nonneg_left (hbound u) (hnn i a u)
      _ = deltaAt k f := by rw [← Finset.sum_mul, hsum i a, one_mul]
  -- PART B: two kernels, and this is where D-3a is consumed
  have hoscG : osc G ≤ deltaAt i f := by
    obtain ⟨u₀, -, hu₀⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty) G
    obtain ⟨v₀, -, hv₀⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty) G
    have : osc G = f (Function.update b i u₀) - f (Function.update b i v₀) := by
      unfold osc; rw [hu₀, hv₀]
    rw [this]
    exact le_trans (le_abs_self _) (abs_sub_update_le i f b u₀ v₀)
  have hB : |∑ u, (P u - Q u) * G u| ≤ C i k * deltaAt i f := by
    have htv : |∑ u, (P u - Q u) * G u| ≤ TV P Q * osc G := by
      refine abs_sum_sub_le_tv_mul_osc ?_ G
      rw [hP, hQ, hsum i a, hsum i b]
    refine le_trans htv ?_
    refine mul_le_mul (hC i k hk η s t) hoscG (osc_nonneg G) ?_
    exact le_trans (TV_nonneg P Q) (hC i k hk η s t)
  -- assemble
  have hsum2 : |(∑ u, P u * (F u - G u)) + ∑ u, (P u - Q u) * G u|
      ≤ deltaAt k f + C i k * deltaAt i f := by
    rw [abs_le] at hA hB ⊢
    exact ⟨by linarith [hA.1, hB.1], by linarith [hA.2, hB.2]⟩
  have hgoal : |siteExp p i f a - siteExp p i f b| ≤ deltaAt k f + C i k * deltaAt i f := by
    unfold siteExp
    rw [hsplit]
    exact hsum2
  exact hgoal

/-! ## §5  Step 7: the matrix form, and the ONLY place `C i i = 0` is used -/

/-- The single-update matrix `B i = I - eᵢeᵢᵀ + Cᵀ eᵢeᵢᵀ`.  The transpose is
what makes the influence `k → i` land in the `k`-th coordinate. -/
noncomputable def Bupd (C : Matrix ι ι ℝ) (i : ι) : Matrix ι ι ℝ :=
  1 - Matrix.single i i 1 + C.transpose * Matrix.single i i 1

/-- **The coordinate formula, PROVED and not left to a simplification.**  This is
where the orientation becomes visible: the `k`-th coordinate carries `C i k`,
the influence of `k` on `i`. -/
theorem Bupd_mulVec (C : Matrix ι ι ℝ) (i : ι) (v : ι → ℝ) (k : ι) :
    (Bupd C i).mulVec v k = v k - (if k = i then v i else 0) + C i k * v i := by
  have hsingle : (Matrix.single i i (1:ℝ)).mulVec v = Function.update (0 : ι → ℝ) i (v i) := by
    rw [Matrix.single_mulVec, one_mul]
  have hprod : (C.transpose * Matrix.single i i (1:ℝ)).mulVec v k = C i k * v i := by
    rw [← Matrix.mulVec_mulVec, hsingle]
    have hexp : C.transpose.mulVec (Function.update (0 : ι → ℝ) i (v i)) k
        = ∑ l, C.transpose k l * (Function.update (0 : ι → ℝ) i (v i)) l := rfl
    rw [hexp, Finset.sum_eq_single i]
    · rw [Function.update_self, Matrix.transpose_apply]
    · intro l _ hl
      rw [Function.update_of_ne hl, Pi.zero_apply, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  unfold Bupd
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply, hprod, hsingle]
  by_cases hki : k = i
  · subst hki; simp
  · rw [Function.update_of_ne hki, Pi.zero_apply, if_neg hki]

/-- **The matrix form of the key lemma.**  `C i i = 0` is a hypothesis HERE and
nowhere else: `deltaAt_siteExp_le` and `deltaAt_siteExp_self` are stated without
it, so any dominating interdependence matrix drives them. -/
theorem deltaVec_siteExp_le (p : ι → (ι → S) → S → ℝ) (C : Matrix ι ι ℝ)
    (hnn : ∀ i η s, 0 ≤ p i η s)
    (hsum : ∀ i η, ∑ s, p i η s = 1)
    (hloc : LocalKernel p)
    (hC : ∀ (i k : ι), k ≠ i → ∀ (η : ι → S) (s t : S),
      TV (p i (Function.update η k s)) (p i (Function.update η k t)) ≤ C i k)
    (hdiag : ∀ i, C i i = 0)
    (i : ι) (f : (ι → S) → ℝ) (k : ι) :
    deltaAt k (siteExp p i f) ≤ (Bupd C i).mulVec (fun j => deltaAt j f) k := by
  rw [Bupd_mulVec]
  by_cases hki : k = i
  · subst hki
    rw [deltaAt_siteExp_self p hloc k f, if_pos rfl, hdiag k]
    simp
  · rw [if_neg hki]
    have := deltaAt_siteExp_le p C hnn hsum hC hki f
    linarith

/-! ## §6  Non-vacuity — the hypotheses are jointly satisfiable

Hard rule 3 of the repository: never state a conditional theorem without a
witness that its premises can all hold at once.  A conditional whose hypotheses
are contradictory is vacuously true and says nothing.

**This witness is DEGENERATE and is labelled as such.**  It takes `C = 0`, so it
establishes joint satisfiability of every hypothesis — including `C i i = 0` and
the majorant condition — but it does NOT exercise the influence term: with
`C = 0` the conclusion of the key lemma reads `deltaAt k (E i f) ≤ deltaAt k f`,
which is the contraction statement alone.  A non-degenerate witness, with some
`C i k > 0` actually attained, is owed and is not supplied here.  Saying so is
the point; a witness that quietly covers less than the theorem needs would be
worse than none. -/

/-- The uniform single-site kernel: it ignores the configuration entirely. -/
noncomputable def uniformKernel : ι → (ι → S) → S → ℝ :=
  fun _ _ _ => (Fintype.card S : ℝ)⁻¹

omit [Fintype ι] [DecidableEq ι] [Nonempty S] in
theorem uniformKernel_local : LocalKernel (uniformKernel (ι := ι) (S := S)) :=
  fun _ _ _ _ => rfl

omit [Fintype ι] [DecidableEq ι] in
theorem uniformKernel_nonneg (i : ι) (η : ι → S) (s : S) :
    0 ≤ uniformKernel i η s := by
  unfold uniformKernel
  positivity

omit [Fintype ι] [DecidableEq ι] in
theorem uniformKernel_sum (i : ι) (η : ι → S) :
    ∑ s, uniformKernel (ι := ι) i η s = 1 := by
  unfold uniformKernel
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

omit [Fintype ι] [Nonempty S] in
theorem uniformKernel_tv (i k : ι) (η : ι → S) (s t : S) :
    TV (uniformKernel (ι := ι) i (Function.update η k s))
       (uniformKernel (ι := ι) i (Function.update η k t)) = 0 := by
  unfold TV uniformKernel
  simp

omit [Fintype ι] in
/-- **Every hypothesis of `deltaVec_siteExp_le` holds simultaneously.**  With
`C = 0`, hence degenerate in the sense declared above. -/
theorem deltaVec_hypotheses_satisfiable :
    ∃ (p : ι → (ι → S) → S → ℝ) (C : Matrix ι ι ℝ),
      (∀ i η s, 0 ≤ p i η s) ∧
      (∀ i η, ∑ s, p i η s = 1) ∧
      LocalKernel p ∧
      (∀ (i k : ι), k ≠ i → ∀ (η : ι → S) (s t : S),
        TV (p i (Function.update η k s)) (p i (Function.update η k t)) ≤ C i k) ∧
      (∀ i, C i i = 0) := by
  refine ⟨uniformKernel, 0, uniformKernel_nonneg, uniformKernel_sum,
    uniformKernel_local, ?_, fun i => rfl⟩
  intro i k _ η s t
  rw [uniformKernel_tv i k η s t]
  exact le_of_eq rfl

end Dobrushin

end YangMills.OS
