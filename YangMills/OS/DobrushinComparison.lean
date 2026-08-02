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

The one-site update is governed by the coordinatewise majorant `B i` constructed
from `C`.  `C` is not claimed to be the exact, minimal or optimal influence, and
what acts on oscillation vectors is `B i`, not `C` alone.

This is the LOCAL TRANSPORT INPUT.  D-3d must iterate it, and D-3e must still
convert that iteration into the covariance comparison estimate — the charter
separates those two rungs and so does this module.

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

## MANIFEST — every named declaration, listed literally

The authority is this list of NAMES, not a total and not a `grep`.  The audit
driver must be exactly this manifest.  Three earlier versions of this section
quoted totals — 9, then 19, then 38 with classes summing to 28 — and every one
was wrong, because a total is remembered while a list is checked.

**Load-bearing and interface — 11**

```
 1  deltaAt_siteExp_self            endpoint
 2  deltaAt_siteExp_le              endpoint  (THE key lemma)
 3  Bupd_mulVec                     endpoint  (coordinate formula, orientation)
 4  deltaVec_siteExp_le             endpoint  (matrix form, uses C i i = 0)
 5  deltaAt_eq_deltaAtOff           convention equivalence
 6  abs_sub_update_le               oscillation auxiliary
 7  abs_sub_le_deltaAt              oscillation auxiliary
 8  deltaAt_nonneg                  oscillation auxiliary
 9  C_nonneg_of_majorant            D-3d interface, OFF-DIAGONAL only
10  Bupd_mulVec_mono                D-3d interface, needs global nonnegativity
11  Bupd_mulVec_mono_of_majorant    D-3d interface, assembles both sources
```

**Headline witnesses — 4**

```
12  deltaVec_hypotheses_satisfiable   satisfiability, DEGENERATE (C = 0)
13  Witness.hypotheses_hold           satisfiability, NON-degenerate (C 0 1 ≠ 0)
14  Witness.pw_tv_attained            the MAJORANT is attained
15  Witness.deltaAt_siteExp_attained  the TRANSPORT bound is attained
```

**Supporting witness lemmas — 16**

```
16  uniformKernel_local        24  two_cases
17  uniformKernel_nonneg       25  pw_nonneg
18  uniformKernel_sum          26  pw_sum
19  uniformKernel_tv           27  Cw_diag
20  fw_update_zero             28  pw_tv
21  fw_update_one              29  siteExp_pw
22  pw_local                   30  deltaAt_zero_fw
23  deltaAt_one_fw             31  deltaAt_one_siteExp
```

**Definitions — 9**

```
deltaAt   deltaAtOff   siteExp   LocalKernel   Bupd
uniformKernel   Witness.pw   Witness.Cw   Witness.fw
```

`11 + 4 + 16 = 31` theorems, plus `9` definitions: **40 named declarations**.

Note on measurement: a count taken by grepping for lines beginning with
`theorem` once reported one theorem too many, because a line of PROSE inside a
docstring began with that word.  A guard that cannot tell code from
documentation has produced a wrong inventory twice in this repository, and that
is why the manifest above is a list of names.

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
every proof below.  The two forms are not merely claimed to agree: `deltaAtOff`
is the charter's form and `deltaAt_eq_deltaAtOff` proves the EQUALITY of the two
suprema.  `abs_sub_le_deltaAt` gives only the domination direction, which is what
the rest of the module consumes; an earlier version of this paragraph cited it as
if it proved the equality, which it does not. -/

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

open scoped Classical in
/-- **The charter's form of the seminorm**: a supremum over PAIRS agreeing off
`i`.  Pairs that do not agree contribute `0`, which cannot raise the supremum
because the diagonal already contributes `0`. -/
noncomputable def deltaAtOff (i : ι) (f : (ι → S) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun q : (ι → S) × (ι → S) =>
      if (∀ j, j ≠ i → q.1 j = q.2 j) then |f q.1 - f q.2| else 0)

/-- **The two conventions are EQUAL, not merely comparable.**  The module defines
`deltaAt` over updates and the charter states it over exterior-agreeing pairs;
this is the theorem that stops them drifting apart. -/
theorem deltaAt_eq_deltaAtOff (i : ι) (f : (ι → S) → ℝ) :
    deltaAt i f = deltaAtOff i f := by
  classical
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun q _ => ?_
    obtain ⟨η, s, t⟩ := q
    have hagree : ∀ j, j ≠ i → (Function.update η i s) j = (Function.update η i t) j := by
      intro j hj
      rw [Function.update_of_ne hj, Function.update_of_ne hj]
    refine le_trans ?_ (Finset.le_sup'
      (fun q : (ι → S) × (ι → S) =>
        if (∀ j, j ≠ i → q.1 j = q.2 j) then |f q.1 - f q.2| else 0)
      (Finset.mem_univ (Function.update η i s, Function.update η i t)))
    rw [if_pos hagree]
  · refine Finset.sup'_le _ _ fun q _ => ?_
    by_cases hq : ∀ j, j ≠ i → q.1 j = q.2 j
    · rw [if_pos hq]
      exact abs_sub_le_deltaAt i f hq
    · rw [if_neg hq]
      exact deltaAt_nonneg i f

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

/-- **THE KEY LEMMA.**  For `k ≠ i`, one-site updating satisfies the
coordinatewise Dobrushin majorant.  Not an identity, and not optimality: the
statement is `≤`, and `C i k` is an upper bound on the influence, so nothing here
says `c i k = C i k`.

`hC` is an INEQUALITY: `C i k` majorises the influence of `k` on the conditional
at `i`.  Minimality is never used and must never be added.

**`LocalKernel` is NOT a hypothesis here.**  The first elaboration carried it,
following the charter's ladder, and the linter reported it unused.  It is: the
off-diagonal transport needs only nonnegativity, normalisation and the majorant.
Semantic locality is what `deltaAt_siteExp_self` needs, and only that.  Removing
it makes this statement strictly stronger, and leaving it in would have been
a theorem quietly claiming less than it proves. -/
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

**This section supplies only the DEGENERATE satisfiability witness.**  It takes
`C = 0`, so it establishes joint satisfiability of every hypothesis — including
`C i i = 0` and the majorant condition — but it does NOT exercise the influence
term: with `C = 0` the conclusion of the key lemma reads
`deltaAt k (E i f) ≤ deltaAt k f`, the contraction statement alone.

**A non-degenerate sharpness witness is supplied separately in §8**, with
`C 0 1 = 1/2` nonzero, attained as a total variation and attained again as
equality in the key lemma.  An earlier version of this paragraph said such a
witness was owed and not supplied, and stayed in the file after §8 paid the
debt. -/

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

/-! ## §7  The interface D-3d needs, and it is not automatic

Iterating the one-site bound requires that `B i` preserve the order on
oscillation vectors.  That does not follow from the coordinate formula alone; it
needs `C` entrywise nonnegative, and entrywise nonnegativity has TWO sources
which must not be run together:

* **`hC` supplies the OFF-DIAGONAL part only.**  It is quantified under `k ≠ i`,
  so `TV ≥ 0` yields `0 ≤ C i k` exactly for `k ≠ i` and says nothing whatever
  about `C i i`.
* **`hdiag` supplies the diagonal**, which is zero and hence nonnegative.

An earlier version of this paragraph said nonnegativity is forced by `hC`, with
no such split.  That is false on the diagonal.
`Bupd_mulVec_mono_of_majorant` below assembles the two sources, so that D-3d
never has to reconstruct a global hypothesis this module wrongly attributed to
one of them. -/

omit [Fintype ι] in
/-- `hC` already forces `C` nonnegative off the diagonal: `TV ≥ 0`. -/
theorem C_nonneg_of_majorant (p : ι → (ι → S) → S → ℝ) (C : ι → ι → ℝ)
    (hC : ∀ (i k : ι), k ≠ i → ∀ (η : ι → S) (s t : S),
      TV (p i (Function.update η k s)) (p i (Function.update η k t)) ≤ C i k)
    {i k : ι} (hk : k ≠ i) : 0 ≤ C i k := by
  obtain ⟨s⟩ := ‹Nonempty S›
  exact le_trans (TV_nonneg _ _) (hC i k hk (fun _ => s) s s)

/-- **`B i` preserves the componentwise order** when `C` is entrywise
nonnegative.  This is the step that makes D-3d an iteration; without it, chaining
the one-site bound is not licensed. -/
theorem Bupd_mulVec_mono (C : Matrix ι ι ℝ) (i : ι)
    (hCnn : ∀ j k, 0 ≤ C j k) {v w : ι → ℝ} (hvw : ∀ j, v j ≤ w j) (k : ι) :
    (Bupd C i).mulVec v k ≤ (Bupd C i).mulVec w k := by
  rw [Bupd_mulVec, Bupd_mulVec]
  by_cases hki : k = i
  · subst hki
    rw [if_pos rfl, if_pos rfl]
    nlinarith [hCnn k k, hvw k]
  · rw [if_neg hki, if_neg hki]
    nlinarith [hCnn i k, hvw k, hvw i]

/-- **The consumer D-3d should call.**  It takes the two hypotheses that already
exist — the majorant condition and the zero diagonal — and produces order
preservation, assembling entrywise nonnegativity from its two distinct sources
rather than demanding it as a fresh global assumption. -/
theorem Bupd_mulVec_mono_of_majorant (p : ι → (ι → S) → S → ℝ) (C : Matrix ι ι ℝ)
    (hC : ∀ (i k : ι), k ≠ i → ∀ (η : ι → S) (s t : S),
      TV (p i (Function.update η k s)) (p i (Function.update η k t)) ≤ C i k)
    (hdiag : ∀ i, C i i = 0)
    {v w : ι → ℝ} (hvw : ∀ j, v j ≤ w j) (i k : ι) :
    (Bupd C i).mulVec v k ≤ (Bupd C i).mulVec w k := by
  have hCnn : ∀ j l, 0 ≤ C j l := by
    intro j l
    by_cases hjl : l = j
    · rw [hjl]
      exact le_of_eq (hdiag j).symm
    · exact C_nonneg_of_majorant p C hC hjl
  exact Bupd_mulVec_mono C i hCnn hvw k

/-! ## §8  A NON-DEGENERATE witness: the key lemma is ATTAINED

`deltaVec_hypotheses_satisfiable` shows the premises are consistent, but with
`C = 0` it never exercises the influence term.  This section supplies the missing
one: two sites, two states, `C 0 1 = 1/2` genuinely nonzero and genuinely
attained, so the inequality of `deltaAt_siteExp_le` is an EQUALITY here.

It also pins the ORIENTATION empirically inside Lean: the nonzero entry is
`C 0 1`, the influence of site `1` on the conditional at site `0`, and it is site
`1`'s oscillation that responds. -/

namespace Witness

/-- Site `0` copies site `1` with probability `3/4`; site `1` is uniform. -/
noncomputable def pw : Fin 2 → (Fin 2 → Fin 2) → Fin 2 → ℝ :=
  fun i η s => if i = 0 then (if s = η 1 then 3/4 else 1/4) else 1/2

/-- Only `C 0 1` is nonzero, and it equals the total variation actually produced. -/
noncomputable def Cw : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i k => if i = 0 ∧ k = 1 then 1/2 else 0

/-- The observable: the indicator that site `0` is in state `1`. -/
def fw : (Fin 2 → Fin 2) → ℝ := fun η => if η 0 = 1 then 1 else 0

theorem fw_update_zero (η : Fin 2 → Fin 2) (s : Fin 2) :
    fw (Function.update η 0 s) = if s = 1 then 1 else 0 := by
  unfold fw; rw [Function.update_self]

theorem fw_update_one (η : Fin 2 → Fin 2) (s : Fin 2) :
    fw (Function.update η 1 s) = fw η := by
  unfold fw; rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]

theorem pw_local : LocalKernel pw := by
  intro i η η' h
  funext s
  unfold pw
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi]
    have : η 1 = η' 1 := h 1 (by rw [hi]; decide)
    rw [this]
  · rw [if_neg hi, if_neg hi]

theorem two_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide

theorem pw_nonneg (i : Fin 2) (η : Fin 2 → Fin 2) (s : Fin 2) : 0 ≤ pw i η s := by
  unfold pw
  by_cases hi : i = 0
  · rw [if_pos hi]
    by_cases hs : s = η 1
    · rw [if_pos hs]; norm_num
    · rw [if_neg hs]; norm_num
  · rw [if_neg hi]; norm_num

theorem pw_sum (i : Fin 2) (η : Fin 2 → Fin 2) : ∑ s, pw i η s = 1 := by
  unfold pw
  rw [Fin.sum_univ_two]
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi]
    rcases two_cases (η 1) with h1 | h1 <;> rw [h1] <;> norm_num
  · rw [if_neg hi, if_neg hi]; norm_num

theorem Cw_diag (i : Fin 2) : Cw i i = 0 := by
  unfold Cw; fin_cases i <;> norm_num

theorem pw_tv (i k : Fin 2) (hk : k ≠ i) (η : Fin 2 → Fin 2) (s t : Fin 2) :
    TV (pw i (Function.update η k s)) (pw i (Function.update η k t)) ≤ Cw i k := by
  rcases two_cases i with hi | hi <;> rcases two_cases k with hk0 | hk0
  · exact absurd (hk0.trans hi.symm) hk
  · subst hi; subst hk0
    unfold TV pw Cw
    rw [Fin.sum_univ_two]
    simp only [Function.update_self, and_self]
    rcases two_cases s with hs | hs <;> rcases two_cases t with ht | ht <;>
      rw [hs, ht] <;> norm_num
  · subst hi; subst hk0
    unfold TV pw Cw
    rw [Fin.sum_univ_two]
    norm_num
  · exact absurd (hk0.trans hi.symm) hk

theorem siteExp_pw (η : Fin 2 → Fin 2) :
    siteExp pw 0 fw η = if η 1 = 1 then (3 : ℝ)/4 else 1/4 := by
  have h0 : fw (Function.update η 0 0) = 0 := by rw [fw_update_zero]; norm_num
  have h1 : fw (Function.update η 0 1) = 1 := by rw [fw_update_zero]; norm_num
  unfold siteExp
  rw [Fin.sum_univ_two, h0, h1, mul_zero, mul_one, zero_add]
  unfold pw
  rw [if_pos rfl]
  by_cases h : η 1 = 1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun hc => h hc.symm]

theorem deltaAt_zero_fw : deltaAt 0 fw = 1 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun q _ => ?_
    obtain ⟨η, s, t⟩ := q
    rw [fw_update_zero, fw_update_zero]
    by_cases hs : s = 1 <;> by_cases ht : t = 1 <;> norm_num [hs, ht]
  · have h := abs_sub_update_le (0 : Fin 2) fw (fun _ => 0) 1 0
    rw [fw_update_zero, fw_update_zero] at h
    norm_num at h
    exact h

theorem deltaAt_one_fw : deltaAt 1 fw = 0 := by
  refine le_antisymm ?_ (deltaAt_nonneg 1 fw)
  refine Finset.sup'_le _ _ fun q _ => ?_
  obtain ⟨η, s, t⟩ := q
  rw [fw_update_one, fw_update_one, sub_self, abs_zero]

theorem deltaAt_one_siteExp : deltaAt 1 (siteExp pw 0 fw) = 1/2 := by
  have key : ∀ (η : Fin 2 → Fin 2) (s : Fin 2),
      siteExp pw 0 fw (Function.update η 1 s) = if s = 1 then (3:ℝ)/4 else 1/4 := by
    intro η s
    rw [siteExp_pw, Function.update_self]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun q _ => ?_
    obtain ⟨η, s, t⟩ := q
    rw [key, key]
    by_cases hs : s = 1 <;> by_cases ht : t = 1 <;> norm_num [hs, ht]
  · have h := abs_sub_update_le (1 : Fin 2) (siteExp pw 0 fw) (fun _ => 0) 1 0
    rw [key, key] at h
    norm_num at h
    exact h

/-- **THE SHARPNESS WITNESS.**  With a genuinely nonzero influence, the key lemma
holds with EQUALITY: `1/2 = 0 + (1/2) * 1`.  So `C 0 1 = 1/2` is not a bound
above the truth, and the orientation `C 0 1 = influence of 1 on 0` is the one
that compiles. -/
theorem deltaAt_siteExp_attained :
    deltaAt 1 (siteExp pw 0 fw) = deltaAt 1 fw + Cw 0 1 * deltaAt 0 fw := by
  rw [deltaAt_one_siteExp, deltaAt_one_fw, deltaAt_zero_fw]
  unfold Cw
  norm_num

/-- **The influence majorant is ATTAINED.**  `C 0 1` is not a bound above the
truth: the total variation actually produced by flipping site `1` equals it
exactly.  This is a DIFFERENT sharpness from `deltaAt_siteExp_attained` — that
one says the transport inequality is attained, this one says the majorant is —
and until now only the first was a theorem while the second lived in prose. -/
theorem pw_tv_attained :
    TV (pw 0 (Function.update (fun _ => (0 : Fin 2)) 1 0))
       (pw 0 (Function.update (fun _ => (0 : Fin 2)) 1 1)) = Cw 0 1 := by
  unfold TV pw Cw
  rw [Fin.sum_univ_two]
  simp only [Function.update_self, and_self]
  norm_num

/-- The witness satisfies every hypothesis of `deltaVec_siteExp_le`, with a
NONZERO influence matrix. -/
theorem hypotheses_hold :
    (∀ i η s, 0 ≤ pw i η s) ∧
    (∀ i η, ∑ s, pw i η s = 1) ∧
    LocalKernel pw ∧
    (∀ (i k : Fin 2), k ≠ i → ∀ (η : Fin 2 → Fin 2) (s t : Fin 2),
      TV (pw i (Function.update η k s)) (pw i (Function.update η k t)) ≤ Cw i k) ∧
    (∀ i, Cw i i = 0) ∧ Cw 0 1 ≠ 0 :=
  ⟨pw_nonneg, pw_sum, pw_local, pw_tv, Cw_diag, by unfold Cw; norm_num⟩

end Witness

end Dobrushin

end YangMills.OS
