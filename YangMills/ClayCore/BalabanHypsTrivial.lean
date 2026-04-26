/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.BalabanH1H2H3
import YangMills.ClayCore.PolymerLocality

/-!
# Unconditional `BalabanHyps N_c` for arbitrary `N_c` (trivial witness)

This module produces a fully unconditional inhabitant of
`BalabanHyps N_c` **for every `N_c ≥ 1`**, not just SU(1). The
construction uses the existential witness `R := 0` for both
`h_sf : ∀ n, ∃ R, 0 ≤ R ∧ R ≤ E₀ · g²· exp(-κn)` and
`h_lf : ∀ n, ∃ R, 0 ≤ R ∧ R ≤ exp(-p₀) · exp(-κn)`.

## Why this is a structural observation, not Branch II progress

The `BalabanHyps` predicate as currently formalised quantifies the
small-field bound and large-field decay **existentially over `R`**.
The existential is satisfied by `R := 0` for every `n`, regardless
of the gauge group, because the upper bounds are products of
positive quantities (and `0 ≤ 0 ≤ E₀ · g² · exp(-κn)` holds for
any positive `E₀`, `g`, `κ`).

So `BalabanHyps N_c` is **structurally non-vacuous for every `N_c`**.
The non-trivial **analytic** content of Bałaban RG lives in:

* `WilsonPolymerActivityBound` (`WilsonPolymerActivity.lean`).
* `LargeFieldProfile` and `LargeFieldActivityBound`
  (`LargeFieldDominance.lean`).
* The `WilsonPolymerActivityBound → BalabanHyps` chain in
  `LargeFieldDominance.balabanHyps_from_wilson_activity` (which
  carries the actual Bałaban R values).

The fact that the trivial `R := 0` witness inhabits `BalabanHyps`
means the predicate, in isolation, does **not** encode the Bałaban
content. It is a packaging type for the (E₀, g, κ, p₀) parameters
plus existential R bounds that downstream consumers extract and
combine.

## Parameter choice

We pick `E₀ := 4`, `κ := 1`, `g := 1/2`, `p₀ := 1`. Then
`E₀ · g² = 4 · (1/2)² = 1` and `exp(-p₀) = exp(-1) ≤ 1`, so the
cross-compatibility `exp(-p₀) ≤ E₀ · g²` is `exp(-1) ≤ 1`, which
follows from `Real.exp_le_one_iff`.

## Importance for the Clay programme

This is a **negative structural finding** dressed as a positive
witness:

* **Positive**: `BalabanHyps` is non-vacuous for every `N_c`.
* **Negative**: that doesn't mean Bałaban RG is "done at SU(1)".
  The actual analytic obligation sits in
  `WilsonPolymerActivityBound` (still hypothesis-conditioned for
  `N_c ≥ 2`).

For the strict Clay attack, this means: future Branch II work
should target `WilsonPolymerActivityBound` directly, NOT
`BalabanHyps`, since the latter is already trivially inhabitable.

Documented as `COWORK_FINDINGS.md` Finding 013.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills

open Real

/-! ## §1. Trivial `BalabanH1` and `BalabanH2` inhabitants for any `N_c` -/

/-- A canonical `BalabanH1 N_c` with `E₀ := 4`, `κ := 1`, `g := 1/2`, and
    `R := 0` for every `n` (trivially satisfying the existential).

    The choice `E₀ = 4` makes `E₀ · g² = 1`, which gives the cross-
    compatibility `exp(-1) ≤ 1` needed in `unconditional_BalabanHyps_trivial`. -/
noncomputable def unconditional_BalabanH1 (N_c : ℕ) [NeZero N_c] :
    BalabanH1 N_c where
  E0 := 4
  hE0 := by norm_num
  kappa := 1
  hkappa := one_pos
  g_bar := 1 / 2
  hg_pos := by norm_num
  hg_lt1 := by norm_num
  h_sf := fun n => by
    refine ⟨0, le_refl 0, ?_⟩
    -- Goal: 0 ≤ 4 * (1/2)^2 * exp(-1 * n)
    have h1 : (0 : ℝ) ≤ (4 : ℝ) * (1 / 2 : ℝ) ^ 2 := by norm_num
    exact mul_nonneg h1 (Real.exp_nonneg _)

#print axioms unconditional_BalabanH1

/-- A canonical `BalabanH2 N_c` with `p₀ := 1`, `κ := 1`, `g := 1/2`, and
    `R := 0` for every `n`. -/
noncomputable def unconditional_BalabanH2 (N_c : ℕ) [NeZero N_c] :
    BalabanH2 N_c where
  p0 := 1
  hp0 := one_pos
  kappa := 1
  hkappa := one_pos
  g_bar := 1 / 2
  hg_pos := by norm_num
  h_lf := fun n => by
    refine ⟨0, le_refl 0, ?_⟩
    -- Goal: 0 ≤ exp(-1) * exp(-1 * n)
    exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)

#print axioms unconditional_BalabanH2

/-! ## §2. Cross-compatibility -/

/-- Cross-compatibility for the canonical (E₀=4, g=1/2, p₀=1) choice:
    `exp(-1) ≤ 4 · (1/2)² = 1`. Follows from `Real.exp_le_one_iff` (since
    `-1 ≤ 0`). -/
private lemma unconditional_compat :
    Real.exp (-(1 : ℝ)) ≤ (4 : ℝ) * (1 / 2 : ℝ) ^ 2 := by
  have h1 : Real.exp (-(1 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h2 : (4 : ℝ) * (1 / 2 : ℝ) ^ 2 = 1 := by norm_num
  rw [h2]; exact h1

/-! ## §3. The full unconditional `BalabanHyps N_c` witness -/

/-- **Unconditional inhabitant of `BalabanHyps N_c` for every `N_c ≥ 1`**.

    Constructed via `balabanHyps_of_h1_h2` from `unconditional_BalabanH1`
    and `unconditional_BalabanH2`. All consistency conditions
    (`hg_eq`, `hk_eq`, `hlf_le`) close by `rfl` / `unconditional_compat`. -/
noncomputable def unconditional_BalabanHyps_trivial
    (N_c : ℕ) [NeZero N_c] : BalabanHyps N_c :=
  balabanHyps_of_h1_h2
    (unconditional_BalabanH1 N_c) (unconditional_BalabanH2 N_c)
    (rfl) (rfl) unconditional_compat

#print axioms unconditional_BalabanHyps_trivial

/-! ## §4. SU(1) instantiation (joins the SU(1) ladder) -/

/-- The SU(1) instantiation of `unconditional_BalabanHyps_trivial`. -/
noncomputable def unconditional_BalabanHyps_su1 : BalabanHyps 1 :=
  unconditional_BalabanHyps_trivial 1

#print axioms unconditional_BalabanHyps_su1

/-! ## §5. Coordination note -/

/-
This file produces the first **N_c-agnostic** unconditional witness in
the project — every prior unconditional witness from Phases 7.2 + 43–58
is SU(1)-specific. The reason it is N_c-agnostic is structural: the
`BalabanHyps N_c` data type does NOT depend on the gauge group beyond
the typeclass `[NeZero N_c]`, and the existential `R` bound is
satisfiable by `R := 0` for all positive parameter choices.

This is a **structural** finding and surfaces a design observation:
the analytic Bałaban content lives elsewhere (in
`WilsonPolymerActivityBound` and `LargeFieldDominance.balabanHyps_from_wilson_activity`),
not in `BalabanHyps` itself.

For the strict Clay attack at `N_c ≥ 2`, future Branch II work should
target the `WilsonPolymerActivityBound` layer directly.

Cross-references:
- `BalabanH1H2H3.lean` — `BalabanHyps` definitions.
- `PolymerLocality.lean` — `balabanHyps_of_h1_h2` constructor used here.
- `LargeFieldDominance.lean` — analytic-content carrier (where Branch II
  work should focus).
- `COWORK_FINDINGS.md` Finding 013 — full discussion of the structural
  observation.
-/

end YangMills
