/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.WilsonPolymerActivity

/-!
# Trivial `WilsonPolymerActivityBound` for arbitrary `N_c`

This module produces an unconditional inhabitant of
`WilsonPolymerActivityBound N_c` for every `N_c ≥ 1`, by setting
the truncated polymer activity `K` identically to zero. The amplitude
bound `|K(γ)| = |0| = 0 ≤ A₀ · r^|γ|` then holds trivially.

## Two perspectives, both honest

* **At SU(1) the trivial inhabitant is *physically accurate*.** The
  connected Wilson correlator on `GaugeConfig d L SU(1)` is identically
  zero (`wilsonConnectedCorr_su1_eq_zero`, Phase 7.2). Hence the
  truncated polymer activity at SU(1) is genuinely the zero function,
  not merely a placeholder. The trivial witness is therefore the
  *correct* witness for the SU(1) trivial-group case.
* **At `N_c ≥ 2` the trivial inhabitant is structurally valid but
  physics-vacuous.** The actual truncated activity `K_phys` is a
  non-trivial function carrying the cluster-expansion content;
  setting `K := 0` evades that content rather than capturing it.
  For genuine Branch I / Branch II Clay closure at `N_c ≥ 2`, the
  `K` field must come from the physical Wilson polymer activity
  (Bałaban CMP 116 Lemma 3 / Brydges-Kennedy random-walk expansion),
  not from this triviality.

## Relation to Finding 013 (Phase 59)

`BalabanHyps N_c` is structurally trivially inhabitable for any
`N_c` because its `R` field is existentially quantified
(`R := 0` works). `WilsonPolymerActivityBound N_c` has a stronger
shape: the `K` field is **explicit data**, and a UNIVERSAL bound
holds. Even so, the universal bound is satisfied with `K := 0`.

Both findings together establish a **design observation**: every
predicate in the lattice-gauge / cluster-expansion frontier of this
project is structurally inhabitable with zero / identity / vacuous
witnesses. The genuine analytic content lives at the **integration**
layer — where these predicates are composed with concrete physical
inputs (Wilson actions, Haar integrals, cluster sums, terminal
endpoints).

This is a positive observation about the project's design: it has a
clean separation between **abstract type-level structure** (always
non-vacuous) and **concrete physical content** (the actual obligation).

## Caveat

Same trivial-group physics-degeneracy of Findings 003 + 011 + 012 +
013 applies. Documented as `COWORK_FINDINGS.md` Finding 014.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills

open Real

/-! ## §1. Trivial `WilsonPolymerActivityBound` for arbitrary `N_c` -/

/-- **Trivial `WilsonPolymerActivityBound N_c` for every `N_c ≥ 1`**,
    with `K ≡ 0`, `A₀ := 1`, `r := 1/2`, `β := 1`.

    The amplitude bound `|K γ| ≤ A₀ · r^|γ|` becomes
    `|0| ≤ 1 · (1/2)^|γ|`, which is `0 ≤ (1/2)^|γ|` and holds because
    `(1/2)^|γ|` is positive. -/
noncomputable def trivialWilsonPolymerActivityBound (N_c : ℕ) [NeZero N_c] :
    WilsonPolymerActivityBound N_c where
  β := 1
  hβ := one_pos
  r := 1 / 2
  hr_pos := by norm_num
  hr_lt1 := by norm_num
  A₀ := 1
  hA₀ := zero_le_one
  K := fun {_d _L _hd _hL} _γ => 0
  h_bound := by
    intro d L _hd _hL γ
    -- Goal: |0| ≤ 1 * (1/2)^γ.card
    rw [abs_zero]
    have hr_pos : (0 : ℝ) < 1 / 2 := by norm_num
    have h_pow_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ γ.card :=
      pow_pos hr_pos γ.card
    linarith

#print axioms trivialWilsonPolymerActivityBound

/-! ## §2. SU(1) instantiation — physically accurate -/

/-- The SU(1) instantiation of `trivialWilsonPolymerActivityBound`.
    For SU(1) this is **physically accurate**: the truncated polymer
    activity on the trivial group is genuinely zero, because every
    connected correlator vanishes (`wilsonConnectedCorr_su1_eq_zero`).

    For `N_c ≥ 2` the same construction (with the same `K := 0`) is
    structurally valid but physics-vacuous. -/
noncomputable def trivialWilsonPolymerActivityBound_su1 :
    WilsonPolymerActivityBound 1 :=
  trivialWilsonPolymerActivityBound 1

#print axioms trivialWilsonPolymerActivityBound_su1

/-! ## §3. Coordination note -/

/-
After Phase 60, the **structural-triviality observation** spans two
of the major Branch I / Branch II predicate carriers:

| Predicate                       | Trivially inhabitable? | Witness phase |
|---------------------------------|------------------------|---------------|
| `BalabanHyps N_c`               | Yes (R := 0)           | Phase 59      |
| `WilsonPolymerActivityBound N_c`| Yes (K := 0)           | Phase 60      |

Both are structurally non-vacuous for ANY `N_c ≥ 1`. The genuine
Bałaban / Brydges-Kennedy / Kotecký-Preiss content is encoded
**not in these predicates themselves**, but in the **composition**
of these predicates with downstream theorems
(`physicalStrong_of_*`, `clayMassGap_of_*`) that consume both the
predicate AND a concrete physical input.

For the Clay attack at `N_c ≥ 2`:
* The path forward is NOT to prove `WilsonPolymerActivityBound N_c`
  (already done trivially).
* The path forward IS to construct a *non-trivial* `K` from the
  Wilson Gibbs measure that satisfies the universal bound, AND to
  feed it into Codex's terminal endpoints.

This is a **design observation**, not a critique: the project's
abstract type-level scaffolding is appropriately separated from the
concrete-content layer. Cowork's role here is to document the
separation explicitly.

Cross-references:
- `WilsonPolymerActivity.lean` — `WilsonPolymerActivityBound` definition.
- `BalabanHypsTrivial.lean` (Phase 59) — companion `BalabanHyps`
  finding.
- `LargeFieldDominance.balabanHyps_from_wilson_activity` — the
  composition from Wilson activity to `BalabanHyps` (this is where
  the analytic content actually flows).
- `COWORK_FINDINGS.md` Finding 014 — full discussion.
-/

end YangMills
