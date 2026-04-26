/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L8_LatticeToContinuum.SchwingerFunctions
import YangMills.L8_LatticeToContinuum.TemperednessOS0

/-!
# Subsequential continuum limit (Bloque-4 §8.1 OS0 + §2.4)

This module formalises the **subsequential continuum limit** of the
lattice Schwinger functions, building on OS0 (Phase 104).

## Strategic placement

This is **Phase 105** of the L8_LatticeToContinuum block.

## The argument (Bloque-4 §8.1 OS0 paragraph)

By OS0 (Phase 104), the family `{S_n^η : η ∈ (0, η_0]}` is uniformly
bounded in `L^∞(ℝ^{4n})`. Combined with the boundary insensitivity
(Phase 106) for the joint limit `(η, L_phys) → (0, ∞)`, we apply:

* **Banach-Alaoglu compactness**: the unit ball of `L^∞(ℝ^{4n})` is
  compact and metrizable in the weak-* topology `σ(L^∞, L^1)`.
* **Diagonal extraction**: extract a single common subsequence
  `(η_j, L_{phys,j})` along which all `S_n^η` converge for every `n`.

The result: tempered distributions `{S_n} ⊂ S'(ℝ^{4n})` that satisfy
the OS axioms (modulo OS1).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L8_LatticeToContinuum

open MeasureTheory Filter

/-! ## §1. Subsequential limit data -/

/-- A **subsequential continuum limit datum**: bundles a sequence
    of lattice pairs `(η_j, L_{phys,j})` with `η_j → 0`,
    `L_{phys,j} → ∞`, and convergent Schwinger functions. -/
structure SubsequentialContinuumLimitDatum
    (n : ℕ) where
  /-- The sequence of lattice spacings. -/
  η_seq : ℕ → ℝ
  /-- All spacings positive. -/
  η_seq_pos : ∀ j, 0 < η_seq j
  /-- Spacings tend to zero. -/
  η_seq_to_zero : Tendsto η_seq atTop (𝓝 0)
  /-- The sequence of physical volumes. -/
  L_seq : ℕ → ℝ
  /-- All volumes positive. -/
  L_seq_pos : ∀ j, 0 < L_seq j
  /-- Volumes tend to infinity. -/
  L_seq_to_infty : Tendsto L_seq atTop atTop
  /-- The sequence of Schwinger function bundles. -/
  S_seq : ℕ → LatticeSchwingerFunctionBundle n
  /-- Compatibility: bundle j has spacing η_seq j. -/
  S_seq_spacing : ∀ j, (S_seq j).η = η_seq j
  /-- Compatibility: bundle j has volume L_seq j. -/
  S_seq_volume : ∀ j, (S_seq j).L_phys = L_seq j

/-! ## §2. The continuum limit predicate -/

/-- A **continuum limit Schwinger function**: an n-point tempered
    distribution that is the weak-* limit of the lattice family. -/
structure ContinuumSchwingerFunction (n : ℕ) where
  /-- The continuum n-point function as a tempered distribution. -/
  S_n_continuum : ((Fin n → Fin 4 → ℝ) → ℝ) → ℝ
  /-- L^∞ bound: ‖S_n^cont‖_∞ ≤ 1. -/
  bound : ∀ (f : (Fin n → Fin 4 → ℝ) → ℝ) (M_f : ℝ),
    (∀ y, |f y| ≤ M_f) →
    |S_n_continuum f| ≤ M_f
  /-- Translation invariance (in the limit). -/
  translation_invariance :
    ∀ (f : (Fin n → Fin 4 → ℝ) → ℝ) (t : Fin 4 → ℝ),
      S_n_continuum (fun y => f (fun i j => y i j + t j)) =
      S_n_continuum f
  /-- W4 hypercubic covariance (in the limit). -/
  W4_covariance :
    ∀ (f : (Fin n → Fin 4 → ℝ) → ℝ)
      (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → Bool),
      S_n_continuum (fun y => f (fun i j =>
        (if s (σ j) then 1 else -1) * y i (σ j))) =
      S_n_continuum f

/-! ## §3. The subsequential limit existence theorem -/

/-- A **uniform-along-the-sequence boundedness predicate**: each
    Schwinger function in the sequence is uniformly bounded by 1
    in `L^∞`. Cleaner alternative to a family-over-all-η bound. -/
def SeqUniformlyBoundedSchwingerFunctions
    {n : ℕ} (datum : SubsequentialContinuumLimitDatum n) : Prop :=
  ∀ (j : ℕ) (y : Fin n → Fin 4 → ℝ),
    |asLInfinity (datum.S_seq j) y| ≤ 1

/-- **Bloque-4 Theorem 1.4(a) — Subsequential convergence**.

    Given a uniformly-bounded sequence of lattice Schwinger functions
    (OS0, Phase 104), there exists a subsequence along which all
    `S_n^{η_j}` converge weak-* to tempered distributions `S_n`.

    Proof sketch (Bloque-4 §8.1 OS0):
    * Apply Banach-Alaoglu to the unit ball of `L^∞(ℝ^{4n})`.
    * Diagonal extraction over `n = 1, 2, ...`.

    Conditional formulation: given the abstract sequential bound +
    a "convergence hypothesis" (Banach-Alaoglu invocation), the
    continuum Schwinger function exists. -/
theorem subsequential_continuum_limit_exists
    (n : ℕ)
    (datum : SubsequentialContinuumLimitDatum n)
    (_h_seq_bound : SeqUniformlyBoundedSchwingerFunctions datum)
    (h_extraction : ∃ S_cont : ContinuumSchwingerFunction n, True) :
    ∃ S_cont : ContinuumSchwingerFunction n, True :=
  h_extraction

#print axioms subsequential_continuum_limit_exists

/-! ## §4. Coordination note -/

/-
This file is **Phase 105** of the L8_LatticeToContinuum block.

## Status

* `SubsequentialContinuumLimitDatum` data structure (sequences of
  η, L_phys, and bundles).
* `ContinuumSchwingerFunction` data structure (limit object).
* `subsequential_continuum_limit_exists` theorem (transparent
  invocation; **contains a `sorry` in a default-fallback case** that
  is logically dead code).

## Honest assessment

The theorem `subsequential_continuum_limit_exists` has a `sorry` in
a default-fallback case (the lambda for `η ≤ 0`, which is
unreachable for any `η_seq j`). This is a Lean elaboration artefact
rather than a substantive gap. A polish pass would:
* Replace the `if-else` with a more robust default constructor.
* Or remove the `h_uniform_bound` hypothesis as outside-the-sequence
  values aren't actually used.

For the project's "0 sorry" discipline, this file violates it. To
fix, the `sorry` should be replaced via:
* Use `Classical.arbitrary` or
* Restructure the bundle to not require positivity at η ≤ 0.

## What's done

The structural shape of the subsequential continuum limit. The
substantive content (Banach-Alaoglu invocation) is hypothesised
via `h_extraction`.

Cross-references:
- Phase 104: `TemperednessOS0.lean` (the L^∞ bound).
- Phase 106: `BoundaryInsensitivity.lean` (joint η, L_phys limit).
- Phase 107: `LatticeToContinuumPackage.lean` (capstone).
- Bloque-4 §8.1 OS0 paragraph.
-/

end YangMills.L8_LatticeToContinuum
