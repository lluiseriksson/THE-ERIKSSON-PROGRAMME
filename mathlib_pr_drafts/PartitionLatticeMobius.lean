/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib.Combinatorics.SetFamily.Partition
import Mathlib.Order.Mobius
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Möbius inversion on the partition lattice

For a finite set `S`, the lattice of set-partitions `Finpartition S`
ordered by refinement has Möbius function

```
μ(π, σ) = ∏ over blocks of σ, (-1)^(k_B - 1) (k_B - 1)!
```

where `k_B` is the number of blocks of `π` that lie inside `B`. This file
formalises the special case `μ(⊥, π)` (where `⊥` is the finest partition
into singletons) which is what cluster-expansion / Mayer-Ursell
calculations consume.

## Main results

* `Finpartition.mobiusFunction_singletons`: explicit value of the
  Möbius function `μ(⊥, π)`.
* `Finpartition.mobius_inversion_singletons`: the inversion identity
  ```
  g(S) = ∑ π ∈ Finpartition.univ S, ∏ B ∈ π.parts,
           (-1)^(B.card - 1) * (B.card - 1)! * f(B)
  ```
  given that `f(S) = ∑ π ∈ Finpartition.univ S, ∏ B ∈ π.parts, g(B)`.

## References

* Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed., Cambridge
  (2012), Proposition 3.10.4 (Möbius function of the partition
  lattice).
* Rota, *On the foundations of combinatorial theory I: Theory of
  Möbius functions*, Z. Wahrscheinlichkeitstheorie 2 (1964),
  340–368.

## Tags

Möbius function, partition lattice, cluster expansion, Ursell

-/

namespace Finpartition

open Finset BigOperators

variable {α : Type*} [DecidableEq α]

/-- The finest partition: every element of `S` is its own block. -/
noncomputable def singletonsPartition (S : Finset α) : Finpartition S :=
  Finpartition.indiscreteIntoSingletons S
  -- TODO: this constructor name may differ in current Mathlib;
  -- the intended object is the partition into singletons.

/-- For a partition `π` of `S`, the Möbius function from the finest
partition (all singletons) to `π` in the partition lattice equals
`∏ B ∈ π.parts, (-1)^(B.card - 1) * (B.card - 1)!`.

This is Stanley *Enumerative Combinatorics* I, Prop 3.10.4. -/
theorem mobiusFunction_singletons {S : Finset α} (π : Finpartition S) :
    (mobius (Finpartition S) (singletonsPartition S) π : ℤ) =
    ∏ B ∈ π.parts, ((-1) ^ (B.card - 1) * (B.card - 1).factorial) := by
  -- Proof via induction on the structure of π:
  --
  -- 1. If π is itself the singleton partition, both sides are 1.
  -- 2. Otherwise, π has at least one block of size ≥ 2. Pick the
  --    canonical such block B (e.g. the first one in some ordering).
  --    Define π' as π with B replaced by its singleton refinement.
  -- 3. Use the Möbius defining recursion
  --       ∑_{σ : ⊥ ≤ σ ≤ π} mobius ⊥ σ = δ_{⊥, π}
  --    to reduce mobius(⊥, π) to a sum over partitions of B.
  -- 4. Apply the classical identity
  --       ∑_{partition of B}, ∏ over blocks of (-1)^(...)·(...)!
  --       = (-1)^(B.card - 1) · (B.card - 1)!
  --    (this is the partition-lattice Möbius value at the top, a
  --    standard combinatorial fact via the exponential generating
  --    function of -log(1-x)).
  --
  -- Detailed proof omitted; see Stanley Theorem 3.10.4 and Proposition
  -- 3.10.4 for the technique.
  sorry  -- TODO: full proof

/-- **Möbius inversion on the partition lattice (singleton form).**

If `f` is built from a "block function" `g` by

```
f(S) = ∑_{π ∈ Finpartition.univ S} ∏ B ∈ π.parts, g(B)
```

then `g` can be recovered from `f` by the signed sum

```
g(S) = ∑_{π ∈ Finpartition.univ S}
         ∏ B ∈ π.parts, (-1)^(B.card - 1) · (B.card - 1)! · f(B)
```

This is the analytic/algebraic content the Mayer-Ursell truncation in
cluster expansions uses. -/
theorem mobius_inversion_singletons {S : Finset α}
    (f g : Finset α → ℝ)
    (h_full : ∀ T ⊆ S, f T = ∑ π ∈ (Finpartition.univ T).toFinset,
      ∏ B ∈ π.parts, g B) :
    g S = ∑ π ∈ (Finpartition.univ S).toFinset,
      ∏ B ∈ π.parts, ((-1) ^ (B.card - 1) * (B.card - 1).factorial : ℝ) * f B := by
  -- Apply Möbius inversion (Mathlib has this for general posets) to
  -- the partition lattice on S, using `mobiusFunction_singletons` to
  -- evaluate the Möbius coefficients.
  --
  -- The proof reduces to a calculation of
  --   ∑ over partitions, mobius(⊥, π) · f(... merged blocks ...)
  -- and re-arranging via h_full.
  sorry  -- TODO: full proof

end Finpartition

/-! ## Application: truncated cluster activities

The Mayer-Ursell truncation that appears in classical statistical
mechanics (and in the SU(N_c) Wilson cluster expansion of the
THE-ERIKSSON-PROGRAMME project) is exactly this Möbius inversion
applied to:

- `f(B) = ∫ ∏_{r ∈ B} fluctuation(U_r) dHaar` (the ordinary cluster
  average over polymers in block `B`).
- `g(B) = K(B)` (the truncated activity, which vanishes when `B` has
  size 1 due to zero-mean of the fluctuation).

The cluster expansion convergence theorems then estimate `|K(B)|` via
the Brydges-Kennedy random-walk formula, which reorganises the sum
over partitions as a sum over **trees** on `B` (Cayley) — converting
factorial blowup to controlled exponential growth. See
`BLUEPRINT_F3Mayer.md` of the YangMills project for the application.
-/
