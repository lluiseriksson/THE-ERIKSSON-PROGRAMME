/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Ursell

/-!
# KP2b (attack) — the cluster sum, right-hand side of the Mayer expansion

The Kotecký–Preiss / Mayer cluster expansion asserts that, in finite volume,

  `log Ξ(Λ) = ∑_{n ≥ 1} (1/n!) ∑_{X : Fin n → Polymer} φ(X) · ∏ᵢ z(Xᵢ)`,

equivalently `Ξ(Λ) = exp(clusterSum)`, where `φ = ursell` is the Mayer coefficient
(`YangMills/KP/Ursell.lean`).  This file defines the **right-hand side** as a Lean
object — the first concrete step of KP2b — for a finite polymer system (`Fintype
Polymer`), where each inner tuple-sum is finite.

The outer sum over cluster size `n` is genuinely infinite, so `clusterSum` is a
`tsum`; its **convergence** (under the KP smallness criterion) and the **identity**
`log Ξ = clusterSum` are the hard content of KP2b — the months-long crux
(`docs/kp-cluster-expansion-plan.md`).  This file does not prove them; it pins the
object so the identity can be stated and attacked.

Recall (already verified, `Ursell.lean`): `φ` vanishes off clusters
(`ursell_eq_zero_of_not_isCluster`), so only genuine clusters contribute to the
inner sum — the cluster sum really is a sum over clusters.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped Classical BigOperators

variable (P : PolymerSystem)

/-- The **cluster sum** (right-hand side of the Mayer expansion), for a finite
polymer system:
`∑' n, (1/(n+1)!) · ∑_{X : Fin (n+1) → Polymer} φ(X) · ∏ᵢ z(Xᵢ)`.
Indexing by `n+1` makes every term a nonempty tuple.  Only clusters contribute
(`ursell_eq_zero_of_not_isCluster`).  The target identity is `Ξ = exp(clusterSum)`. -/
noncomputable def clusterSum [Fintype P.Polymer] : ℂ :=
  ∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
    ∑ X : Fin (n + 1) → P.Polymer, (ursell P X : ℂ) * ∏ i, P.activity (X i)

/-- **E2 (sum level): the cluster sum is supported exactly on clusters.**  In each
inner tuple-sum, the non-cluster tuples contribute `0` (`ursell_eq_zero_of_not_isCluster`),
so the sum over all tuples equals the sum restricted to clusters.  This makes precise
that `clusterSum` is genuinely a *sum over clusters*, the index set of the Mayer
expansion — the first verified reduction toward the identity `Ξ = exp(clusterSum)`. -/
theorem clusterSum_eq_sum_clusters [Fintype P.Polymer] :
    clusterSum P = ∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
      ∑ X ∈ Finset.univ.filter (fun X : Fin (n + 1) → P.Polymer => IsCluster P X),
        (ursell P X : ℂ) * ∏ i, P.activity (X i) := by
  classical
  unfold clusterSum
  refine tsum_congr (fun n => ?_)
  congr 1
  refine (Finset.sum_filter_of_ne ?_).symm
  intro X _ hX
  by_contra hnc
  exact hX (by rw [ursell_eq_zero_of_not_isCluster P X hnc]; simp)

/-- **E3 base case: the Mayer identity `Ξ = exp(clusterSum)` for the empty system.**
When there are no polymers, `Ξ(univ) = Ξ(∅) = 1` and `clusterSum = 0` (every inner
tuple-sum ranges over the empty function type `Fin (n+1) → ∅`), so the identity reads
`1 = exp(0)`.  Degenerate, but it is the genuine base case of E3 and — crucially — a
check that `partition` and `clusterSum` are normalized *consistently*: a normalization
mismatch between the two objects would already break here.  The general identity (the
Mayer–Ursell inversion) is the deferred combinatorial crux. -/
theorem expansion_identity_isEmpty [Fintype P.Polymer] [IsEmpty P.Polymer] :
    partition P (Finset.univ : Finset P.Polymer) = Complex.exp (clusterSum P) := by
  classical
  have h1 : clusterSum P = 0 := by
    unfold clusterSum
    have hterm : ∀ n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X : Fin (n + 1) → P.Polymer, (ursell P X : ℂ) * ∏ i, P.activity (X i) = 0 := by
      intro n
      haveI : IsEmpty (Fin (n + 1) → P.Polymer) := ⟨fun f => isEmptyElim (f 0)⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
    rw [tsum_congr hterm]; exact tsum_zero
  have h2 : partition P (Finset.univ : Finset P.Polymer) = 1 := by
    rw [Finset.univ_eq_empty]; exact partition_empty P
  rw [h2, h1, Complex.exp_zero]

/-- **E3 first-order consistency: the lowest-order term of the cluster sum is the
sum of single-polymer activities.**  The `n = 0` summand of `clusterSum` is
`(1!)⁻¹ · ∑_{X : Fin 1 → Polymer} φ(X)·z(X₀)`; since a single polymer is a cluster
with `φ = 1` (`ursell_fin_one`), this collapses to `∑_x z(x)`.  This is precisely the
linear term of `Ξ(Λ) = ∑_{S admissible} ∏ z`, so the cluster expansion matches `Ξ`
to first order — the second verified consistency check for the identity
`Ξ = exp(clusterSum)` (after the empty-system base case). -/
theorem clusterSum_first_order [Fintype P.Polymer] :
    ((Nat.factorial 1 : ℂ))⁻¹ *
      ∑ X : Fin 1 → P.Polymer, (ursell P X : ℂ) * ∏ i, P.activity (X i)
    = ∑ x : P.Polymer, P.activity x := by
  classical
  have hf : (Nat.factorial 1 : ℂ) = 1 := by norm_num
  rw [hf, inv_one, one_mul]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) P.Polymer)
    (fun X => (ursell P X : ℂ) * ∏ i, P.activity (X i)) (fun x => P.activity x) ?_
  intro X
  dsimp only
  rw [ursell_fin_one, Int.cast_one, one_mul, Fin.prod_univ_one]
  simp [Equiv.funUnique]

end YangMills.KP
