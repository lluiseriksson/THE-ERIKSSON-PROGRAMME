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

open scoped BigOperators

variable (P : PolymerSystem)

/-- The **cluster sum** (right-hand side of the Mayer expansion), for a finite
polymer system:
`∑' n, (1/(n+1)!) · ∑_{X : Fin (n+1) → Polymer} φ(X) · ∏ᵢ z(Xᵢ)`.
Indexing by `n+1` makes every term a nonempty tuple.  Only clusters contribute
(`ursell_eq_zero_of_not_isCluster`).  The target identity is `Ξ = exp(clusterSum)`. -/
noncomputable def clusterSum [Fintype P.Polymer] : ℂ :=
  ∑' n : ℕ, (((n + 1).factorial : ℂ))⁻¹ *
    ∑ X : Fin (n + 1) → P.Polymer, (ursell P X : ℂ) * ∏ i, P.activity (X i)

end YangMills.KP
