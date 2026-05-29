# Formalization plan — Kotecký–Preiss polymer cluster expansion in Lean

**Status: design only. Nothing here is implemented.** This is a concrete starting
blueprint for a (later, stronger) prover to build the polymer / cluster-expansion
layer that the Eriksson paper's §5 (terminal clustering) and §6.2 (single-scale UV
bound) rest on, and whose abstract endpoint is **Appendix A, Prop. A.1**
(`KP bound ⇒ exponential decay of truncated correlations`).

The code blocks below are **illustrative Lean signatures**, not compiled. They are
written so that proofs are `sorry`-free *targets*, never axioms. Per the project's
discipline (`FOUNDATIONS.md`), this file lives in `docs/` and is **not** part of the
verified `YangMillsCore`; it must never be imported into the core with `sorry`s.

> Honest difficulty: this is a **multi-month, novel formalization project**. To our
> knowledge there is **no polymer cluster expansion in Mathlib** as of 2026-05.
> Landing it would be a Mathlib-grade contribution useful far beyond this repo, and
> it is exactly milestone **M3** of `ROADMAP.md`: large, but *known mathematics*
> (not open). Do not expect to close it in a session.

---

## 0. Goal and what it unlocks

Formalize the abstract Kotecký–Preiss theorem and its corollary used by the paper:

> **(Appendix A, Prop. A.1)** For a hard-core polymer gas with activities `z(X)`
> satisfying a KP smallness criterion, the truncated two-point function decays
> exponentially: `|Cov(F,G)| ≤ C ‖F‖ ‖G‖ exp(−m · dist(supp F, supp G))`.

This `m > 0` is the terminal mass `m*` consumed as a **hypothesis** by
`YangMills/Paper/MassGapAssembly.lean` (`mass_gap_bound`, §7). Discharging Prop. A.1
turns that hypothesis from "assumed" to "derived from the KP bound" — i.e. it makes
the §5 input of the assembly genuine. (The §6.2 single-scale bound uses the same
machinery at each RG scale.)

It does **not** discharge where the KP bound itself comes from (Paper [1], extracted
from Balaban's activity estimates) — that remains the imported, hard input.

---

## 1. What Mathlib provides / lacks

**Has (reuse):** `Finset`, `Finset.sum`/`prod`, `Multiset`, `SimpleGraph` (for the
incompatibility graph and connectivity), `tsum`/`Summable` and absolute convergence,
`Real.exp` and monotonicity, geometric-series bounds (used already in
`UVSummation.lean`), `NNReal`/`ENNReal`.

**Lacks (must build):** polymer models, the polymer partition function, the
**Ursell/Mayer cluster coefficients**, the **cluster (Mayer) expansion of `log Ξ`**,
the **Kotecký–Preiss convergence criterion and its inductive proof**, and the
**truncated-correlation cluster representation**. None of this exists in Mathlib.

---

## 2. Recommended route

Use the **inductive Kotecký–Preiss proof** (Kotecký–Preiss, CMP 103 (1986)), in the
clean self-contained exposition of **Friedli–Velenik, _Statistical Mechanics of
Lattice Systems_, Ch. 5** (esp. Thm 5.4 and §5.7.1). Reasons:

* It avoids the Penrose/Brydges–Federbush **tree-graph inequality** (a separate hard
  combinatorial theorem) — KP's induction bounds the one-point cluster sum directly.
* The convergence is proved by induction on the number of polymers in a cluster,
  which maps well to Lean structural/strong induction.
* Friedli–Velenik state every constant and inequality explicitly (good for porting).

Alternative (if a tree-graph identity is later wanted for sharper constants):
Brydges–Kennedy / Bissacot–Fernández–Procacci — heavier, defer.

---

## 3. Layered Lean architecture (illustrative signatures)

### KP0 — Polymer substrate

```lean
/-- An abstract hard-core polymer system with complex activities. -/
structure PolymerSystem where
  Polymer    : Type*
  [decEq     : DecidableEq Polymer]
  incomp     : Polymer → Polymer → Prop          -- "incompatible" (overlap/touch)
  incomp_symm : ∀ X Y, incomp X Y → incomp Y X
  incomp_self : ∀ X, incomp X X                  -- hard core
  activity   : Polymer → ℂ                       -- z(X)

variable (P : PolymerSystem)

/-- A polymer family is *admissible* if its polymers are pairwise compatible. -/
def Admissible (S : Finset P.Polymer) : Prop :=
  ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → ¬ P.incomp X Y
```

### KP1 — Partition function (finite volume)

```lean
/-- Polymers "living in" a finite region `Λ : Finset Polymer`. -/
def partition (Λ : Finset P.Polymer) : ℂ :=
  ∑ S ∈ Λ.powerset.filter (Admissible P), ∏ X ∈ S, P.activity X
-- Ξ(Λ) = Σ over admissible subfamilies of the product of activities.
```

### KP2 — Cluster expansion and the KP criterion (the heart)

```lean
/-- The Kotecký–Preiss smallness criterion: there is a weight `a ≥ 0` with
    `∑_{Y incompatible with X} |z(Y)| · exp(a Y) ≤ a X`  for every polymer `X`. -/
def KPCriterion (a : P.Polymer → ℝ) : Prop :=
  (∀ X, 0 ≤ a X) ∧
  ∀ X, Summable (fun Y => if P.incomp X Y then ‖P.activity Y‖ * Real.exp (a Y) else 0) ∧
       (∑' Y, if P.incomp X Y then ‖P.activity Y‖ * Real.exp (a Y) else 0) ≤ a X

/-- Ursell/Mayer cluster coefficient of an (ordered) tuple of polymers, the sum over
    connected spanning subgraphs of the incompatibility graph of `(−1)^{edges}`. -/
noncomputable def ursell : List P.Polymer → ℚ := sorry   -- TARGET (combinatorial)

/-- **KP convergence (Friedli–Velenik Thm 5.4).** Under the KP criterion, the
    one-point cluster sum is bounded by `exp(a X) − 1`; hence the cluster expansion
    of `log Ξ` converges absolutely, uniformly in the volume. -/
theorem kp_cluster_convergence {a} (hKP : KPCriterion P a) (X : P.Polymer) :
    (∑' clusters containing X, |ursell …| * ∏ ‖activity‖) ≤ Real.exp (a X) - 1 := sorry
```

The induction (FV Thm 5.4): bound `Σ_{clusters ∋ X of n polymers}` by induction on
`n`, peeling one polymer and using the KP criterion to control the branching. This is
the single hardest lemma; budget most of the effort here.

### KP3 — Truncated correlation decay (= Appendix A, the payoff)

```lean
/-- Truncated two-point function as a sum over clusters connecting the supports. -/
-- def truncatedCorr (F G : Observable) : ℂ := ∑' clusters linking supp F, supp G, …

/-- **Appendix A, Prop. A.1.** KP convergence ⇒ exponential decay of covariances,
    with rate `m` from the KP weight and the per-polymer size penalty. -/
theorem kp_exponential_clustering
    {a} (hKP : KPCriterion P a) (hpen : SizePenalty P a m) (F G : …) :
    ‖truncatedCorr P F G‖ ≤ C * ‖F‖ * ‖G‖ * Real.exp (-(m * dist (supp F) (supp G))) := sorry
```

Any cluster linking `supp F` to `supp G` contains a connected chain spanning the
distance; the KP weights give an exponential penalty in that length. Summation over
such clusters uses `kp_cluster_convergence`. The output `m` is exactly the `mstar`
hypothesis of `mass_gap_bound`.

---

## 4. Milestones (with honest difficulty)

| ID | Content | Difficulty | Notes |
|----|---------|-----------|-------|
| **KP0** | `PolymerSystem`, `Admissible`, `partition` | low | ✅ **landed** — `YangMills/KP/Basic.lean` (`PolymerSystem`, `Admissible` + `admissible_empty`/`_mono`/`_singleton`, `partition`, `partition_empty = 1`); green, oracle clean. |
| **KP1** | finite-volume `Ξ`, basic identities (factorization over compatible blocks) | low–med | ✅ **landed** — `YangMills/KP/Basic.lean`: `partition_singleton` (`Ξ({X})=1+z(X)`), `admissible_union_iff`, and the factorization `partition_union` (`Ξ(Λ₁∪Λ₂)=Ξ(Λ₁)·Ξ(Λ₂)` for disjoint, cross-compatible blocks); green, oracle clean. This is the multiplicativity that makes `log Ξ` additive. |
| **KP2a** | `ursell` coefficients + connected-cluster indexing | **high** | ✅ **defined** — `YangMills/KP/Cluster.lean` (`incompGraph`, `incompGraph_adj`, `IsCluster`) + `YangMills/KP/Ursell.lean` (`ursell` = signed sum `∑(−1)^{#edges}` over connected spanning subgraphs of the incompatibility graph); green, oracle clean. **Next:** values on small clusters, the expansion identity `log Ξ = ∑ clusters …`, then KP2b convergence. |
| **KP2b** | `kp_cluster_convergence` (FV Thm 5.4, inductive) | **highest** | The crux. Strong induction on cluster size + KP criterion. Budget the bulk here. |
| **KP3** | `kp_exponential_clustering` (Appendix A) | med–high | Given KP2b, this is "spanning cluster pays e^{−m·dist}" + summation. |
| **KP4** | wire `m*` into `mass_gap_bound` (§7); state §5 as a theorem, not a hypothesis | low | The payoff: §5 input becomes derived from the KP bound. |

Estimated total: **multi-month**, KP2b dominating. Each milestone should land green
with oracle `[propext, Classical.choice, Quot.sound]` and no `sorry` before the next
begins (the project rule).

---

## 5. Where it leaves the honest picture

Completing KP0–KP4 would discharge the §5 (and, with the per-scale version, §6.2)
inputs of the already-formalized `mass_gap_bound` — turning the conditional lattice
mass-gap **assembly** into one resting only on the **KP bound of Paper [1]** (still
imported) and Balaban's framework. It would be a major, genuinely valuable
formalization milestone (M3).

It would **not** reach the Clay theorem: OS1 / full O(4) covariance and the continuum
construction (M4/M5, `ROADMAP.md`) remain open mathematics, and the KP input itself
(Paper [1], from Balaban's estimates) remains unformalized/imported. The honest
percentage ledger of `ROADMAP.md §0` is unchanged by *planning* this; it moves only
when the lemmas land green and survive an adversarial audit.
