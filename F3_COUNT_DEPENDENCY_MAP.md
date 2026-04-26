# F3_COUNT_DEPENDENCY_MAP.md

**Cowork-authored mathematician-readable dependency map for the F3-COUNT closure path.**
**Updated: 2026-04-26T17:15:00Z, post-v2.52.0.**
**Status of `F3-COUNT` in `UNCONDITIONALITY_LEDGER.md`: `CONDITIONAL_BRIDGE` — and remains so until both missing theorems in §(b) land.**

This document is a planning blueprint, not a proof.  It is the input Codex
should use to schedule v2.53+ work on `CLAY-F3-COUNT-RECURSIVE-001`.  It does
not move any LEDGER row.  It does not reduce the lattice 28% / 23–25% /
Clay-as-stated 5% / named-frontier 50% headline numbers in
`registry/progress_metrics.yaml`.

All file references are absolute paths in
`YangMills/ClayCore/LatticeAnimalCount.lean` unless noted otherwise.

---

## Goal restated

Prove, **unconditionally and oracle-clean**, that the number of preconnected
subsets `X ⊆ siteLattice d L` containing a fixed `root`, with `|X| = n`, is
bounded by a Klarner-style geometric series:

    count(n) ≤ A₀ · K^n        with  A₀ = 1,  K = 2d − 1.

For the project's chosen `d = 4`, this gives `K_count = 7` and feeds directly
into `physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296`
(line 1096, already proven conditionally on
`PhysicalConnectingClusterBaselineExtraWordDecoderCovers 1296`).

The path from "physical 1296 alphabet anchored bucket family" to the Klarner
bound is exactly the BFS/Klarner anchored word decoder.  The remaining gap is
that the iteration step requires a *global* safe-deletion existence theorem,
not just the local degree-one subcase that v2.52 supplies.

---

## (a) Lean theorems already proven

In topologically sorted order, from primitive infrastructure up through
v2.52.0.  Every line reference was spot-checked via `Grep "^theorem … "` against
the live file at audit time.

### A.0 — Plaquette graph and degree bounds (preexisting)

| Line | Identifier | Role |
|---:|---|---|
| 50 | `plaquetteGraph_adj_siteLatticeDist_le_one` | adjacency definition |
| 59 | `plaquetteGraph_adj_of_ne_of_siteLatticeDist_le_one` | adjacency closure under distance ≤ 1 |
| 81 | `plaquetteGraph_neighborFinset_eq_filter` | neighbor decomposition |
| 95 | `plaquetteGraph_neighborFinset_subset_siteBall` | neighbor cardinality bound (geometric) |
| 106 | `plaquetteGraph_degree_le_siteBall_card` | degree ≤ ball cardinality |
| 337 | `plaquetteGraph_degreeBoundDim_of_siteNeighborBallBoundDim` | degree bound ≤ 2d |
| 358 | `plaquetteGraph_degreeBoundDim_physical_ternary` | physical instantiation: degree ≤ 2·4 = 8 (one per face direction); reduces to 7 via root-shell exclusion in §A.3 |
| 388 | `plaquetteGraph_neighborFinset_card_le_physical_ternary` | physical neighbor count ≤ 1296 (=`6^4`) |
| 421 | `plaquetteGraph_branchingBoundDim_physical_ternary` | branching ≤ K_count = 7 in d = 4 |
| 427 | `plaquetteGraph_branching_le_physical_ternary` | physical branching bound |

### A.1 — Anchored bucket family (preexisting → v2.42)

| Line | Identifier | Role |
|---:|---|---|
| 1269 | `plaquetteGraphPreconnectedSubsetsAnchoredCard` (def) | the anchored bucket family at size `k` |
| 1279 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_mem` | root always in bucket |
| 1289 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_card_eq` | bucket cardinality `=k` |
| 1299 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_preconnected` | members are preconnected (induced subgraph reachability) |
| 1309 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_card_pos` | nontrivial buckets exist |
| 1324 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_ne_root` | nontrivial buckets contain a non-root vertex |

### A.2 — Root shell witness (v2.42–v2.44)

The anchored root shell `X ∩ neighborFinset(root)` is the first BFS layer.

| Line | Identifier | Role |
|---:|---|---|
| 1372 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighbor` | shell nonempty for `1 < k` |
| 1396 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_root_neighborFinset` | finset variant |
| 1409 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_nonempty` | shell as Finset |
| 1420 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_pos` | shell card ≥ 1 |
| 1430 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_neighborFinset` | shell ⊆ neighborFinset |
| 1439 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShell_card_le_branching` | shell card ≤ K_count = 7 |
| 1462 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCodeOfBranching` (def) | encoding shell vertex into `Fin K_count` |
| 1473 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCodeOfBranching_injective` | injective encoding |

### A.3 — Anchored first-shell parent selector (v2.48)

| Line | Identifier | Role |
|---:|---|---|
| 1949 | `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296` (def) | parent code in `Fin 1296` |
| 1963 | `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296` (def) | parent vertex |
| 1979 | `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable` | reachability through parent |
| 2001 | `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296_spec` | parent code specification |

### A.4 — First-deletion / residual primitive (v2.50)

| Line | Identifier | Role |
|---:|---|---|
| 1530 | `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDeleteCode1296` (def) | first deletion code |
| 1545 | `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_firstDelete1296` (def) | first deletion vertex |
| 1561 | `..._firstDeleteCode1296_spec` | code specification |
| 1581 | `..._firstDelete1296_mem_erase_root` | deletion ∈ X.erase root |
| 1604 | `..._firstDeleteResidual1296` (def) | residual after deletion |
| 1618 | `..._firstDeleteResidual1296_card` | residual cardinality `= k − 1` |
| 1637 | `..._root_mem_firstDeleteResidual1296` | root ∈ residual |

### A.5 — Conditional recursive-deletion bridge (v2.51)

| Line | Identifier | Role |
|---:|---|---|
| 1666 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_preconnected` | **bridge**: if `X.erase z` is preconnected, residual ∈ anchored family at `k − 1` |
| 1690 | `..._firstDeleteResidual1296_mem_of_preconnected` | physical 1296 specialization |

This is the recursive step *conditional* on preserved preconnectedness.

### A.6 — Degree-one leaf deletion subcase (v2.52, latest)

| Line | Identifier | Role |
|---:|---|---|
| 1727 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_preconnected_of_induced_degree_one` | **NEW**: induced-degree-1 non-root deletion preserves preconnectedness |
| 1784 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_induced_degree_one` | **NEW**: full membership statement combining v2.52 + v2.51 |

### A.7 — Word-decoder consumer (preexisting at lines 982–1100)

| Line | Identifier | Role |
|---:|---|---|
| 987 | `PhysicalConnectingClusterExtraWordDecoderBound K` (Prop) | word decoder predicate |
| 1057 | `PhysicalConnectingClusterBaselineExtraWordDecoderCovers K` (Prop) | baseline coverage form |
| 1068 | `physicalConnectingClusterExtraWordDecoderBound_of_baselineExtraWordDecoderCovers` | bridge between forms |
| 1085 | `PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296` (abbrev) | physical instantiation |
| 1096 | `physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296` | **the consumer**: produces the full Klarner bound from a baseline word decoder coverage |

The consumer at line 1096 is conditional on
`PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296` — *that* is the
final hypothesis the missing theorems in §(b) are tasked with discharging.

### A.8 — Trivial-`k` and base-case bounds

| Line | Identifier | Role |
|---:|---|---|
| 2051 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_eq_empty` | k=0 trivial |
| 2070 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_one_subset_singleton` | k=1 = {root} |
| 2098 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_card_le_pow` | k=0 base case |
| 2107 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_one_card_le_pow` | k=1 base case |
| 2117 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_base_card_le_pow` | combined base ≤ K^k for k ≤ 1 |
| 2134 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_zero_wordDecoderCovers` | base k=0 covers word decoder |
| 2147 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_one_wordDecoderCovers` | base k=1 covers word decoder |
| 2164 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_base_wordDecoderCovers` | base k ≤ 1 covers word decoder |

The base cases are already in the codec form expected by §A.7's word decoder.

### A.9 — Root reachability and induced paths

| Line | Identifier | Role |
|---:|---|---|
| 2185 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_reachable` | root reachable from any member |
| 2202 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path` | induced path to root exists |

Useful for the §(d) iteration step (induced-degree-1 vertex existence often
proven by considering a longest induced path).

---

## (b) Lean theorems still missing

Two theorems are required to close `F3-COUNT`.  Both are non-trivial graph
combinatorics, but they are bounded in scope.

### B.1 — Global root-avoiding leaf existence lemma  *(see also §(c) for full statement)*

**Proposed Lean signature**:

```lean
theorem plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_safe_deletion
    {d : ℕ} {L : SiteLatticeBound d} {root : SiteLattice d L} {k : ℕ}
    (hk : 2 ≤ k)
    (X : Finset (SiteLattice d L))
    (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k) :
    ∃ z, z ∈ X ∧ z ≠ root ∧
      (induceFinset (plaquetteGraph d L) X).degree z = 1
```

**Dependencies on §(a)**: A.1 (`exists_ne_root` for nontriviality at `2 ≤ k`),
A.0 (`plaquetteGraph_adj_*` for induced-graph reasoning), A.9
(`root_exists_induced_path` is the natural witness — the endpoint of a longest
induced path from `root` is a degree-one leaf in the induced subgraph and is
not equal to `root`).

**Difficulty estimate**: **MEDIUM.**  Standard finite-graph theorem (every
finite tree has at least two leaves; in our case, "longest induced path
endpoint ≠ root" gives a non-root induced-degree-1 vertex).  The Mathlib
statement might already exist in `SimpleGraph.Connected.Subgraph`-adjacent
files; if so, the proof is < 50 LOC.  If we need to prove the general lemma
ourselves, ≈ 100–200 LOC.

**Variant (acceptable substitute)**: `safe_deletion` could be relaxed from
"induced degree 1" to "any non-root vertex `z` such that `X.erase z` remains
preconnected".  v2.51's `erase_mem_of_preconnected` accepts the relaxed form,
so both routes plug into the iteration in §(d).

### B.2 — Anchored word decoder iteration lemma  *(see also §(d))*

**Proposed Lean signature**:

```lean
theorem PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved :
    PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296
```

i.e. the existential propositional content of A.7's hypothesis is *closed*
unconditionally.

**Dependencies on §(a) + §(b)**: A.4–A.6 (deletion machinery), A.8 (base
cases), A.7 (consumer schema), §(b)/B.1 (global safe-deletion existence at
each `k ≥ 2`).

**Difficulty estimate**: **MEDIUM-HIGH.**  Conceptually a structural
induction on `k`: at each step pick a safe deletion via §(b)/B.1, apply
`erase_mem_of_induced_degree_one` (v2.52, line 1784) or
`erase_mem_of_preconnected` (v2.51, line 1666), recurse.  The cardinality
budget of A.4 (`firstDeleteResidual1296_card`) closes the descent.  Encoding
the full BFS/Klarner word as an iterated `Fin 1296` choice should follow A.3's
parent code pattern.  ≈ 200–400 LOC after B.1 lands.

---

## (c) Precise statement of the global root-avoiding leaf existence lemma

**Mathematical statement (informal)**:

> Let `G` be a finite simple graph and let `X` be a finite subset of `V(G)`
> with `|X| ≥ 2`, such that the induced subgraph `G[X]` is connected.  Fix any
> `root ∈ X`.  Then there exists `z ∈ X` with `z ≠ root` and `degree_{G[X]}(z) = 1`.

**Proof sketch (one paragraph, mathematician-grade)**:

> Take any longest induced path `P` in `G[X]` starting at `root`.  Such a path
> exists because `X` is finite and `G[X]` is connected.  Let `z` be the
> endpoint of `P` other than `root`.  Then `degree_{G[X]}(z) = 1`: if it were
> ≥ 2, `P` could be extended (the extra neighbor cannot be on `P` because then
> we would have an induced cycle, but `P` is induced; and the extra neighbor
> cannot be outside `X` because `X = V(G[X])`).  Since `|X| ≥ 2` and `G[X]` is
> connected, `P` has length ≥ 1, so `z ≠ root`.

**Why it suffices**: Combined with v2.52
(`plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_preconnected_of_induced_degree_one`,
line 1727) and v2.51 (`..._erase_mem_of_preconnected`, line 1666), this gives:
*for every nontrivial `X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L
root k` with `2 ≤ k`, there exists a safe deletion `X.erase z ∈
plaquetteGraphPreconnectedSubsetsAnchoredCard d L root (k − 1)`*.  This is the
recursion driver §(d) needs.

**Cross-check with project conventions**: The lemma uses only the induced
subgraph `(plaquetteGraph d L).induce X` (Mathlib `SimpleGraph.induce`), the
finite-subset hypothesis `X.Finite`, and the project's existing
`Preconnected` predicate.  No new infrastructure required.  A.9's
`root_exists_induced_path` is the natural starting point.

---

## (d) Iteration argument that lifts v2.52 + (c) to the full anchored word decoder

**Pseudocode for the iterated decoder** (mathematician-grade):

```
def decode (X : Finset _, k : ℕ, hk : k ≥ 0, hX : X ∈ Anchored(k)) : Word ℕ ≤ k
  match k with
  | 0       => empty word              -- A.8 base
  | 1       => singleton word [root]   -- A.8 base
  | k + 2   =>
      -- (B.1): pick a safe deletion z
      let z := safeDeletion X (k+2) hX                              -- §(c) / B.1
      -- (A.5 / A.6): the residual is in the smaller anchored family
      let X' := X.erase z                                          -- A.4 firstDelete*
      have hX' : X' ∈ Anchored(k+1) := erase_mem_of_induced_degree_one … z … hX
                                                                     -- v2.52 line 1784
      -- recurse
      let w := decode X' (k+1) (by omega) hX'                       -- recursion
      -- (A.3): encode the deletion symbol via parent code
      let s := rootShellParentCode1296 X (k+2) hX … z                -- v2.48 line 2001
      append s w
```

**Why this terminates and gives the Klarner bound**: at each step the bucket
size strictly decreases (A.4: `firstDeleteResidual1296_card` certifies `k → k
− 1`).  At each step the symbol `s` lives in `Fin 1296` (A.3).  After
unrolling, every `X ∈ Anchored(k)` produces a distinct word of length `≤ k` in
a `1296`-letter alphabet.  Combined with A.0's branching bound `branching ≤
K_count = 7` for `d = 4`, the encoding factors through a deterministic
mapping into `Fin K_count^k`, yielding `count(k) ≤ K^k = 7^k` exactly the
Klarner bound that A.7 / line 1096 consumes.

**Where v2.52 fits**: v2.52 is the proof that the inductive step's
preconnectedness preservation holds *in the degree-one subcase*.  §(c)/B.1
upgrades from "pick a deletion *if* one is degree-one" to "*there exists* a
non-root degree-one deletion".  These two pieces compose via `Exists.elim
hexists fun z hz => erase_preconnected_of_induced_degree_one … hz`.

---

## (e) Final Klarner-style bound

After §(d), the consumer at line 1096 fires:

```lean
def physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296
    (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296) :
    physicalShiftedF3CountPackageExp
```

with `hcover` discharged unconditionally by §(b)/B.2.  The package
`physicalShiftedF3CountPackageExp` is exactly the Klarner-style geometric
bound `count(n) ≤ A₀ · K^n = 1 · 7^n` that the Mayer/Brydges-Kennedy
side (`F3-MAYER`) needs.

**Effect on `UNCONDITIONALITY_LEDGER.md`**:

| Row | Before | After §(b) lands |
|---|---|---|
| `F3-COUNT` | `CONDITIONAL_BRIDGE` (v2.48 + v2.50 + v2.51 + v2.52) | `FORMAL_KERNEL` |
| `F3-MAYER` | `BLOCKED (gated on F3-COUNT)` | `READY` for independent attack |
| `F3-COMBINED` | `BLOCKED (gated on F3-COUNT and F3-MAYER)` | gated only on `F3-MAYER` |

**Effect on `registry/progress_metrics.yaml`**:

| Component | Current `contribution_percent` | After §(b) lands |
|---|---:|---:|
| F3-COUNT | 5 | **20** (full headline weight) |
| F3-MAYER | 0 | unchanged until F3-MAYER itself proven |
| F3-COMBINED | 0 | unchanged until F3-COMBINED itself assembled |

The `lattice_small_beta` headline would move ~28% → ~43% (assuming F3-COUNT
component's `weight_percent: 20` were realized; component contribution adds
+15 net).  **This bound applies only after §(b)'s missing theorems are
proven.  Until then, the headline 28% / 23–25% / 5% / 50% numbers stand
unchanged.**

---

## Honesty discipline

- This document is a **plan**, not a proof.  Filing it does not move any
  LEDGER row.  The dispatcher must not auto-promote `F3-COUNT` to
  `FORMAL_KERNEL` based on this document existing.
- The §(c) statement is mathematically routine but not yet Lean-formalized.
  Calling it "easy" or "almost done" would be overclaim — only the proof
  artefact in Lean closes it.
- The §(d) iteration is structurally clean but an arithmetic-of-encoding
  Lean proof is a non-trivial engineering effort, ≈ 200–400 LOC.
- The §(e) "after §(b) lands" effect on percentages is **conditional** on
  the actual Lean proofs.  No infrastructure win, no documentation win, no
  blueprint quality alone moves the percentages.
- `F3-COUNT` remains `CONDITIONAL_BRIDGE` until both §(b)/B.1 and §(b)/B.2
  land in `YangMills/ClayCore/LatticeAnimalCount.lean` with `#print axioms ⟹
  [propext, Classical.choice, Quot.sound]` and `lake build` green.

---

## Cross-references

- `AXIOM_FRONTIER.md` v2.52.0 entry (lines 1–49): the v2.52 commit's own
  honest framing — *"This is a genuine graph-combinatorics step inside
  CLAY-F3-COUNT-RECURSIVE-001, but it still does not close F3-COUNT"*.
- `UNCONDITIONALITY_LEDGER.md`: F3-COUNT row remains CONDITIONAL_BRIDGE.
- `JOINT_AGENT_PLANNER.md` critical path step 1 (`F3-SAFE-DELETION`) and
  step 2 (`F3-ANCHORED-WORD-DECODER`) match §(b)/B.1 and §(b)/B.2
  one-to-one.
- `FORMALIZATION_ROADMAP_CLAY.md`: F3 milestone gating identical.

---

## Suggested Codex schedule for v2.53+

1. **v2.53**: prove §(c)/B.1 — global root-avoiding leaf existence lemma.
   ~100–200 LOC.  Use the longest-induced-path argument; A.9's
   `root_exists_induced_path` is the start.  `#print axioms` must remain at
   `[propext, Classical.choice, Quot.sound]`.

2. **v2.54**: prove §(b)/B.2 — anchored word decoder iteration lemma.
   ~200–400 LOC.  Compose §(c)/B.1 with v2.52 line 1784 via structural
   induction on `k`; encode the deletion symbol via v2.48 line 2001's
   `rootShellParentCode1296`.

3. **v2.55**: tactical clean-up — chain through line 1096
   (`physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296`)
   to produce the unconditional `count(n) ≤ K_count^n` package; update the
   F3-COUNT LEDGER row to `FORMAL_KERNEL`; refresh
   `registry/progress_metrics.yaml` with Cowork audit (`lattice_small_beta`
   ~28% → ~43%, contribution `F3-COUNT` 5 → 20).

After v2.55: `F3-COUNT` is closed unconditionally and `F3-MAYER` becomes
the next live front.

---

*End of dependency map.  Filed by Cowork as deliverable for
`COWORK-F3-DEPENDENCY-MAP-001` per dispatcher instruction at
2026-04-26T17:10:00Z.*
