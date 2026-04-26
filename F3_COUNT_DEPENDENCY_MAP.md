# F3_COUNT_DEPENDENCY_MAP.md

**Cowork-authored mathematician-readable dependency map for the F3-COUNT closure path.**
**Originally filed: 2026-04-26T17:15:00Z (post-v2.52.0). Refreshed: 2026-04-26T17:55:00Z (post-v2.53.0) per `REC-COWORK-F3-DEPENDENCY-MAP-V2.53-REFRESH-001`. Codex addendum: 2026-04-26T19:25:00Z (post-v2.55.0).**
**Status of `F3-COUNT` in `UNCONDITIONALITY_LEDGER.md`: `CONDITIONAL_BRIDGE` — and remains so until both missing theorems in §(b) land.**

**v2.53 refresh summary**: Codex v2.53 introduced the exact recursive
hypothesis `PlaquetteGraphAnchoredSafeDeletionExists` as a `def Prop`,
explicitly separated it from the strictly stronger
`PlaquetteGraphAnchoredDegreeOneDeletionExists`, and proved a one-directional
bridge (degree-one ⇒ safe-deletion) plus a conditional one-step driver. This
refresh updates §(a), §(b)/B.1, §(c), and §(d) so the blueprint reflects the
correct minimum-strength target. The original draft used the stronger
degree-one form, which fails on cyclic buckets (counter-example: 4-cycle root
shell) — the v2.53 framing is the correct one and is what this map now
adopts.

This document is a planning blueprint, not a proof.  It is the input Codex
should use to schedule v2.56+ work on `CLAY-F3-COUNT-RECURSIVE-001`.  It does
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

### A.6 — Degree-one leaf deletion subcase (v2.52)

| Line | Identifier | Role |
|---:|---|---|
| 1727 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_preconnected_of_induced_degree_one` | induced-degree-1 non-root deletion preserves preconnectedness |
| 1784 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_induced_degree_one` | full membership statement combining v2.52 + v2.51 |

### A.6.1 — Exact safe-deletion hypothesis + degree-one sufficiency bridge + conditional one-step driver (v2.53, latest)

The v2.53 entries split into two `def Prop`s (the named gaps) and four
oracle-clean theorems (conditional bridges/drivers).  None of them close
F3-COUNT; together they pin down the *minimum-strength* gap and provide the
clean one-step recursion driver from any future safe-deletion proof.

| Line | Identifier | Kind | Role |
|---:|---|---|---|
| 1805 | `PlaquetteGraphAnchoredSafeDeletionExists` | **`def Prop` (open gap)** | The exact recursive hypothesis — every nontrivial anchored bucket admits a non-root deletion whose residual is again an anchored bucket of size `k − 1`. **This is the minimum-strength target B.1 must discharge.** |
| 1820 | `PlaquetteGraphAnchoredDegreeOneDeletionExists` | **`def Prop` (open gap, strictly stronger)** | The strictly stronger sufficient hypothesis — every nontrivial anchored bucket has a non-root member of induced-degree 1 in the bucket subgraph. Sufficient via line 1831, but **not necessary**, and known to fail on cyclic buckets (see §(c) Strategy 1 counter-example). |
| 1831 | `plaquetteGraphAnchoredSafeDeletionExists_of_degreeOneDeletionExists` | theorem (oracle-clean) | **One-directional bridge**: degree-one ⇒ safe-deletion via v2.52 line 1727. The converse is *not* claimed and does not hold in general. |
| 1847 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion` | theorem (oracle-clean) | **Conditional one-step driver**: takes `PlaquetteGraphAnchoredSafeDeletionExists d L` as input, produces the existence of a non-root deletion landing in the bucket family at `k − 1`. This is the v2.53 hand-off used by §(d). |
| 1860 | `PhysicalPlaquetteGraphAnchoredSafeDeletionExists` | abbrev | physical d=4 specialization |
| 1866 | `PhysicalPlaquetteGraphAnchoredDegreeOneDeletionExists` | abbrev | physical d=4 specialization |
| 1872 | `physicalPlaquetteGraphAnchoredSafeDeletionExists_of_degreeOneDeletionExists` | theorem (oracle-clean) | physical bridge |
| 1882 | `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion` | theorem (oracle-clean) | physical conditional one-step driver |

### A.6.2 — Unrooted non-cut deletion + card-two root-avoiding base (v2.54–v2.55)

| Line | Identifier | Kind | Role |
|---:|---|---|---|
| 1909 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_preconnected_unrooted` | theorem (oracle-clean) | v2.54: some vertex can be deleted while preserving induced preconnectedness; deletion is not root-avoiding |
| 1960 | `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_preconnected_unrooted` | theorem (oracle-clean) | physical v2.54 specialization |
| 1979 | `plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_two` | theorem (oracle-clean) | v2.55: root-avoiding safe deletion for the first nontrivial bucket size `k = 2` |
| 2022 | `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_two` | theorem (oracle-clean) | physical v2.55 specialization |

The remaining B.1 obstruction is therefore narrower than the v2.53 refresh:
prove the global root-avoiding safe-deletion theorem for `k >= 3`, then package
it as `PlaquetteGraphAnchoredSafeDeletionExists`.

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
combinatorics, but they are bounded in scope.  **The minimum-strength target
of B.1 is `PlaquetteGraphAnchoredSafeDeletionExists` (v2.53 line 1805), not
the strictly stronger `PlaquetteGraphAnchoredDegreeOneDeletionExists` (line
1820).**

### B.1 — Global root-avoiding safe-deletion existence (the v2.53 hypothesis)

**Proposed Lean signature** (the actual `def Prop` v2.53 already names — B.1
is to *prove* this proposition, not to introduce a new statement):

```lean
theorem plaquetteGraphAnchoredSafeDeletionExists_proved
    {d L : ℕ} [NeZero d] [NeZero L] :
    PlaquetteGraphAnchoredSafeDeletionExists d L
```

Unfolding: for every `root`, `k ≥ 2`, and `X ∈
plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k`, exhibit some
`z ∈ X`, `z ≠ root`, with `X.erase z ∈
plaquetteGraphPreconnectedSubsetsAnchoredCard d L root (k − 1)`.  In graph
language: every nontrivial anchored preconnected bucket admits a non-root
*non-cut* (safe) deletion.

**Why not the degree-one form**: the strictly stronger
`PlaquetteGraphAnchoredDegreeOneDeletionExists` fails for buckets containing
cycles.  Concrete counter-example (induced 4-cycle):

> Take `d = 1`, `L = 4`, root = `a`, `X = {a, b, c, d}` arranged in a
> 4-cycle with edges `(a,b)`, `(b,c)`, `(c,d)`, `(d,a)`.  Every non-root
> vertex has induced-degree exactly 2.  No non-root vertex has induced
> degree 1.  Yet *every* non-root vertex (b, c, or d) is non-cut in the
> 4-cycle: erasing it leaves a 3-vertex induced path which is preconnected.

So in `C_4`-style configurations the degree-one hypothesis fails but
safe-deletion still holds.  Real plaquette-graph buckets do contain cycles
(plaquette adjacency is not tree-like at d ≥ 2), so the project must target
the safe-deletion form, not the degree-one form.

**Sufficient subcase available**: if a future step proves the strictly
stronger `PlaquetteGraphAnchoredDegreeOneDeletionExists` (which is cleaner
to state but provable only when buckets happen to be tree-like), v2.53's
line 1831 bridge automatically lifts it to the exact safe-deletion
hypothesis.  This is a legitimate intermediate, but the *unconditional*
target is the safe-deletion form.

**Dependencies on §(a)**:

- A.1 (`exists_ne_root`) for non-triviality at `2 ≤ k`.
- A.0 + A.5/A.6 for induced-graph adjacency and the v2.51/v2.52 bridges
  composing into safe-deletion.
- A.9 (`root_reachable` and `root_exists_induced_path`) for the
  longest-induced-path strategy in the acyclic subcase.

**Difficulty estimate**: **MEDIUM-HIGH.**  Two-strategy proof (see §(c)):
Strategy 1 (acyclic case via longest induced path) is ≈ 50–100 LOC and
folkloric.  Strategy 2 (cyclic case via DFS-tree non-cut argument or
block-cut decomposition) is ≈ 150–300 LOC and may pull in standard graph-
theory infrastructure that Mathlib partially has (`SimpleGraph.Connected`,
`SimpleGraph.Subgraph.Connected.exists_isCutVert`-adjacent).  Combined
estimate ≈ 200–400 LOC.

**Mathlib pre-check (per `REC-CODEX-MATHLIB-LONGEST-INDUCED-PATH-CHECK-001`)**:
before proving from scratch, grep Mathlib4 for any of: `IsCutVertex`,
`IsBridge`, `Connected.erase`, `Connected.exists_non_cut`,
`SimpleGraph.Subgraph.Connected.exists_isPathInduced`, `LongestPath`, or
DFS-tree machinery.  If Mathlib has the non-cut-vertex existence lemma, B.1
reduces to a ≈ 30–50 LOC adapter; if not, write the general non-cut-vertex
lemma as a fresh Mathlib PR draft simultaneously with the project-side
proof.

**Variant (strictly weaker, acceptable as intermediate)**: prove
`PlaquetteGraphAnchoredDegreeOneDeletionExists` instead.  v2.53 line 1831
then composes it to the exact safe-deletion form.  Acceptable only if (a)
the full `PlaquetteGraphAnchoredSafeDeletionExists` proof is too far away,
*and* (b) the project explicitly accepts the stronger hypothesis as
sufficient input for §(d) (which it is).  The downside: this approach
inherits the cyclic-case failure described above, so the stronger
hypothesis cannot in fact be proven globally — it is only a valid step on
the acyclic subset of buckets.

### B.2 — Anchored word decoder iteration lemma  *(see also §(d))*

**Proposed Lean signature**:

```lean
theorem PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved :
    PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296
```

i.e. the existential propositional content of A.7's hypothesis is *closed*
unconditionally.

**Dependencies on §(a) + §(b)**: A.4–A.6 (deletion machinery), A.6.1 v2.53
(`exists_erase_mem_of_safeDeletion` driver at line 1847 or its physical
specialization at line 1882), A.8 (base cases), A.7 (consumer schema),
§(b)/B.1 (global safe-deletion existence at each `k ≥ 2`).

**Difficulty estimate**: **MEDIUM-HIGH.**  Conceptually a structural
induction on `k`: at each step apply v2.53 line 1847's
`exists_erase_mem_of_safeDeletion` (which takes `B.1` as input), apply
v2.51 line 1666's `erase_mem_of_preconnected`, recurse.  The cardinality
budget of A.4 (`firstDeleteResidual1296_card`) closes the descent.  Encoding
the full BFS/Klarner word as an iterated `Fin 1296` choice should follow
A.3's parent-code pattern.  ≈ 200–400 LOC after B.1 lands.

---

## (c) Precise statement of the global root-avoiding safe-deletion existence lemma

The minimum-strength target — the actual unconditional content of v2.53's
`def Prop` at line 1805 unfolded.

**Mathematical statement (informal)**:

> Let `G` be a finite simple graph and let `X` be a finite subset of `V(G)`
> with `|X| ≥ 2`, such that the induced subgraph `G[X]` is connected.  Fix
> any `root ∈ X`.  Then there exists `z ∈ X` with `z ≠ root` such that
> `G[X.erase z]` is also connected (i.e. `z` is a non-cut vertex of `G[X]`
> different from `root`).

In project terminology (after specialising to `G = plaquetteGraph d L` and
the `Preconnected` notion the project uses): for every `2 ≤ k` and every
`X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard d L root k`, there
exists `z ∈ X` with `z ≠ root` and `X.erase z ∈
plaquetteGraphPreconnectedSubsetsAnchoredCard d L root (k − 1)`.

This is exactly the unfolding of `PlaquetteGraphAnchoredSafeDeletionExists d
L` at v2.53 line 1805.

### Two strategies, one combined proof

**Strategy 1 — acyclic / tree-shaped buckets**: longest-induced-path
endpoint argument.

> If `G[X]` is acyclic (a tree on `X`), every leaf — endpoint of the longest
> induced path — has induced-degree 1, and at least one such leaf must be
> distinct from `root` because `|X| ≥ 2`.  In Lean, A.9's
> `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path`
> at line 2202 supplies the path; the endpoint extraction is a Mathlib-style
> lemma about `SimpleGraph.Walk.IsPath.length`.

This strategy was the original §(c) idea in the v1 draft of this map.  It
proves the *strictly stronger* `PlaquetteGraphAnchoredDegreeOneDeletionExists`
hypothesis (line 1820), which then implies safe-deletion via v2.53 line
1831's bridge.  But it **only applies when the induced bucket subgraph is
acyclic**.

**Why Strategy 1 alone is insufficient**: real plaquette-graph buckets
contain cycles.  Counter-example for the degree-one form (already given in
§(b)/B.1): a `C_4` cycle has every non-root vertex at induced-degree 2.  In
such a bucket, no non-root induced-degree-1 vertex exists, so Strategy 1's
output is empty even though a non-cut deletion does exist.

**Strategy 2 — general case via non-cut vertex existence (DFS-tree or
block-cut decomposition)**: every nontrivial finite connected graph has at
least *two* non-cut vertices, so at least one of them must differ from the
root.

> *Theorem (folklore, e.g. Diestel "Graph Theory" Prop. 1.4.1)*: Every
> connected graph `H` on `≥ 2` vertices has at least 2 non-cut vertices.
>
> *Proof*: Run depth-first search from any vertex.  The DFS tree's leaves
> are non-cut in `H` itself — deleting a DFS leaf cannot disconnect the
> graph because every other vertex's tree-path to root avoids the leaf.
> The DFS tree on `n ≥ 2` vertices has ≥ 2 leaves (if it has only 1, the
> tree is a single path, whose two endpoints are both leaves — contradiction
> since the path has 2 leaves).  So `H` has ≥ 2 non-cut vertices.

In our setting `H = G[X]` and `|X| = k ≥ 2`, so `G[X]` has at least 2
non-cut vertices.  At least one of them is `≠ root`, giving the
`PlaquetteGraphAnchoredSafeDeletionExists` witness.

**Why Strategy 2 covers the cyclic case**: in the `C_4` counter-example,
both DFS trees (rooted at any vertex) have exactly 2 leaves; both leaves
are non-cut in `C_4`; one of the two leaves is necessarily different from
`root`.

**Combined proof outline** (Lean-side):

```
theorem plaquetteGraphAnchoredSafeDeletionExists_proved (d L : ℕ)
    [NeZero d] [NeZero L] :
    PlaquetteGraphAnchoredSafeDeletionExists d L := by
  intro root k X hk hX
  -- A.0 + A.5 + A.6 + Mathlib SimpleGraph.Connected give:
  -- the induced subgraph (plaquetteGraph d L).induce {x // x ∈ X} is connected,
  -- and |X| = k ≥ 2.
  -- Strategy 2: pick a non-root non-cut vertex via DFS-tree leaves.
  obtain ⟨z, hzX, hz_ne_root, hz_safe⟩ :=
    SimpleGraph.Connected.exists_two_non_cut … -- Mathlib helper, possibly missing
  -- If Mathlib lacks the helper, prove it once at the SimpleGraph level
  -- and PR upstream; meanwhile, prove a project-internal version using A.9.
  ...
```

**Cross-check with project conventions**: The lemma uses only the induced
subgraph `(plaquetteGraph d L).induce X` and the project's existing
`Preconnected` predicate.  A.9 supplies one starting point; Mathlib's
`SimpleGraph.Connected` machinery should supply the rest (with PR-able
gaps where it doesn't).

**Notes on robustness**: the safe-deletion form is robust to graph
topology (cyclic or acyclic), making it the correct unconditional target.
The degree-one form, while easier to state and useful as an intermediate,
is too strong globally and cannot be the project's final target.

---

## (d) Iteration argument that lifts v2.52 + (c) to the full anchored word decoder

**Pseudocode for the iterated decoder** (mathematician-grade, post-v2.53):

```
def decode (X : Finset _, k : ℕ, hk : k ≥ 0, hX : X ∈ Anchored(k))
    (hsafe : PlaquetteGraphAnchoredSafeDeletionExists d L)
    : Word (Fin 1296) ≤ k
  match k with
  | 0       => empty word              -- A.8 base
  | 1       => singleton word [root]   -- A.8 base
  | k + 2   =>
      -- (v2.53 line 1847): obtain a non-root deletion landing in Anchored(k+1)
      obtain ⟨z, hzX, hz_ne_root, hz_residual⟩ :=
        plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_safeDeletion
          hsafe (by omega : 2 ≤ k + 2) hX
      -- (A.5 v2.51 + A.6 v2.52 are now upstream of v2.53 line 1847; we use
      -- the v2.53 driver directly without composing them by hand)
      let X' := X.erase z                                          -- A.4 firstDelete*
      have hX' : X' ∈ Anchored(k+1) := hz_residual
      -- recurse
      let w := decode X' (k+1) (by omega) hX' hsafe                -- recursion
      -- (A.3): encode the deletion symbol via parent code
      let s := rootShellParentCode1296 X (k+2) hX z                -- v2.48 line 2001
      append s w
```

**Why this terminates and gives the Klarner bound**: at each step the bucket
size strictly decreases (A.4: `firstDeleteResidual1296_card` certifies
`k → k − 1`; v2.53 line 1847 packages this with safe deletion as a single
step).  At each step the symbol `s` lives in `Fin 1296` (A.3).  After
unrolling, every `X ∈ Anchored(k)` produces a distinct word of length `≤ k`
in a `1296`-letter alphabet.  Combined with A.0's branching bound
`branching ≤ K_count = 7` for `d = 4`, the encoding factors through a
deterministic mapping into `Fin K_count^k`, yielding `count(k) ≤ K^k = 7^k`
— the Klarner bound consumed by A.7 / line 1096.

**Where v2.52 + v2.53 fit**: v2.52 (lines 1727 + 1784) proves the
inductive step's preconnectedness preservation in the *local* degree-one
subcase.  v2.53 (lines 1805/1820/1831/1847) rewraps this into the
*hypothesis-shape* the decoder actually consumes: take the global
safe-deletion existence as a Prop input, get the one-step recursive
transition out.  §(b)/B.1 then discharges the hypothesis input
unconditionally, completing the Klarner closure.  The decoder pseudocode
above plugs the v2.53 driver directly — no need to hand-compose v2.51 +
v2.52 anymore.

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
| `F3-COUNT` | `CONDITIONAL_BRIDGE` (v2.48 + v2.50 + v2.51 + v2.52 + v2.53) | `FORMAL_KERNEL` |
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

## Suggested Codex schedule for v2.56+ (post-v2.55 addendum)

**v2.53–v2.55 already landed**: the exact safe-deletion `def Prop` +
degree-one sufficient `def Prop` + bridge + conditional one-step driver,
the unrooted non-cut deletion theorem, and the `k = 2` root-avoiding base
case, all oracle-clean.  The remaining work is now precisely:

1. **v2.56**: prove §(b)/B.1 for the remaining `k >= 3` case —
   `plaquetteGraphAnchoredSafeDeletionExists_proved`.  The unrooted non-cut
   adapter exists from v2.54; the missing step is ensuring one safe deletion
   avoids the anchored root, likely via a two-non-cut-vertices theorem or a
   rooted block/DFS argument.

   **Acceptable intermediate**: prove the strictly stronger
   `PlaquetteGraphAnchoredDegreeOneDeletionExists` instead, then use v2.53
   line 1831's bridge.  Gets you a working decoder for tree-shaped buckets,
   but **not for cyclic buckets**, so cannot be the final unconditional
   target.

2. **v2.57**: prove §(b)/B.2 — `PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296_proved`.
   ~200–400 LOC after B.1 lands.  Use v2.53 line 1847's
   `exists_erase_mem_of_safeDeletion` driver directly (no hand-composition
   with v2.51/v2.52 needed).  Structural induction on `k`; encode the
   deletion symbol via v2.48 line 2001's `rootShellParentCode1296`.

3. **v2.58**: tactical clean-up — chain through line 1096
   (`physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296`)
   to produce the unconditional `count(n) ≤ K_count^n` package; update
   the F3-COUNT LEDGER row to `FORMAL_KERNEL`; refresh
   `registry/progress_metrics.yaml` with Cowork audit (`lattice_small_beta`
   ~28% → ~43%, contribution `F3-COUNT` 5 → 20).

After v2.56: `F3-COUNT` is closed unconditionally and `F3-MAYER` becomes
the next live front.

---

*End of dependency map.  Filed by Cowork as deliverable for
`COWORK-F3-DEPENDENCY-MAP-001` per dispatcher instruction at
2026-04-26T17:10:00Z.*
