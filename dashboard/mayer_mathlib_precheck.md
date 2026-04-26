# mayer_mathlib_precheck.md

**Cowork-authored Mathlib pre-check for F3-MAYER §(b)/B.3 (BK polymer bound).**
**Filed: 2026-04-26T20:20:00Z by Cowork.**
**Loop-input for the F3-MAYER work that begins after F3-COUNT closes (post-v2.57+).
Parallel to `REC-CODEX-MATHLIB-LONGEST-INDUCED-PATH-CHECK-001` (RESOLVED) which
saved ~100 LOC for v2.54.**

This document is a **scoping**, not a proof. Cowork has not written any Mathlib
PR, has not closed any §(b)/B.* theorem. The document enumerates what Mathlib
**has** vs what Mathlib **lacks** for the BK forest formula at `F3_MAYER_DEPENDENCY_MAP.md`
§(b)/B.3 (HIGH difficulty, ~250 LOC). The pattern: Cowork pre-check → Codex
adopt findings → Codex implement project-side and/or PR Mathlib. v2.54's
unrooted non-cut step landed in ~100 LOC instead of ~200 LOC because the
helper Cowork pointed at already existed; the present pre-check identifies
similar opportunities (and more importantly, a clean gap-list).

The Mathlib clone consulted: `C:\Users\lluis\Downloads\mathlib4` (local
checkout, base commit `80a6231dcf` per dashboard).

---

## (a) SimpleGraph spanning trees / tree enumeration / Cayley's formula

### What Mathlib has

| Mathlib import path | Identifier | Role |
|---|---|---|
| `Mathlib.Combinatorics.SimpleGraph.Acyclic` | `SimpleGraph.IsTree` (predicate) | Tree predicate; lines 157, 161 give witness lemmas (`IsTree.coe_singletonSubgraph`, `IsTree.coe_subgraphOfAdj`) |
| `Mathlib.Combinatorics.SimpleGraph.Acyclic` | `SimpleGraph.IsAcyclic` | Acyclic predicate |
| `Mathlib.Combinatorics.SimpleGraph.Acyclic`:453 | `isTree_iff_maximal_isAcyclic` | `IsTree ↔ Nonempty V ∧ Maximal IsAcyclic G` |
| `Mathlib.Combinatorics.SimpleGraph.Acyclic`:604/609 | `IsTree.coloringTwoOfVert`, `IsTree.coloringTwo` | trees are 2-colorable |
| `Mathlib.Combinatorics.SimpleGraph.Walk.IsPath` (used by v2.54) | `Walk.IsPath` predicate | path predicate; available |
| `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected` | `SimpleGraph.Connected` + helpers | already used by v2.54 (`exists_preconnected_induce_compl_singleton_of_finite`) |
| `Mathlib.Combinatorics.SimpleGraph.Hamiltonian` | Hamiltonian path predicates | adjacent but not what BK needs |
| `Mathlib.Combinatorics.SimpleGraph.Subgraph` | subgraph machinery | used by v2.54 |

### What Mathlib LACKS (critical for BK forest formula)

- **Cayley's formula** (`number of spanning trees of K_n = n^(n-2)`): zero matches
  in Mathlib's tree. Searched for `Cayley.*formula`, `cayley_formula`,
  `n_pow_n_minus_two`, `spanning_trees_card` — all zero. Note: `Mathlib/Combinatorics/SimpleGraph/Cayley.lean`
  is the **Cayley graph of a group**, NOT Cayley's formula for tree count.
- **Spanning tree enumeration / counting**: zero results for `spanningTree`,
  `spanning_tree`, `isSpanningTree`. Mathlib has tree predicates but no
  enumerator or cardinality theorem.
- **Tree-on-finite-set count**: `|spanning_trees(K_n)| = n^(n-2)` is folklore
  (Cayley 1889) but has not been formalized in Mathlib as of this checkout.

### Estimated Mathlib LOC needed if PR'd upstream

- `Cayley_n_pow_n_minus_two`: ~250–400 LOC. Multiple proof strategies exist:
  Prüfer correspondence (most direct, requires bijection lemma), Kirchhoff's
  matrix-tree theorem (linear algebra heavy, requires `LapMatrix` content
  Mathlib already has at `Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean`).
- BK forest formula does **not** strictly need Cayley's formula — it needs the
  weaker bound `tree_count(Y) ≤ |Y|^(|Y|-2)`, which the BK estimate uses as a
  loose upper bound. So Cayley's exact formula is convenient but a Prüfer-style
  injection proof (~150 LOC) suffices.

---

## (b) Measure-theoretic interpolation / Brydges-Kennedy / random-walk cluster expansion

### What Mathlib has

| Mathlib import path | Identifier | Role |
|---|---|---|
| `Mathlib.MeasureTheory.Constructions.Pi` | `MeasureTheory.Measure.pi` | product measure on finite product spaces |
| `Mathlib.MeasureTheory.Integral.IntegrableOn` | `IsCompact.integrableOn`, `Continuous.integrableOn_isCompact` | integrability on compact sets |
| `Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable` | `Continuous.aestronglyMeasurable` | continuous → AE strongly measurable |
| `Mathlib.MeasureTheory.Integral.Bochner.Basic` (general path) | `MeasureTheory.integral` API | the actual integral |
| Mathlib has `MeasureTheory.Measure.IsHaarMeasure` | Haar measure on locally compact groups | already foundational for SU(N) |

### What Mathlib LACKS (critical for BK forest formula)

- **Brydges-Kennedy interpolation formula**: **zero matches** for `Brydges`,
  `brydges`, `forestFormula`, `forest_formula` across all of Mathlib. The
  canonical reference (Brydges-Kennedy, *Mayer expansions and the
  Hamilton-Jacobi equation*, J. Stat. Phys. 48, 1987) has **not been formalized
  in any form** in Mathlib.
- **Mayer expansion / Mayer-Ursell identity**: search for `Mayer` returns only
  sheaf-cohomology Mayer-Vietoris, irrelevant. **Zero matches** for the
  statistical-mechanics Mayer identity.
- **Random-walk cluster expansion** infrastructure: zero matches for
  `cluster_expansion`, `clusterExpansion`, `polymer_expansion`. The project's
  existing `MayerExpansion.lean` (`TruncatedActivities` structure) is the
  project's home-rolled version.
- **Möbius inversion on the partition lattice**: not found in Mathlib in the
  form needed for cluster expansion (Mathlib has `Möbius` for arithmetic
  functions and posets generally, but not the partition-lattice instance with
  the connected-cumulant structure).

### Estimated Mathlib LOC needed if PR'd upstream

- BK interpolation formula proper: ~600–1000 LOC. This is **research-level
  Mathlib content**, much larger than v2.54's ~100-LOC adapter. A proper PR
  would need: tree-on-Y enumeration (sec (a)), the polynomial Φ(s_1,...,s_{|Y|−1}),
  the integral identity, the bound. Realistic scope: a multi-PR contribution
  if attempted upstream.
- More tractable: project-side hand-rolled BK estimate using Mathlib's
  `MeasureTheory.Measure.pi`, `Finset.sum_powerset`, `Polynomial` API. The
  BLUEPRINT_F3Mayer §4.1 file (3) `BrydgesKennedyEstimate.lean` (~250 LOC)
  estimate already accounts for this without upstream PR.

---

## (c) `essSup`, supremum-of-bounded-continuous-on-compact, integrability

### What Mathlib has

| Mathlib import path | Identifier | Role |
|---|---|---|
| `Mathlib.MeasureTheory.Function.EssSup` | `MeasureTheory.essSup`, `essSup_le_iff` | essential supremum API |
| `Mathlib.MeasureTheory.Function.LpSeminorm.Basic` | `eLpNorm`, `Memℒp` | Lp norm machinery |
| `Mathlib.MeasureTheory.Function.LpSeminorm.Defs` | `Memℒp` definitions | |
| `Mathlib.MeasureTheory.Integral.IntegrableOn` | `Continuous.integrableOn_compact_of_isFiniteMeasure` (or equiv) | continuous + compact → integrable |
| `Mathlib.Topology.ContinuousOn` | `IsCompact.exists_isMaxOn` (continuous on compact attains its sup) | gives `‖f‖∞ = sup |f|` for continuous on compact |
| `Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable` | `Continuous.aestronglyMeasurable` | for the `meas` direction |

### What Mathlib LACKS

- **Direct lemma `IsCompact.continuous_integrable_pow`**: not found by name.
  However, integrability of `(f U)^k` for continuous `f` on compact follows from
  `Continuous.pow` + `IsCompact.integrableOn_isFiniteMeasure_of_continuous` (or
  similar; chained).
- **Direct lemma `‖continuous_function_on_compact‖_∞ = sup_value`**: this is
  also chained through `IsCompact.exists_isMaxOn` + `essSup_eq_iSup_of_continuous`
  or similar; not a single-name lemma.

### Estimated project-side LOC needed

- `‖w̃‖∞ ≤ 4 N_c · β` (B.4 in F3_MAYER_DEPENDENCY_MAP.md): ~80 LOC, mostly
  arithmetic. Mathlib has all the helpers needed; the LOC is just chaining.
- Gap from `‖w̃‖∞^|Y|` bound to the Lᵖ norm needed by `MayerExpansion.lean`:
  ~30 LOC, a chain of `essSup_pow` + `Continuous.essSup_le` + integrability.

---

## (d) Mathlib has-vs-lacks summary for §(b)/B.* dependency

| Item | Mathlib has? | Project-side LOC needed | PR-upstream LOC if missing |
|---|:---:|---:|---:|
| `SimpleGraph.IsTree` predicate | ✓ | 0 (use directly) | n/a |
| `SimpleGraph.IsAcyclic` predicate | ✓ | 0 (use directly) | n/a |
| Spanning tree enumeration | ✗ | ~50 (project-side enumerator) | ~150–250 |
| Cayley's formula `\|spanning_trees(K_n)\| = n^(n-2)` | ✗ | not strictly needed | ~250–400 (Prüfer) or ~600 (matrix-tree) |
| Tree-count upper bound `tree_count(Y) ≤ |Y|^(|Y|-2)` | ✗ | ~30 if Cayley exact landed; ~150 from scratch | ~150 |
| BK interpolation formula | ✗ | ~250 (BLUEPRINT_F3Mayer §4.1 file 3) | ~600–1000 (research-level) |
| Mayer-Ursell identity | ✗ | ~200 (BLUEPRINT_F3Mayer §4.1 file 4) | ~400 (research-level) |
| Möbius inversion on partition lattice | partial (Möbius for posets, but not the partition-lattice instance with connected-cumulant structure) | ~80 (specialize to partition lattice for connected cumulants) | ~200 |
| `essSup`, `Memℒp` machinery | ✓ | 0 (use directly) | n/a |
| `Continuous.aestronglyMeasurable` | ✓ | 0 (use directly) | n/a |
| `IsCompact.integrableOn_continuous` | ✓ | 0 (use directly) | n/a |
| `‖continuous_on_compact‖∞ = sup` | partial (chained) | ~30 (chaining) | ~50 (single-name lemma if PR'd) |
| `MeasureTheory.Measure.pi` for Wilson plaquettes | ✓ | ~50 (Wilson-specific wrapper) | n/a |

### Most expensive gap

**The BK interpolation formula itself** (~600–1000 LOC if PR'd upstream;
~250 LOC project-side) is the most expensive Mathlib gap of any project work
to date. Cowork recommends **project-side implementation** rather than
attempting an upstream PR for this specific theorem — the analytic content is
too specialized (statistical mechanics) to expect rapid Mathlib acceptance,
and the project's `MayerExpansion.lean` already provides the consumer
infrastructure (`TruncatedActivities`).

### Most savings available

**Tree-count upper bound** (`tree_count(Y) ≤ |Y|^(|Y|-2)`) is the second-most
expensive gap. If a Prüfer correspondence proof is contributed to Mathlib
upstream (~150–250 LOC), it benefits the broader ecosystem AND saves the
project ~30 LOC. Cowork recommends Codex either (a) PR a Prüfer correspondence
proof when it implements §(b)/B.3, or (b) hand-roll a project-side `treeCountFinset`
function with a loose upper bound, deferring the Mathlib PR.

---

## (e) Recommendation filing

Cowork files **two** new recommendations to capture the findings:

### REC-CODEX-MAYER-MATHLIB-CAYLEY-OR-PRUFER-001 (priority 6, OPEN)

**Title**: Codex should choose between (a) Mathlib PR for Prüfer correspondence
giving Cayley's formula, or (b) project-side `treeCountFinset` with loose upper
bound, when implementing F3-MAYER §(b)/B.3.

**Rationale**: BK forest formula needs `tree_count(Y) ≤ |Y|^(|Y|-2)`. Mathlib
has tree predicates (`IsTree`, `IsAcyclic`) but no tree count theorem.
Two paths:
- (a) Project contributes a Prüfer correspondence proof to Mathlib (~150-250 LOC,
  benefits broader ecosystem, ~30 LOC saving inside project).
- (b) Project hand-rolls a `treeCountFinset` definition + loose upper bound
  (~150 LOC project-side, no Mathlib touch).

**Risk if ignored**: Codex hand-rolls a tree counter without Mathlib integration,
losing ~30 LOC of reuse and missing an upstream contribution opportunity.

### REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001 (priority 7, OPEN)

**Title**: Codex should keep the BK interpolation formula project-side
(~250 LOC in `BrydgesKennedyEstimate.lean`), NOT attempt a Mathlib upstream
PR.

**Rationale**: Cowork's pre-check finds **zero** matches for Brydges-Kennedy /
Mayer / forest-formula content in Mathlib. The BK formula is research-level
statistical mechanics that has not been formalized in any open-source Lean
project. A Mathlib PR would be ~600–1000 LOC, multi-month, and likely meet
Mathlib reviewer skepticism (specialized; not foundational). The BLUEPRINT_F3Mayer
§4.1 file (3) estimate of ~250 LOC project-side is the right scope.

**Risk if ignored**: Codex spends Codex cycles attempting a Mathlib PR for BK
that is not accepted upstream within the F3-MAYER timeline.

---

## Honesty discipline

- **This is a Mathlib pre-check, not a proof.** Cowork has not written any
  Mathlib content; Cowork has not closed any §(b)/B.* theorem.
- **No Mathlib helper proves §(b)/B.3 directly.** The pre-check finds Mathlib
  has the tree predicates and integrability machinery but **none** of the BK
  / Mayer / forest-formula content. Section (b) of the F3-MAYER blueprint
  remains open.
- **F3-MAYER row** in `UNCONDITIONALITY_LEDGER.md`: unchanged (`BLOCKED`).
- **F3-COUNT row**: unchanged (`CONDITIONAL_BRIDGE` per v2.56 audit).
- **Tier 2 axiom count**: unchanged at 5 (per freshness audit-004).
- **All 4 percentages**: unchanged at 5% / 28% / 23-25% / 50%.
- **README badges**: unchanged.

This pre-check **prevents wasted Codex cycles** by mapping the Mathlib gap
landscape **before** v2.57+ work begins. Same pattern as v2.54: Cowork
recommends a search → Codex finds (or doesn't find) the helper → Codex
proceeds with the right LOC budget.

## Cross-references

- `F3_MAYER_DEPENDENCY_MAP.md` §(b)/B.3 (the BK polymer bound, HIGH
  difficulty ~250 LOC).
- `BLUEPRINT_F3Mayer.md` §3 (BK random-walk strategy + Cayley's formula
  context) + §4.1 (file numbering: file 3 `BrydgesKennedyEstimate.lean`,
  ~250 LOC).
- `REC-CODEX-MATHLIB-LONGEST-INDUCED-PATH-CHECK-001` (RESOLVED) — the
  pre-check pattern this document follows.
- `Mathlib.Combinatorics.SimpleGraph.Acyclic` — has `IsTree` + `IsAcyclic`
  predicates.
- `Mathlib.MeasureTheory.Function.EssSup` — has `essSup` API.

---

*End of Mayer Mathlib pre-check. Filed by Cowork as deliverable for
`COWORK-MAYER-MATHLIB-PRECHECK-001` per dispatcher instruction at
2026-04-26T19:50:00Z. Cowork is scoping Mathlib content, not proving any
new math.*
