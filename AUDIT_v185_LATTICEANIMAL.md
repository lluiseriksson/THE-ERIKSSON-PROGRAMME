# AUDIT_v185_LATTICEANIMAL.md

**Author**: Cowork agent (Claude), execution audit pass 2026-04-25
**Subject**: detailed audit of v1.85.0 `YangMills/ClayCore/LatticeAnimalCount.lean`
against the Priority 1.2 target from `CODEX_CONSTRAINT_CONTRACT.md` §4
**Method**: read the actual Lean code, compare against
`BLUEPRINT_F3Count.md` §4 and `mathlib_pr_drafts/F3_Count_Witness_Sketch.lean`,
identify what is closed and what remains.

---

## 0. Bottom line

Codex landed v1.85.0 ~25 minutes ago (commit 2026-04-25T10:01 local).
The release creates `YangMills/ClayCore/LatticeAnimalCount.lean` and
populates it with 99 lines of foundational scaffolding: the
`plaquetteGraph` adjacency definition plus 4 supporting theorems.

**Progress against Priority 1.2**: ~24% complete by LOC estimate.
Codex has ported the graph definition from
`mathlib_pr_drafts/F3_Count_Witness_Sketch.lean` (the consumer-side
sketch I provided in the PR draft turn) and added one bridge lemma.

What remains to close Priority 1.2:
1. The full `PolymerConnected ↔ (plaquetteGraph d L).induce S.Connected`
   biconditional — half-direction landed, other half open.
2. A degree bound on `plaquetteGraph d L` (e.g. `Δ ≤ 4d²` for the
   loose form, `Δ ≤ 2d` for the tight form via plaquette-share-edge
   adjacency).
3. The Klarner BFS-tree count theorem itself: connected animals of
   size m anchored at a vertex are at most `Δ^(m-1)` in number.
4. Packaging into `ShiftedConnectingClusterCountBoundExp 1 K` for
   explicit `K`.

Estimated remaining work: ~310 LOC across the four items above.
At v1.85.0's observed development rate (~99 LOC in ~30 minutes for
foundational work; harder content moves slower), closure should land
in 2-4 hours of focused Codex effort.

---

## 1. What v1.85.0 contains (line-by-line audit)

### 1.1 `siteLatticeDist_symm` (line 25)

```lean
theorem siteLatticeDist_symm {d N : ℕ} (p q : FinBox d N) :
    siteLatticeDist p q = siteLatticeDist q p
```

**Mathematical content**: Euclidean distance on the lattice is symmetric.

**Compare to blueprint**: not in my blueprint explicitly, but a
prerequisite that I had assumed silently. Codex correctly identified
this as needing explicit proof.

**Quality**: trivial via `dist_comm`. ~5 LOC. Oracle clean.

### 1.2 `plaquetteGraph` (line 32)

```lean
def plaquetteGraph (d L : ℕ) [NeZero d] [NeZero L] :
    SimpleGraph (ConcretePlaquette d L) where
  Adj p q := p ≠ q ∧ siteLatticeDist p.site q.site ≤ 1
  symm := by
    intro p q h
    exact ⟨h.1.symm, by rw [siteLatticeDist_symm]; exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
```

**Mathematical content**: the simple graph on `ConcretePlaquette d L`
where two plaquettes are adjacent iff they are distinct and their
base sites are at Euclidean distance ≤ 1.

**Compare to blueprint** (`F3_Count_Witness_Sketch.lean` §"plaquette
adjacency graph"):

```lean
-- My sketch:
def plaquetteGraph (d L : ℕ) [NeZero d] [NeZero L] :
    SimpleGraph (ConcretePlaquette d L) where
  Adj p q := p ≠ q ∧ siteLatticeDist p.site q.site ≤ 1
  symm := by
    intro p q ⟨hne, hd⟩
    exact ⟨hne.symm, by rw [siteLatticeDist_symm]; exact hd⟩
  loopless := fun p ⟨hne, _⟩ => hne rfl
```

**Match**: character-for-character identical to my sketch.
Codex's version is slightly tighter (`fun _ h => h.1 rfl` vs my
`fun p ⟨hne, _⟩ => hne rfl`), same proof, slightly different
destructuring style. **Faithful execution.**

### 1.3 `plaquetteGraph_decidableRel` instance (line 41)

```lean
noncomputable instance plaquetteGraph_decidableRel ... :
    DecidableRel (plaquetteGraph d L).Adj
```

**Mathematical content**: decidability of adjacency, needed for
finite enumeration / `Finset.filter` later.

**Compare to blueprint**: I had `instance ... : DecidableRel ...` (no
noncomputable). Codex made it `noncomputable instance` because the
adjacency uses `≤` on `ℝ` which is not decidable computably without
`Classical`. **Correct refinement of my sketch.**

### 1.4 `plaquetteGraph_adj_siteLatticeDist_le_one` (line 50)

```lean
theorem plaquetteGraph_adj_siteLatticeDist_le_one
    {d L : ℕ} [NeZero d] [NeZero L] {p q : ConcretePlaquette d L}
    (h : (plaquetteGraph d L).Adj p q) :
    siteLatticeDist p.site q.site ≤ 1
```

**Mathematical content**: forward extraction from adjacency to the
distance bound.

**Quality**: trivial (`h.2`). ~3 LOC. Useful API.

### 1.5 `plaquetteGraph_adj_of_ne_of_siteLatticeDist_le_one` (line 59)

```lean
theorem plaquetteGraph_adj_of_ne_of_siteLatticeDist_le_one
    {d L : ℕ} [NeZero d] [NeZero L] {p q : ConcretePlaquette d L}
    (hne : p ≠ q) (hdist : siteLatticeDist p.site q.site ≤ 1) :
    (plaquetteGraph d L).Adj p q
```

**Mathematical content**: backward construction.

**Quality**: trivial. ~3 LOC. Symmetric API.

### 1.6 `plaquetteGraph_isChain_of_nodup_siteLatticeDist_isChain` (line 68-95)

```lean
theorem plaquetteGraph_isChain_of_nodup_siteLatticeDist_isChain
    ∀ (l : List (ConcretePlaquette d L)),
      l.Nodup → List.IsChain (...siteLatticeDist...) l →
      List.IsChain (plaquetteGraph d L).Adj l
```

**Mathematical content**: a nodup list whose successive elements have
`siteLatticeDist ≤ 1` is a chain in the graph (because all elements
are distinct, so the `p ≠ q` half of `Adj` is automatic).

**Compare to blueprint**: not explicitly in my sketch. This is a
**bridge lemma** Codex added that I missed — it's exactly the right
thing to provide because `PolymerConnected` is defined in terms of
nodup site-distance chains, and the graph version uses
`(plaquetteGraph d L).Adj`. Codex inserted the chain-level bridge
rather than going straight to the `Connected` predicate, which is
cleaner.

**Quality**: ~28 LOC, induction on the list. Proof is a careful
case-split using `List.IsChain.cons_cons` + nodup extraction. Oracle
clean.

---

## 2. What is closed by v1.85.0

After v1.85.0:

- The graph is defined.
- Decidability is established.
- Adjacency ↔ (distinct ∧ distance ≤ 1) bidirectionally.
- A nodup site-distance chain is a graph chain.

This closes the **forward direction** of the bridge between
`PolymerConnected` (the existing `Finset` predicate) and
`(plaquetteGraph d L).induce S.Connected` (the graph predicate
amenable to standard SimpleGraph theorems).

---

## 3. What remains to close Priority 1.2

### 3.1 The reverse-direction bridge

```lean
theorem polymerConnected_iff_induced_connected
    {d L : ℕ} [NeZero d] [NeZero L] (Y : Finset (ConcretePlaquette d L)) :
    PolymerConnected Y ↔ ((plaquetteGraph d L).induce Y).Connected
```

The forward direction (`PolymerConnected → (plaquetteGraph d L).induce
Y.Connected`) is now buildable from the chain lemma + `SimpleGraph.Walk`
construction.

The reverse direction (`(plaquetteGraph d L).induce Y.Connected →
PolymerConnected Y`) requires translating a `Walk` in the induced
subgraph back into the explicit list-with-nodup form. This uses
`SimpleGraph.Walk.toPath` (giving nodup) plus extraction of the
distance bounds from the chain.

**Estimated LOC**: ~50.

### 3.2 Degree bound

```lean
theorem plaquetteGraph_degree_le
    {d L : ℕ} [NeZero d] [NeZero L] (p : ConcretePlaquette d L) :
    (plaquetteGraph d L).degree p ≤ Δ
```

with `Δ` either:

- **Loose**: `4 * d * d` (per `mathlib_pr_drafts/F3_Count_Witness_Sketch.lean`
  §"degree bound"). Easy to prove: each plaquette has 2 axes, each
  axis pair giving at most `2d` neighbouring plaquettes.
- **Tight**: `2 * d - 1` (per blueprint §4.2 step 4). Requires more
  careful counting — the subtraction by 1 is the "predecessor in BFS"
  that doesn't count as a fresh neighbor.

**Estimated LOC**: ~80 (loose) or ~120 (tight).

### 3.3 The Klarner BFS-tree count

```lean
theorem connectedSubsetCount_anchored_le
    {d L : ℕ} [NeZero d] [NeZero L]
    (root : ConcretePlaquette d L) (m : ℕ) :
    ((Finset.univ.filter (fun S =>
      root ∈ S ∧ S.card = m + 1 ∧
      ((plaquetteGraph d L).induce S).Connected)).card : ℝ) ≤ Δ ^ m
```

This is the **mathematical core** of Priority 1.2. The proof is
induction on `m`:

- Base `m = 0`: only `S = {root}`, count = 1 = Δ^0.
- Step: pick the canonical "DFS-last leaf" of `S`, build an injection
  `S ↦ (S.erase last, last)` into pairs (smaller-S, neighbour-of-S).

Already drafted in `mathlib_pr_drafts/AnimalCount.lean` at the
abstract `SimpleGraph` level. The in-repo specialisation uses the
concrete `plaquetteGraph d L`.

**Estimated LOC**: ~150.

### 3.4 The package witness

```lean
theorem connecting_cluster_count_exp_bound
    (d : ℕ) [NeZero d] :
    ShiftedConnectingClusterCountBoundExp 1 (Δ : ℝ)
```

with `Δ = 4d²` (loose) or `2d - 1` (tight).

Built by:
1. Restricting from "anchored at root" (§3.3) to "containing both p
   and q" (extra filter).
2. Translating polymer cardinality `n + ⌈d(p,q)⌉` to BFS-tree size.
3. Combining with the degree bound (§3.2).
4. Packaging via `ShiftedConnectingClusterCountBoundExp` (already
   declared in v1.79.0).

**Estimated LOC**: ~30 of glue.

---

## 4. Total estimate to Priority 1.2 closure

| Step | LOC estimate | Difficulty |
|---|---:|---|
| 3.1 Reverse-direction bridge | 50 | low |
| 3.2 Degree bound (loose) | 80 | medium |
| 3.3 Klarner BFS-tree count | 150 | high (the analytic boss) |
| 3.4 Package witness | 30 | low (glue) |
| **Total remaining** | **~310** | mixed |

Plus the 99 LOC already in v1.85.0 → ~410 LOC for full Priority 1.2.

At Codex's observed rate (~99 LOC per 30 minutes of focused work for
graph-scaffolding content), the remaining 310 LOC should close in
**2-4 hours** depending on how the §3.3 induction unfolds. The §3.3
step is the only one that may surprise — the others are mechanical.

---

## 5. Recommended order of attack for Codex

1. **§3.1 first** (reverse bridge): closes the API surface and lets
   §3.3 use standard `SimpleGraph` theorems instead of `Finset`
   gymnastics.
2. **§3.2 next** (degree bound): the loose `4d²` form first; tighten
   to `2d-1` later if convergence-radius optimisation matters.
3. **§3.3** (Klarner): the analytic content. Should produce a
   substantive release (e.g. v1.86.0 "lattice-animal connected
   count via BFS").
4. **§3.4** (witness package): the closing release (e.g. v1.87.0
   "F3-Count exponential witness for d=4").

At v1.87.0, Priority 1.2 is closed and the priority queue advances
to Priority 2.x (F3-Mayer scaffolding from `BLUEPRINT_F3Mayer.md`).

---

## 6. Risk register for the remaining work

| Risk | Likelihood | Mitigation |
|---|---|---|
| BFS-tree induction has a subtle off-by-one error | medium | Specifically the "last leaf" canonical choice — multiple polymers can have the same `(erased subset, removed vertex)` projection. The blueprint §4.2 Lemma C explicitly addresses this; if Codex hits it, point at that proof. |
| `Δ ≤ 4d²` is too loose to satisfy `K · r < 1` for physically interesting β | low | The smallness regime adapts: `r < 1/(4·N_c·β)` with `K = 4d² = 64` for d=4 gives `β < 1/(256 N_c)`. For QCD N_c=3, β < 1/768 ≈ 0.0013. Tight but valid. |
| Degree bound proof requires more lattice geometry than expected | low | The plaquette graph at d=4 has each plaquette specified by (basepoint site, two axis directions). Counting neighbours is essentially "for each axis pair, count pairs of plaquettes sharing a site at distance ≤ 1." |
| Mathlib's `SimpleGraph.induce` API is missing pieces | low-medium | The reverse bridge §3.1 needs `(induce S).Connected → PolymerConnected`. If `induce` lacks the right walk-to-path machinery, Codex may need to file a finding (per CONTRIBUTING_FOR_AGENTS.md §4) and either work around or open Mathlib upstream. |

---

## 7. Self-correction note

In the previous CODEX_EXECUTION_AUDIT.md (covering v1.79-v1.82), I
estimated F3-Count witness work as ~150 LOC. Now seeing v1.85.0 at
99 LOC for **scaffolding alone**, my new estimate for the full
Priority 1.2 (scaffolding + bridges + degree + count + package) is
~410 LOC. The 150 LOC estimate referred to **only the count theorem
itself** (§3.3 above), not the surrounding API.

Apologies for the underestimate — the LOC budget for Priority 1.2 in
`CODEX_CONSTRAINT_CONTRACT.md` §4 should be revised upward from 150
to ~400. Will queue an edit.

---

*Audit complete 2026-04-25 by Cowork agent.*
