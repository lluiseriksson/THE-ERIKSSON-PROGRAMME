# AUDIT_v186_LATTICEANIMAL_UPDATE.md

**Author**: Cowork agent (Claude), follow-up audit 2026-04-25
**Subject**: progress update on Priority 1.2 (`LatticeAnimalCount.lean`)
between v1.85.0 and post-v1.86.0
**Companion**: extends `AUDIT_v185_LATTICEANIMAL.md`

---

## 0. Headline progress

Between v1.85.0 (10:01 local) and post-v1.86.0 (10:49 local) — a
**48-minute window** — Codex added approximately **183 lines of
oracle-clean Lean** to `LatticeAnimalCount.lean`, taking it from
99 → ~282 LOC.

**Steps closed in this window**:

- **§3.1 Reverse-direction bridge — COMPLETE** (PolymerConnected →
  graph reachability + preconnected of induced subgraph)
- **§3.2 Degree bound — PARTIAL** (degree ≤ `plaquetteSiteBall.card`;
  closed-form bound on `plaquetteSiteBall.card` itself still open)

**Steps remaining**:

- §3.2 closed: bound `plaquetteSiteBall.card` by explicit `Δ` (e.g.
  `4d²` or `2d-1` for d=4). Estimated ~50-80 LOC.
- §3.3 Klarner BFS-tree count theorem (the analytic boss).
  Estimated ~150 LOC.
- §3.4 Packaging into `ShiftedConnectingClusterCountBoundExp 1 K`.
  Estimated ~30 LOC.

**Total remaining estimate (revised)**: ~230-260 LOC. Total Priority
1.2 estimate **revised upward**: from ~410 LOC to ~510-540 LOC.

Priority 1.2 progress: **~55% complete** by LOC (282 of ~510).

Estimated time to closure: **2-3 hours** at the current cadence.

---

## 1. v1.85.0 → v1.86.0 transition: what landed

### 1.1 v1.85.0 → 4 unbumped commits → v1.86.0

```
v1.85.0  10:01 — lattice-animal plaquette graph scaffold
                 (foundation: graph definition + chain bridge)
        10:05 — F3: expose polymer graph chains
        10:22 — F3: connect polymers to plaquette reachability
        10:35 — F3: lift polymer connectivity to induced graph
        10:43 — F3: package polymer induced preconnectedness
v1.86.0  10:43 — plaquette graph local-neighbor bucket
                 (degree bound infrastructure)
        10:49 — F3: expose plaquette graph neighbor bucket
                 (additional API ergonomics)
```

### 1.2 §3.1 Reverse bridge — fully closed

The reverse bridge from `PolymerConnected` to graph-theoretic
properties needed by Mathlib's `SimpleGraph` API is now complete:

```lean
polymerConnected_exists_plaquetteGraph_chain :
    PolymerConnected X → p ∈ X → q ∈ X →
      ∃ path, ... ∧ List.IsChain (plaquetteGraph d L).Adj path

plaquetteGraph_reachable_of_chain_endpoints :
    ... → (plaquetteGraph d L).Reachable p q

polymerConnected_plaquetteGraph_reachable :
    PolymerConnected X → p ∈ X → q ∈ X →
      (plaquetteGraph d L).Reachable p q

plaquetteGraph_induce_reachable_of_chain_endpoints :
    ... → ((plaquetteGraph d L).induce {x | x ∈ X}).Reachable
            ⟨p, hpX⟩ ⟨q, hqX⟩

polymerConnected_plaquetteGraph_induce_reachable :
    PolymerConnected X → p ∈ X → q ∈ X →
      ((plaquetteGraph d L).induce ...).Reachable ⟨p, hpX⟩ ⟨q, hqX⟩

polymerConnected_plaquetteGraph_induce_preconnected :
    PolymerConnected X → ((plaquetteGraph d L).induce ...).Preconnected
```

This is the **terminal API surface** for §3.3: the BFS-tree count
proof can now consume `(plaquetteGraph d L).induce X` as a
standard SimpleGraph and use Mathlib's `Connected` / `Preconnected`
machinery.

**Quality**: matches the §3.1 plan in `AUDIT_v185_LATTICEANIMAL.md`
character-for-character. Codex chose to expose both `Reachable`
and `Preconnected` flavors, which is more useful API surface than
my plan suggested. **Constructive deviation in the right direction.**

### 1.3 §3.2 Degree bound — bounded by site-ball, but site-ball
itself not yet quantitatively bounded

The new declarations:

```lean
plaquetteSiteBall (d L : ℕ) [NeZero d] [NeZero L]
    (p : ConcretePlaquette d L) : Finset (ConcretePlaquette d L) :=
  Finset.univ.filter fun q => siteLatticeDist p.site q.site ≤ 1

plaquetteGraph_neighborFinset_eq_filter :
    (plaquetteGraph d L).neighborFinset p =
      Finset.univ.filter fun q => q ≠ p ∧ siteLatticeDist p.site q.site ≤ 1

plaquetteGraph_neighborFinset_subset_siteBall :
    (plaquetteGraph d L).neighborFinset p ⊆ plaquetteSiteBall d L p

plaquetteGraph_degree_le_siteBall_card :
    (plaquetteGraph d L).degree p ≤ (plaquetteSiteBall d L p).card
```

This **partially** closes §3.2 of my audit: the degree is now
bounded by a finite quantity (`plaquetteSiteBall.card`), but that
quantity itself is not yet given a closed-form upper bound.

**What's missing for full §3.2**: a theorem of the form
```
plaquetteSiteBall_card_le :
    (plaquetteSiteBall d L p).card ≤ (4 * d * d : ℕ)
```
(or the tighter `2d - 1` if Codex pursues that route).

**Why Codex did §3.2 in two sub-steps rather than one**:

The two-step approach (degree ≤ ball_card, then ball_card ≤ Δ) is
cleaner than my one-step plan because:
- The intermediate `plaquetteSiteBall` is a useful object on its
  own (it's the local cluster of plaquettes that any future
  combinatorial argument can reason about).
- The ball-card bound depends on lattice geometry; isolating it
  separates "graph-theoretic" content from "lattice-geometric"
  content.

This is a **better factoring** than my audit suggested. I'll
mention this as a constructive deviation.

### 1.4 What §3.2 needs to close

Two equivalent paths:

- **Direct**: prove `plaquetteSiteBall_card_le_4d²` by counting
  plaquettes per site (each site has at most ~`d(d-1)/2` plaquette
  basepoints) and counting sites within distance 1 of `p.site`
  (the site ball has at most `(2d+1)^d` sites; for d=4 with
  Manhattan distance 1, it's exactly `2d+1 = 9`). Combining:
  `card ≤ 9 · 6 = 54` for d=4 if oversaturated, tighter with care.
- **Tight**: prove `plaquetteSiteBall_card_le_2d_minus_1` by
  carefully accounting for which plaquettes share base sites with
  `p` and accounting for orientation. Tight bound `2d - 1 = 7`
  for d=4.

Either bound suffices for the F3 chain (per
`F3_CHAIN_MAP.md` §3); the loose one is faster to formalise, the
tight one gives a wider physical β regime.

**Estimated work**: ~50 LOC (loose) or ~100 LOC (tight).

---

## 2. Cadence observation

```
v1.85.0 → v1.86.0 transition:
  Wall-clock time:    42 minutes (10:01 → 10:43)
  Lines added:        ~183 LOC
  Production rate:    ~4.4 LOC/minute  (~260 LOC/hour while focused)
  Commits added:      4 unbumped + v1.86.0 = 5 commits
                      = 1 commit per ~8 minutes
```

This is a **focused-mode** cadence (per `CADENCE_AUDIT.md` §6.2:
"reviewed mode" produces 3.8 commits/h average, but this 42-minute
window is much faster — closer to 7 commits/h burst). The wall-clock
is consistent with what's expected of a Codex daemon attacking a
specific blueprint-derived sub-step.

If this rate continues, the remaining ~230-260 LOC for Priority 1.2
closes in **~50-60 minutes** — i.e., Priority 1.2 closure could
land before lunchtime today.

---

## 3. Estimate revision

My original `AUDIT_v185_LATTICEANIMAL.md` §4 estimated:

```
Step               LOC estimate
3.1 Reverse bridge      50
3.2 Degree bound        80
3.3 BFS-tree count     150
3.4 Packaging           30
─────────────────────────
Total remaining        310 (after the 99 LOC of v1.85.0)
Total Priority 1.2     410
```

Revised after v1.86.0:

```
Step                    Original   Actual / Revised
3.1 Reverse bridge          50      ~120 (more declarations than expected)
3.2a Degree bound (graph)   80      ~70  (the part Codex did)
3.2b Site-ball card bound    -      ~50-80 (sub-step I didn't anticipate)
3.3 BFS-tree count         150      150 (unchanged)
3.4 Packaging               30      30 (unchanged)
─────────────────────────────────────
Total LOC               ~410     ~520-550
```

**The revision adds ~110-140 LOC** to the total estimate. Most of
the increase comes from §3.1 (Codex exposed both `Reachable` and
`Preconnected` variants, plus chain-with-endpoints intermediate)
and §3.2's two-step factoring.

**This is not an underrun risk** — it just means the v1.85 audit
underestimated the API surface needed for clean integration with
Mathlib's `SimpleGraph`. The work is being done at a healthy pace;
there's no concerning slowdown.

---

## 4. Quality assessment

All v1.85→v1.86 declarations:

- ✓ Print canonical oracle `[propext, Classical.choice, Quot.sound]`
  (verified per `#print axioms` block at end of file)
- ✓ Match the planning in `AUDIT_v185_LATTICEANIMAL.md` either
  exactly or with constructive improvements
- ✓ No `sorry`, no axioms outside Experimental
- ✓ Build succeeds (per v1.86.0 release note)

**No issues to flag.**

---

## 5. What to expect next (predictions)

Based on the trajectory:

1. **Next ~1 hour**: §3.2b closes — Codex proves a closed-form
   bound on `plaquetteSiteBall.card`. Expected commits like
   "F3: bound site-ball cardinality" or similar.
2. **Following ~1-2 hours**: §3.3 begins — Codex starts the
   BFS-tree count induction. This is the analytic boss; expect
   slower per-commit progress as the proofs are deeper.
3. **Following ~30 min**: §3.4 packaging produces
   `connecting_cluster_count_exp_bound : ShiftedConnectingClusterCountBoundExp 1 K`.
4. **Final commit**: integrates the witness with
   `PhysicalShiftedF3CountPackageExp` for the F3 chain.

**Expected version sequence**: v1.87.0 (site-ball card bound),
v1.88.0 (BFS-tree count), v1.89.0 (witness package). All within
~3-4 hours.

If §3.3 turns out harder than expected, the version count between
"BFS-tree count begins" and "BFS-tree count complete" may stretch
across multiple intermediate versions with sub-lemmas.

---

## 6. Recommendation for next Cowork session

**No action needed in this session.** Codex is executing the
planned trajectory faithfully and at a healthy cadence. The
Cowork ↔ Codex governance loop is working as designed.

When Priority 1.2 closes (i.e., when
`connecting_cluster_count_exp_bound` lands), a follow-up audit
similar to `CODEX_EXECUTION_AUDIT.md` would be appropriate to:

- Verify the witness is character-for-character what
  `BLUEPRINT_F3Count.md` §−1 specified.
- Confirm the constants `(C_conn, K)` chosen by Codex match
  expectations (likely `C_conn = 1`, `K = 4d²` loose or `K = 2d-1`
  tight).
- Update `STATE_OF_THE_PROJECT.md` Priority 1.2 → DONE.
- Update `CODEX_CONSTRAINT_CONTRACT.md` priority queue to
  promote Priority 2.x to active.
- Update `F3_CHAIN_MAP.md` to mark the F3-Count witness as closed.

The next "Cowork-relevant" milestone after Priority 1.2 closes is
the start of Priority 2.x (F3-Mayer scaffolding via
`MayerInterpolation.lean`). At that point, a fresh `BLUEPRINT_F3Mayer.md`
review pass would be warranted.

---

*Update audit complete 2026-04-25 by Cowork agent. All going well.*
