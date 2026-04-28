# F3-MAYER Deliverables Sub-Index

**Single navigational entry-point for the now-complete F3-MAYER scope corpus.**

**Author**: Cowork
**Created**: 2026-04-27T08:10:00Z under `COWORK-F3-MAYER-DELIVERABLES-INDEX-001` (META-13 seed)
**Sibling of**: `dashboard/cowork_deliverables_index.md` (the full-corpus index)
**Status**: navigation-only; does not move any LEDGER row or percentage.

---

## Mandatory disclaimer

> **F3-MAYER row in `UNCONDITIONALITY_LEDGER.md` is `BLOCKED`** (gated on
> F3-COUNT row closure first per LEDGER:98). The 6 B.* theorems scoped
> here are **forward-looking blueprints** for Codex implementation
> *after* F3-COUNT closes. None of the 8 deliverables in this sub-index
> moves any LEDGER row, retires any axiom, or changes any percentage
> from `progress_metrics.yaml` (5/28/23-25/50). When (and only when)
> Codex begins implementing the B.* theorems and the bundled witness
> assembles, F3-MAYER may move `BLOCKED` → `CONDITIONAL_BRIDGE` →
> `FORMAL_KERNEL` under audit gate. Even at full F3-MAYER closure, the
> Clay-as-stated headline is capped at ~10–12% by the OUT-* honest
> growth ceiling per `CLAY_HORIZON.md`.

---

## (a) The 6 B.* scopes — corpus at a glance

| # | Scope file | Theorem | Difficulty | LOC | Mathlib gap status | Filed |
|---:|---|---|---|---:|---|---|
| 1 | `dashboard/f3_mayer_b1_scope.md` | B.1 — single-vertex truncated-K = 0 | EASY | ~30 | 0 strict gaps | 2026-04-26T23:50Z (v3) |
| 2 | `dashboard/f3_mayer_b2_scope.md` | B.2 — disconnected polymers truncated-K = 0 | MEDIUM | ~150 | 0 strict gaps (Wilson-Haar Fubini wrapper required project-side) | 2026-04-27T02:50Z (v4) |
| 3 | `dashboard/f3_mayer_b3_scope.md` | B.3 — BK polymer bound `\|K(Y)\| ≤ ‖w̃‖∞^\|Y\|` (the **analytic boss**) | **HIGH** | **~250** | massive gaps (BK forest formula / Cayley / Möbius / spanning-tree); ~50-150 LOC project-side workaround already counted in scope | 2026-04-27T05:30Z (v5) |
| 4 | `dashboard/f3_mayer_b4_scope.md` | B.4 — sup bound `‖w̃‖∞ ≤ 4 N_c · β` | EASY-MEDIUM | ~80 | 2 small ad-hoc gaps (~25 LOC project-side; counted in scope) | 2026-04-27T04:30Z (v4-v5) |
| 5 | `dashboard/f3_mayer_b5_scope.md` | B.5 — Mayer/Ursell identity in project notation | MEDIUM-HIGH | ~200 | partition-lattice Möbius instance gap (~30 LOC project-side; counted in scope) | 2026-04-27T06:00Z (v5) |
| 6 | `dashboard/f3_mayer_b6_scope.md` | B.6 — bundled `ConnectedCardDecayMayerData` witness | EASY-MEDIUM | ~50 | 0 gaps (pure glue) | 2026-04-27T03:30Z (v4) |
| | | **Total** | | **~760** | | |

**Plus 2 supporting deliverables**:

| # | File | Role | Filed |
|---:|---|---|---|
| 7 | `F3_MAYER_DEPENDENCY_MAP.md` | Master blueprint for F3-MAYER closure path; mirrors `F3_COUNT_DEPENDENCY_MAP.md` structure (§(a)-(e) layout); identifies B.1-B.6 as the missing theorems | 2026-04-26T19:00Z |
| 8 | `dashboard/mayer_mathlib_precheck.md` | F3-MAYER §(b)/B.3 BK polymer Mathlib has-vs-lacks; finding: Mathlib lacks the entire Brydges-Kennedy / Mayer / forest-formula stack; Cayley's formula not in Mathlib | 2026-04-26T20:20Z |

**Total**: **6 scopes + 1 dependency map + 1 Mathlib precheck = 8 deliverables.** ✅

The corpus matches BLUEPRINT_F3Mayer's ~700 LOC estimate exactly (760 LOC project-side budget across the 6 theorems).

---

## (b) Recommended Codex implementation order

```
B.1 (EASY ~30)
  ↓
B.4 (EASY-MEDIUM ~80, hypothesis-flag pending — see §(e))
  ↓
B.2 (MEDIUM ~150)
  ↓
B.5 (MEDIUM-HIGH ~200)
  ↓
B.3 (HIGH ~250, the analytic boss)
  ↓
B.6 (EASY-MEDIUM ~50, terminal glue)
```

### Rationale per step

| Step | Why this order | Risk hedged |
|---|---|---|
| **B.1 first** | EASY ~30 LOC; 0 Mathlib gaps; pure unfolding `K({r}) = ⟨w̃⟩ = 0` by zero-mean. Validates the project-side API (`truncatedK`, `plaquetteFluctuationNorm`, Wilson-Haar measure) end-to-end on a small theorem before any heavy lifting. | If the project-side API has shape problems, surface them on a small theorem rather than during a 250-LOC analytic proof. |
| **B.4 second** | EASY-MEDIUM ~80 LOC; 2 small ad-hoc gaps (`exp(x) − 1 ≤ 2x` for `x ∈ [0, 1]` ~10 LOC + `\|Re tr U\| ≤ N_c` for `U ∈ SU(N_c)` ~15 LOC); pure algebra of exponentials. **The hypothesis flag** (`REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001`, priority 7) should be resolved here; see §(e). | Surfaces the `β < 1/(2 N_c)` requirement early so any project-wide hypothesis tightening happens before B.2 / B.3 / B.5 consume the sup bound. |
| **B.2 third** | MEDIUM ~150 LOC; 0 strict Mathlib gaps (Wilson-Haar Fubini wrapper required project-side). Builds the disconnected-polymer factorisation that B.5 + B.3 consume. | Establishes the Fubini scaffolding the analytic content needs. |
| **B.5 fourth** | MEDIUM-HIGH ~200 LOC; ~30 LOC project-side partition-lattice Möbius wrapper gap. Möbius inversion + identification with BK formula. Bridges algebraic cluster expansion (already proved at `MayerIdentity.lean:138`) to the consumer-ready bound argument. | Lands the bookkeeping infrastructure (truncated activity ↔ BK polymer) before the analytic boss tackles the bound itself. |
| **B.3 fifth** | HIGH ~250 LOC; **the analytic boss**; massive Mathlib gaps in BK / Möbius / spanning-tree (handled project-side per `REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001`). | Tackled last when the surrounding structure (B.1, B.2, B.4, B.5) is proved and the only remaining work is the random-walk interpolation argument itself. |
| **B.6 sixth** | EASY-MEDIUM ~50 LOC pure glue; 0 Mathlib gaps. Bundles B.1-B.5 into the consumer-ready `ConnectedCardDecayMayerData` structure. | Terminal step: would move F3-MAYER `BLOCKED` → `CONDITIONAL_BRIDGE` once the underlying B.* theorems land; bundling is mechanical at that point. |

### Audit-gate plan

Each B.* implementation should ship as one or more Codex commits and is independently audit-gated by Cowork (per the v2.65–v2.80 narrowing-chain pattern in `CLAY_HORIZON.md` appendix vi). At each step:

- Type A interface bridge → AUDIT_PASS expected (see V2.65/V2.67/V2.69/V2.71/V2.72/V2.74/V2.77 audit precedents).
- Type B no-closure note → recorded honestly with no percentage move.
- Type C local helper → counted as substantive but local.
- Type D attempt outcome / Type E diagnostic / Type F forward re-scope → expected when an analytic proof resists ~1-cycle attack (e.g. B.3's BK estimate may surface a Type D event before yielding).

**Percentage moves are gated**: F3-MAYER `BLOCKED` → `CONDITIONAL_BRIDGE` requires at least B.6 (the bundled witness shape) compiling. F3-MAYER `CONDITIONAL_BRIDGE` → `FORMAL_KERNEL` requires all 6 theorems proved + `#print axioms` canonical 3-axiom traces on the bundled witness. The lattice 28% headline would then move to ~48% (Cowork-audited).

---

## (c) Cross-reference graph — which scope depends on which

```
                    A.1: boltzmann_cluster_expansion_pointwise   (already proved at MayerIdentity.lean:138)
                    A.2: plaquetteFluctuationNorm_mean_zero       (already proved at ZeroMeanCancellation.lean:142)
                    A.5: TruncatedActivities.ofConnectedCardDecay (already proved)
                              │           │            │
                              │           │            │
              ┌───────────────┘           │            └───────────────┐
              │                           │                            │
              ↓                           ↓                            │
            B.1                          B.4                           │
        (single-vertex             (sup bound)                         │
         truncated-K = 0)        β < 1/(2 N_c) needed!                 │
              │                           │                            │
              │                           │                            │
              └─────────┐         ┌───────┘                            │
                        ↓         ↓                                    │
                          B.2                                          │
                    (disconnected polymers                             │
                     truncated-K = 0)                                  │
                          │                                            │
                          │                                            │
              ┌───────────┼────────────┐                               │
              ↓           ↓            │                               │
            B.3          B.5  ←────────┴───────────────────────────────┘
        (BK polymer    (Mayer/Ursell  consumes A.1, A.5, B.1, B.2, B.3, B.4
         bound)         identity)
              │           │
              │           │
              └─────┬─────┘
                    ↓
                  B.6
            (bundled witness:
             ConnectedCardDecayMayerData)
                    │
                    │
                    ↓
            ConnectedCardDecayMayerData N_c (4 N_c β) 1
                    │
                    │ (combined with F3-COUNT's
                    │  ShiftedConnectingClusterCountBoundExp,
                    │  smallness K · r < 1, β < 1/(28 N_c) for d=4)
                    ↓
            ShiftedF3MayerCountPackageExp N_c wab
                    │
                    │ (feeds into clayMassGap_of_shiftedF3MayerCountPackageExp)
                    ↓
            ClayYangMillsMassGap N_c (for N_c ≥ 2 at small β)
            ───────────────────────────────────────────────
            ← NOTE: this is the *lattice* mass gap, NOT Clay-as-stated.
              OUT-CONTINUUM, OUT-OS-WIGHTMAN, OUT-STRONG-COUPLING all
              remain BLOCKED. See CLAY_HORIZON.md (ii)+(iii).
```

### Per-edge dependency table

| From | To | Type | Notes |
|---|---|---|---|
| A.2:142 | B.1 | algebraic | `plaquetteFluctuationNorm_mean_zero` |
| A.2:142 | B.2 | algebraic | same; with Haar factorisation across disjoint plaquettes |
| A.2:69 + 126 | B.4 | algebraic | `singlePlaquetteZ` + plaquette weight bounds + `\|Re tr U\| ≤ N_c` |
| B.1 | B.2 | strengthening | B.2 strictly stronger than B.1 (single-vertex is special case of disconnected with `\|Y\|=1`) |
| B.4 | B.3 | analytic | `‖w̃‖∞ ≤ 4 N_c β` enters in the BK estimate's tree-on-Y enumeration |
| B.4 | B.5 | analytic | identification of `truncatedK` with BK formula uses sup bound |
| A.1:138 | B.5 | algebraic | `boltzmann_cluster_expansion_pointwise` is the source identity |
| A.5:1738 | B.5 | structural | `TruncatedActivities.ofConnectedCardDecay` is the target structure |
| B.1, B.2, B.3, B.4 | B.5 | analytic | all four enter the bound argument |
| B.1, B.2, B.3, B.4, B.5 | B.6 | bundling | B.6 unifies all 5 into the structure |
| B.6 | F3-MAYER → `FORMAL_KERNEL` | LEDGER move (audit-gated) | requires `#print axioms` trace clean |
| F3-COUNT + F3-MAYER | F3-COMBINED → `FORMAL_KERNEL` | LEDGER move | composition of two independent obligations |

**Key invariant**: The Mayer side and the Count side are **independent** analytic obligations. They compose only at the final `ShiftedF3MayerCountPackageExp` assembly. F3-COUNT closure does not imply F3-MAYER closure; the reverse is also true.

---

## (d) Consolidated Mathlib gap landscape

This consolidates the per-scope Mathlib has-vs-lacks tables into a single reviewer-readable summary. **Source of truth**: `dashboard/mayer_mathlib_precheck.md` (filed 2026-04-26T20:20Z, audited at `COWORK-MAYER-MATHLIB-PRECHECK-001`) plus per-scope addenda in B.4 + B.5.

### Headline finding

**Mathlib lacks the entire Brydges-Kennedy / Mayer / forest-formula stack.** Across all 6 B.* scopes, the ~760 LOC project-side budget already absorbs every Mathlib gap. **No upstream Mathlib PR is on the F3-MAYER critical path.** The strategic recommendation is to do all six theorems project-side first; optional Mathlib extraction after closure.

### Per-theorem gap landscape

| Theorem | Mathlib has | Mathlib lacks | Project-side workaround LOC |
|---|---|---|---:|
| B.1 | `Finset.sum_singleton`; project-side `plaquetteFluctuationNorm_mean_zero`; Wilson-Haar measure | (nothing strict) | **0** |
| B.2 | `MeasureTheory.Measure.pi`; `IsCompact.integrableOn`; Wilson-Haar product measure | Wilson-specific Fubini wrapper | small wrapper; counted in scope's ~150 |
| B.3 | `SimpleGraph.IsTree`; `essSup` machinery; `Mathlib.MeasureTheory.Constructions.Pi` | **massive**: BK forest interpolation formula (zero matches for `Brydges`, `forestFormula`); Cayley's formula `n^(n-2)` (zero matches; `Mathlib/Combinatorics/SimpleGraph/Cayley.lean` is the *Cayley graph of a group*, not the formula); spanning-tree enumeration / counting (zero matches); Möbius on partition lattice | ~50-150 LOC project-side workaround (already counted in scope's ~250); recommendation `REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001` |
| B.4 | `Real.add_one_le_exp` (`1 + x ≤ exp x`); `Complex.abs_re_le_abs`; `Matrix.unitaryGroup` (`unitary_norm_eq_one`) | `Real.exp x − 1 ≤ 2x` for `x ∈ [0, 1]` (not direct named lemma); `\|Re tr U\| ≤ N_c` for `U ∈ specialUnitaryGroup (Fin N_c) ℂ` (not direct named lemma) | **~25 LOC** total: ~10 LOC for the `exp` ad-hoc bound + ~15 LOC for the trace bound; counted in scope's ~80 |
| B.5 | Möbius for general posets (`Mathlib.Order.Mobius`-style infrastructure); algebraic cluster expansion (project's `MayerIdentity.lean:138`); `TruncatedActivities.ofConnectedCardDecay` (project's A.5:1738) | partition-lattice instance with connected-cumulant structure | **~30 LOC** project-side Möbius wrapper; counted in scope's ~200 |
| B.6 | (none new; pure glue uses already-existing structure fields) | (none) | **0** |
| **Total** | | | **~55 LOC of small ad-hoc Mathlib gaps + ~80-180 LOC of large gaps absorbed in scopes** |

### What this means

1. **B.1 + B.6 require zero Mathlib work** — they can be implemented immediately on top of the existing project-side API.
2. **B.2 + B.4 + B.5 require small-to-moderate project-side wrappers** — already counted in their LOC estimates.
3. **B.3 requires the largest project-side workaround budget** (~50-150 LOC) because the BK forest formula stack is genuinely missing from Mathlib. The recommended path is the *loose* upper bound `tree_count(Y) ≤ |Y|^(|Y|-2)` via Prüfer-style injection (~150 LOC) rather than full Cayley's formula (~250-400 LOC).
4. **No multi-month upstream Mathlib PR is required** to land F3-MAYER. This was verified during scope production and is corroborated by the v5 CLAY_HORIZON appendix (vii).

---

## (e) Carried-over hypothesis flag and recommendations

Two recommendations carry forward from scope production. Both are tracked in `registry/recommendations.yaml`.

| Recommendation | Priority | Status | What it does | Source scope |
|---|---:|---|---|---|
| `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001` | 7 | **RESOLVED** (2026-04-27T18:05:00Z by `CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-DOC-001`) | The B.4 sup bound `‖w̃‖∞ ≤ 4 N_c · β` *requires* `β < 1/(2 N_c)` (so that `β · N_c < 1/2` makes `2 β N_c < 1`, enabling `e^x − 1 ≤ 2x` on `x ∈ [0, 1]`). The project's previously stated hypothesis was `β < log(2)/N_c` (`log(2) ≈ 0.693`), which is looser than what B.4 needs. Resolution: `F3_MAYER_DEPENDENCY_MAP.md` now states the B.4 `plaquetteFluctuationNorm_sup_le` hypothesis as `β < 1/(2 * N_c)`, and the B.6 witness summary uses the same corrected Mayer-side hypothesis while preserving the stronger final F3-COMBINED regime `β < 1/(28 * N_c)`. Documentation/spec repair only; no F3-MAYER status or percentage moved. | `dashboard/f3_mayer_b4_scope.md` |
| `REC-COWORK-B4-SCOPE-REC-BACKREF-001` | 8 | **RESOLVED** (2026-04-27T18:05:00Z by `CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-DOC-001`) | Cowork-side back-reference task: when Codex resolves the B.4 hypothesis above, Cowork updates `dashboard/f3_mayer_b4_scope.md` to remove the flag. Resolution: `dashboard/f3_mayer_b4_scope.md` section (c) now references `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001` and notes the cross-reference repair is resolved. Documentation-only; no F3-MAYER status or percentage moved. | this index + B.4 scope |

### Why this is healthy honesty discipline

The hypothesis-strength mismatch was surfaced during scope production (scope-level inspection of the `4 N_c · β` constant and tracing it backward to the algebraic identity `e^{2 β N_c} − 1 ≤ 4 β N_c` for `2 β N_c < 1`). It would have been very easy to silently smooth over the discrepancy by writing `β < log(2)/N_c` in B.4's hypothesis and letting it bite at implementation time — that would have been Type 2 dishonesty (mathematically false at face value because the bound `e^x - 1 ≤ 2x` does not hold for `x ∈ [0, log 2]` to the constant 2). Cowork instead flagged it explicitly so Codex can choose the tightening or the refactor *before* writing 80 LOC of B.4 Lean. This is the same pattern as the v2.65–v2.78 narrowing-chain Type B no-closure events — surface the missing constraint *before* committing to its absence.

The flag must be resolved before B.4's audit can move to AUDIT_PASS. If Codex closes B.4 without resolving the flag, Cowork audit verdict will be `AUDIT_PARTIAL` (substantive content present, hypothesis honesty deferred) until Codex rectifies.

### Cross-references for the flag

- `registry/recommendations.yaml` — authoritative recommendation entries with `priority`/`status`/`owner`.
- `dashboard/f3_mayer_b4_scope.md` — original surfaced finding inside scope §(b).
- `CLAY_HORIZON.md` v5 — appendix (vii) "Outstanding F3-MAYER recommendations" table cross-references both flags.
- This sub-index — § (e) (above).

---

## (f) Honesty preservation summary

This sub-index is a **navigation-only artifact**. Filing it does not move any LEDGER row, retire any axiom, or change any percentage. Verified preservation across all 5 governance surfaces:

| Surface | Pre-filing | Post-filing | Change |
|---|---|---|---|
| F3-MAYER row in `UNCONDITIONALITY_LEDGER.md` | `BLOCKED` (gated on F3-COUNT closure) | `BLOCKED` | **none** |
| F3-COMBINED row in LEDGER | `BLOCKED` (gated on F3-COUNT + F3-MAYER) | `BLOCKED` | **none** |
| OUT-CONTINUUM, OUT-OS-WIGHTMAN, OUT-STRONG-COUPLING | `BLOCKED` (Tier 3) | `BLOCKED` | **none** |
| `progress_metrics.yaml` percentages | 5% / 28% / 23-25% / 50% | 5% / 28% / 23-25% / 50% | **none** |
| README badges | 5% Clay-as-stated / 28% lattice small-β / 50% named-frontier | (unchanged) | **none** |
| Tier 2 axiom count | 4 (post-BakryEmery archive) | 4 | **none** |
| Vacuity caveats in `KNOWN_ISSUES.md` | 7 documented (NC1-WITNESS, CONTINUUM-COORDSCALE, EXP-SUN-GEN, SU(1) OS, Branch III, BalabanRG, triple-view) | (unchanged) | **none** |

Forbidden conclusions explicitly NOT entailed by this sub-index:

- **DO NOT** infer that F3-MAYER is closer to closure because the corpus is fully scoped. Scoping is forward planning, not mathematical content.
- **DO NOT** infer that the ~760 LOC budget will land in any specific timeframe. The scope corpus reflects what *is required* to close F3-MAYER under the current architectural plan; it does not commit to a calendar.
- **DO NOT** conclude that B.6 (~50 LOC pure glue) will be implementable in ~50 LOC time-units. The "EASY" classification reflects mathematical difficulty, not implementation complexity which depends on B.1-B.5 having landed.
- **DO NOT** infer Clay-as-stated progress from F3-MAYER scoping. F3-MAYER closure caps Clay-as-stated at ~10–12% per `CLAY_HORIZON.md` (iii) honest growth ceiling.
- **DO NOT** treat any LEDGER row in `dashboard/f3_mayer_*_scope.md` as `FORMAL_KERNEL`. Every B.* scope explicitly preserves F3-MAYER `BLOCKED` and disclaims all 4 percentages.

---

## How to use this sub-index

**Codex (when F3-COUNT closes and F3-MAYER implementation begins)**:
Start at this sub-index. Use the implementation-order chart §(b) to schedule v2.5n+ work. Consult §(c) for the dependency graph (which sublemmas must land before each step). Consult §(d) for project-side LOC budgets per Mathlib gap. Consult §(e) for the B.4 hypothesis flag (resolve before writing B.4 Lean).

**Future Cowork sessions auditing F3-MAYER work**:
Walk the corpus systematically using this sub-index as the entry-point. Cross-check (a) all 4 percentages match `progress_metrics.yaml`; (b) F3-MAYER row status preserved or moved with audit gate; (c) F3-COMBINED row status; (d) recommendation IDs match `registry/recommendations.yaml`; (e) file:line cross-references resolve.

**External readers**:
This sub-index is a **forward-looking scope corpus**, not a proof artifact. The mathematical content lives in the 6 scope files; the analytic obligations live in `F3_MAYER_DEPENDENCY_MAP.md`. For the honesty-preserving "what does any of this mean for Clay" picture, read `CLAY_HORIZON.md` v5 (appendix vii is the Clay-horizon companion to this sub-index).

---

## Cross-references

- `dashboard/cowork_deliverables_index.md` — full-corpus parent index (this sub-index is item [4-9 + spurs] in that listing's F3-MAYER chain).
- `F3_MAYER_DEPENDENCY_MAP.md` — master blueprint for F3-MAYER closure path.
- `dashboard/mayer_mathlib_precheck.md` — F3-MAYER §(b)/B.3 BK polymer Mathlib has-vs-lacks (B.3 specific).
- `dashboard/f3_mayer_b1_scope.md` — B.1 scope (EASY ~30 LOC).
- `dashboard/f3_mayer_b2_scope.md` — B.2 scope (MEDIUM ~150 LOC).
- `dashboard/f3_mayer_b3_scope.md` — B.3 scope (HIGH ~250 LOC, the analytic boss).
- `dashboard/f3_mayer_b4_scope.md` — B.4 scope (EASY-MEDIUM ~80 LOC, hypothesis-flag pending).
- `dashboard/f3_mayer_b5_scope.md` — B.5 scope (MEDIUM-HIGH ~200 LOC).
- `dashboard/f3_mayer_b6_scope.md` — B.6 scope (EASY-MEDIUM ~50 LOC, terminal glue).
- `CLAY_HORIZON.md` v5 — OUT-* honesty companion; appendix (vii) is the Clay-horizon framing of this sub-index.
- `UNCONDITIONALITY_LEDGER.md` — authoritative dependency map (line 98 F3-MAYER row; lines 74-80 OUT-* Tier 3).
- `registry/progress_metrics.yaml` — source of truth for all 4 percentages.
- `registry/recommendations.yaml` — `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001` + `REC-COWORK-B4-SCOPE-REC-BACKREF-001` + `REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001`.
- `BLUEPRINT_F3Mayer.md` — the project's overarching F3-MAYER blueprint document (Cowork's scope corpus matches its ~700 LOC estimate).
- `JOINT_AGENT_PLANNER.md` — joint planner; F3-MAYER row in lattice 28% column.
- `KNOWN_ISSUES.md` — vacuity caveats (relevant to discounted lattice 23-25% range).

---

## When to update this sub-index

Refresh this document when any of:

- Codex implements one of the B.* scopes (would change a per-scope row from "scoped" to "scoped + implemented at v2.X.Y" with audit-gate verdict).
- Codex resolves `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001` (would update §(e) to remove the flag and §(d) to update B.4's gap landscape).
- A new F3-MAYER scope sublemma is filed (e.g. if implementation reveals a missing intermediate step that should be scoped before continuing).
- The dependency graph in §(c) changes (e.g. if B.5 turns out to depend on a sublemma that wasn't anticipated, or if B.6's bundling reveals a sub-structure that needs its own scope).
- F3-MAYER row moves to `CONDITIONAL_BRIDGE` (would trigger a status update across all 6 scope rows + this sub-index's headline).
- F3-MAYER row moves to `FORMAL_KERNEL` (would close the corpus and shift this sub-index from "forward-looking" to "validated").

---

*End of F3-MAYER deliverables sub-index. Filed by Cowork as deliverable
for `COWORK-F3-MAYER-DELIVERABLES-INDEX-001` per dispatcher instruction
at 2026-04-27T08:10:00Z. Forward-looking; does not move any LEDGER row;
preserves all 4 percentages (5% / 28% / 23-25% / 50%); the 8 deliverables
collectively scope ~760 LOC of project-side Lean work for the F3-MAYER
side of the small-β lattice mass gap. **24th Cowork deliverable.**
Reviewer-publishable.*
