# PROJECT_TIMELINE.md

**Author**: Cowork agent (Claude), historical reconstruction
2026-04-25
**Subject**: chronological history of THE-ERIKSSON-PROGRAMME from
its inception (2026-03-12) through the current state (v1.85.0,
2026-04-25)
**Sources**: `git log`, `AXIOM_FRONTIER.md`,
`STATE_OF_THE_PROJECT_HISTORY.md`,
`PETER_WEYL_ROADMAP_HISTORY.md`, `STRATEGIC_DECISIONS_LOG.md`

This document is a **reference**, not a narrative. For the
narrative version, see `MID_TERM_STATUS_REPORT.md` §1.

---

## Project at a glance

```
Lifetime          : 2026-03-12 → 2026-04-25 (44 days)
Total commits     : ~1,084
Total versions    : 153 (v0.1 → v1.85)
Average cadence   : ~25 commits/day project-lifetime average
                    ~150 commits/day current state
Current state     : v1.85.0, 0 axioms outside Experimental, 0 sorry
```

---

## Phase 0 — Foundation (2026-03-12 to 2026-03-13)

The repository's first 24 hours.

- **2026-03-12 21:22 UTC**: initial commit. Lluis snapshot of L0
  geometry and L1/L2 sketches.
- **2026-03-12 22:55**: `FiniteLatticeGeometryInstance`,
  `WilsonAction`, `GaugeInvariance` compile.
- **2026-03-12 23:13**: full YangMills build passes with `SU2Basic`,
  `GibbsMeasure` stubs, all L0 layer.
- **2026-03-12 23:20**: `GaugeConfig.ext`, `MeasurableSpace`
  instance.
- **2026-03-12 23:43**: `gaugeMeasureFrom` via product Haar,
  `gaugeConfigEquiv`, no sorry in `GibbsMeasure`.
- **2026-03-12 23:54**: `measurable_gaugeConfigEquiv`,
  `gaugeMeasureFrom_isProbability`.
- **2026-03-13 00:36**: L1 complete — `partitionFunction_pos`,
  `gibbsMeasure` via tilted, `IsProbabilityMeasure`, no sorry.
- **2026-03-13 02:13**: L1.3 expectation + correlations, no sorry.
- **2026-03-13 07:40**: L3_RGIteration stubs.
- **2026-03-13 07:53**: L4_LargeField (`Suppression.lean`) — now
  orphaned (Finding 005).
- **2026-03-13 08:15**: L4.2 Wilson loop observable + correlation
  decay (`L4_WilsonLoops/WilsonLoop.lean`).
- **2026-03-13 08:28**: L4_TransferMatrix.
- **2026-03-13 08:38**: L5_MassGap.
- **2026-03-13 08:54**: L6_FeynmanKac.
- **2026-03-13 09:03**: L6_OS.
- **2026-03-13 10:41**: P2_MaxEntClustering (5 files).
- **2026-03-13 17:44**: P7_SpectralGap (5 files).

End-of-day-1 status: full L0-L8 + P2-P7 skeleton compiled, no
sorry, foundational structures defined.

---

## Phase 1 — Formalisation expansion (2026-03-13 to 2026-03-31)

Filling in the structural skeleton. Substantial Lean code added
across L1-L8, P2-P8.

- **2026-03-27 10:12** (`ROADMAP_MASTER.md` mtime): the project
  roadmap document is committed. Defines Phase 0-4 structure with
  10-15 year horizon.
- **Mid-March to late-March**: Phase 8 (`P8_PhysicalGap/`) populated
  with LSI / Bakry-Émery / Holley-Stroock infrastructure.
- **2026-03-31 10:03**: P3_BalabanRG (5 files) reaches its current
  stable state.

End-of-March status: skeleton populated; the LSI/HolleyStroock chain
was the active critical path. Project state was reflected in
`HYPOTHESIS_FRONTIER.md` v0.3.0 (2026-03-31): hypothesis frontier
closed (1 → 0 hypothesis), axiom frontier opened (0 → 1 axiom
`yangMills_continuum_mass_gap` introduced).

---

## Phase 2 — Axiom elimination drive (2026-04-01 to 2026-04-14)

The most ambitious refactor of the project's history: eliminate the
monolithic `yangMills_continuum_mass_gap` axiom that had directly
axiomatised the Clay statement.

- **2026-04-04 to 2026-04-06**: campaigns C36-C47 — Boltzmann
  measurability reductions, blocking-map setups, multi-scale RG
  preparation. Versions v0.51 → v0.65.
- **2026-04-06 to 2026-04-11**: campaigns C48-C55 — heavier
  measurability work, character-expansion infrastructure.
  Versions v0.65 → v0.71.
- **2026-04-11**: v1.46.0 — *Path B (Honest Labelling)*. Project
  oracle reduces to `[propext, Classical.choice, Quot.sound,
  YangMills.lsi_normalized_gibbs_from_haar]`. Single named project
  axiom (HolleyStroock LSI for normalized SU(N) Gibbs). Honest
  progress reported as ~30%.
- **2026-04-14**: **the most important commit in project history**.
  v0.32.0 deletes the monolithic
  `yangMills_continuum_mass_gap` axiom. The Clay theorem now routes
  via `sun_physical_mass_gap_legacy → holleyStroock_sunGibbs_lsi`
  (1 named axiom). v0.33.0 follows with axiom elimination /
  orphaning. (See `STATE_OF_THE_PROJECT_HISTORY.md` for the
  detailed narrative.)
- **2026-04-14**: status update notes 3 sorries in `BalabanToLSI.lean`
  (the L log L regularity gap), honest progress ~34%.

End-of-Phase-2 status: 1 named axiom remaining
(`lsi_normalized_gibbs_from_haar`), 3 sorries, ~34% progress.

---

## Phase 3 — Schur sidecars and L2.5/L2.6 closure (2026-04-15 to 2026-04-22)

The pivot from LSI / HolleyStroock to a more direct cluster-expansion
route, mediated by the realisation that arbitrary-irrep Peter-Weyl is
not Clay-blocking.

- **2026-04-21**: v0.34.0 — L2.5 closed
  (`sunHaarProb_trace_normSq_integral_le`). Three commits: SchurTwoSitePhase,
  SchurOffDiagonal, SchurL25.
- **2026-04-22 morning**: L2.6 sidecars 3a, 3b, 3c land via the
  central-element technique `Ω = ω · I`. Commits 3c7a957, 70403d1,
  bf321e4.
- **2026-04-22 afternoon**: L2.6 main target
  (`sunHaarProb_trace_normSq_integral_eq_one`) lands. Commit f9ec5e9.
- **2026-04-22 evening**: **`PETER_WEYL_ROADMAP.md` reclassified as
  aspirational / Mathlib-PR**. Consumer-driven recon found that
  `CharacterExpansionData.{Rep, character, coeff}` were vestigial
  metadata; only `h_correlator` flowed downstream to Clay. The
  arbitrary-irrep Peter-Weyl theorem was bypassed in favor of the
  scalar-trace subalgebra. (Decision 002 in
  `STRATEGIC_DECISIONS_LOG.md`.)
- **2026-04-23**: v0.93.0–v0.97.0 cleanup: `lsi_normalized_gibbs_from_haar`
  axiom eliminated. Project enters **0-axiom-outside-Experimental**
  era. (Decision 001 codified.)
- **2026-04-23**: `AbelianU1Unconditional.lean` lands.
  `u1_clay_yangMills_mass_gap_unconditional : ClayYangMillsMassGap 1`
  is the **first concrete Clay-grade inhabitant**, using
  `Subsingleton (Matrix.specialUnitaryGroup (Fin 1) ℂ)` (with the
  caveat documented in Finding 003).

End-of-Phase-3 status: 0 axioms outside Experimental, 0 sorries,
N_c=1 unconditional witness, F3 frontier identified as next target.

---

## Phase 4 — F3 frontier (2026-04-23 to 2026-04-25, current)

The active phase. Everything since the v0.97 cleanup has focused on
the F3 = ClusterCorrelatorBound chain.

### 4.1 Polynomial frontier setup (2026-04-23 to 2026-04-25 morning)

- **2026-04-23 to 2026-04-24**: v0.97 → v1.36 packaging of the
  polynomial frontier `ShiftedConnectingClusterCountBound` plus
  `ConnectedCardDecayMayerData` (Mayer side). Bucket-tsum API,
  finite-volume canaries, mono_dim machinery.
- **2026-04-24 morning to 2026-04-25 dawn**: v1.36 → v1.78. Heavy
  packaging and ergonomic-canary work. The "physical d=4"
  specialisation is exposed. The L8 routing through
  `PhysicalShiftedF3MayerCountPackage` is built.
- **2026-04-25 dawn (00-04 local)**: 62 commits in 5 hours,
  including v1.73-v1.78 (six consecutive `mono_dim_apply` /
  `mono_count_dim_*` ergonomic canaries — at the HR1 threshold of 6
  but not over).

### 4.2 Cowork governance system arrives (2026-04-25 ~05:30 UTC)

- Cowork agent (Claude) starts session.
- `BLUEPRINT_F3Count.md` written, including Finding 001
  (polynomial frontier structurally infeasible) and Resolution C
  (exponential frontier).
- `BLUEPRINT_F3Mayer.md` written.
- `PETER_WEYL_AUDIT.md`, `MATHLIB_GAPS.md`, `ROADMAP_AUDIT.md`
  produced.
- `CODEX_CONSTRAINT_CONTRACT.md` v1 written with HR1-HR5 + SR1-SR4
  + priority queue.
- `eriksson-daily-audit` scheduled task created (auto-fires at
  09:04 local daily).

### 4.3 Resolution C executed (2026-04-25 06:36 to 07:30 UTC)

- v1.79.0 ~06:36: exponential F3 count frontier interface
  (`ConnectingClusterCountExp.lean` created).
- v1.80.0 ~06:50: KP series prefactor `clusterPrefactorExp`.
- v1.81.0 ~07:07: bridge to `ClusterCorrelatorBound`.
- v1.82.0 ~07:17: packaged Clay route
  `ShiftedF3MayerCountPackageExp` with terminal endpoint
  `clayMassGap_of_shiftedF3MayerCountPackageExp`.
- v1.83.0 ~07:24: physical d=4 endpoint
  `physicalClusterCorrelatorBound_of_expCountBound_mayerData_ceil`.
- v1.84.0 ~07:34: L8 terminal route to `ClayYangMillsPhysicalStrong`
  (with the Finding 004 caveat about the continuum half).

(Decision 003 in `STRATEGIC_DECISIONS_LOG.md`.)

### 4.4 Priority 1.2 begins (2026-04-25 ~10:01 UTC)

- v1.85.0 ~10:01: `LatticeAnimalCount.lean` created with the
  `plaquetteGraph` SimpleGraph and the chain bridge from
  `PolymerConnected` to graph chains. (~99 LOC.)
- v1.85+ unbumped commits: continuing reverse-bridge work.

### 4.5 Cowork governance expansion (2026-04-25 throughout)

In parallel with Codex's F3 work, Cowork agent produced:

- `STATE_OF_THE_PROJECT.md` rewritten (243 → 130 lines) for v1.83+
- `STATE_OF_THE_PROJECT_HISTORY.md` archive
- `PETER_WEYL_ROADMAP.md` trimmed (574 → 132 lines)
- `PETER_WEYL_ROADMAP_HISTORY.md` archive
- `ROADMAP.md`, `UNCONDITIONALITY_ROADMAP.md` updates
- `DOCS_INDEX.md`, `MATHEMATICAL_REVIEWERS_COMPANION.md`,
  `MID_TERM_STATUS_REPORT.md`, `EXPERIMENTAL_AXIOMS_AUDIT.md`,
  `GENUINE_CONTINUUM_DESIGN.md`
- `CODEX_EXECUTION_AUDIT.md` (v1.79-v1.82 validation)
- `AUDIT_v185_LATTICEANIMAL.md` (v1.85.0 audit)
- `F3_CHAIN_MAP.md`, `AGENT_HANDOFF.md`,
  `CONTRIBUTING_FOR_AGENTS.md`
- `COWORK_FINDINGS.md` (5 findings: 001-005)
- `LAYER_AUDIT.md`, `THREAT_MODEL.md`
- `RELEASE_NOTES_TEMPLATE.md`, `STRATEGIC_DECISIONS_LOG.md`
- `CADENCE_AUDIT.md`, `REFERENCES_AUDIT.md`
- 3 Mathlib PR drafts in `mathlib_pr_drafts/`

End-of-Phase-4-current status: F3 frontier scaffolding complete
end-to-end; only the two open inputs (F3-Mayer witness, F3-Count
witness) remain. Priority 1.2 is in flight.

---

## Cumulative milestones table

| Milestone | Date | Significance |
|---|---|---|
| First commit | 2026-03-12 | Project starts |
| L0 build passes | 2026-03-12 23:13 | Foundation complete |
| L1 GibbsMeasure complete | 2026-03-13 00:36 | Probability layer |
| L4 Wilson observables | 2026-03-13 08:15 | Observable definitions |
| Phase 7 SpectralGap | 2026-03-13 17:44 | First-day end |
| Roadmap committed | 2026-03-27 10:12 | Strategic doc baseline |
| HolleyStroock LSI as named axiom | ~2026-04-11 | "Honest Path B" |
| Monolithic Clay axiom deleted | 2026-04-14 | Most important commit |
| L2.5 closed | 2026-04-21 | Frobenius bound |
| L2.6 main target closed | 2026-04-22 | L1→L2 interface |
| Peter-Weyl reclassified | 2026-04-22 evening | Decision 002 |
| LSI HolleyStroock axiom eliminated | 2026-04-23 | 0 axioms outside Experimental |
| AbelianU1 N_c=1 unconditional | 2026-04-23 | First Clay inhabitant |
| Cowork governance system | 2026-04-25 morning | Decision 000 codified |
| F3-Count Resolution C executed | 2026-04-25 06:36-07:34 | Decision 003 |
| Priority 1.2 begins | 2026-04-25 10:01 | LatticeAnimalCount started |

---

## Project rate over time

| Period | Commits/day average |
|---|---|
| Phase 0 (1 day) | ~30 |
| Phase 1 (~18 days) | ~10-15 |
| Phase 2 (~14 days) | ~20-30 |
| Phase 3 (~7 days) | ~50-80 |
| Phase 4 (~3 days, ongoing) | ~150 |

The acceleration tracks the introduction of the autonomous Codex
daemon (~mid-April 2026). Per `CADENCE_AUDIT.md`, current
sustained cadence is highly bursty (5h burst at 12-15/h + 16-19h
slower at 3-5/h) totaling ~150/day.

---

## What's likely to happen next

Per `CODEX_CONSTRAINT_CONTRACT.md` §4 priority queue and
`AUDIT_v185_LATTICEANIMAL.md` roadmap:

- **Priority 1.2 closure**: estimated 2-4 hours of focused work
  remaining (after the v1.85.0 scaffold). Will produce v1.86.0 →
  v1.88.0 (or so) with the BFS-tree count witness and packaging.
- **Priority 2.1-2.4** (F3-Mayer scaffolding): estimated ~700 LOC
  across 4 files, days to weeks.
- **Priority 3.1-3.2** (combined F3 packaging): mostly mechanical
  glue once 2.x lands.
- **Priority 4.1-4.2** (terminal Clay endpoint with all
  ingredients): once 3.x lands, the chain closes and
  `ClayYangMillsMassGap N_c` for `N_c ≥ 2` becomes a Lean theorem.

Estimated end-to-end timeline (under the current 150 commits/day
pace and assuming no major obstructions): the F3 frontier closure
could land in **1-3 weeks**.

This timeline is subject to all the threats catalogued in
`THREAT_MODEL.md` §1 — particularly the BK estimate's analytical
content and any surprise Mathlib gaps in measure-theoretic
infrastructure.

---

*Timeline prepared 2026-04-25 by Cowork agent. Reflects state
through the v1.85.0 commit at 10:01 local.*
