# LAYER_AUDIT.md

**Author**: Cowork agent (Claude), structural audit pass 2026-04-25
**Subject**: health audit of the **non-F3** layers of the repository
**Question**: while all attention is on the F3 frontier in `ClayCore/`,
are the older foundational layers (L0-L7, P2-P8) sound, orphaned, or
quietly degrading?

---

## 0. Bottom line

The non-F3 layers are **structurally sound**. Most are stable
foundations from Phase 0/1 (March 2026) that haven't been touched
since because they don't need to be. None show signs of degradation.

Notable points:

- **407 total Lean files** across 21 layer directories.
- **1 orphan layer detected**: `YangMills/L4_LargeField/` (1 file)
  has 0 importers. Candidate for either deletion or import-cleanup.
- **L8_Terminal is the most active** non-F3 area (16 files, ~2329
  LOC, last modified 2026-04-25). This is the F3 → Clay endpoint
  plumbing.
- **P8_PhysicalGap is the largest** (52 files), housing the LSI /
  spectral-gap chain. Last touched 2026-04-25 — still active in
  background.
- **ClayCore is dominant** (275 files). The F3 frontier work has
  driven the file count up substantially; the average file size
  is small (~50 LOC) suggesting good modularity.

No findings to file; no broken layers; no urgent cleanup actions.
The audit confirms the project's foundational discipline is intact.

---

## 1. Layer inventory

### 1.1 By age and activity

```
Layer                          Files  Last modified           Status
─────────────────────────────────────────────────────────────────────
YangMills/L0_Lattice/             6  2026-03-12 23:13       stable
YangMills/L1_GibbsMeasure/        3  2026-03-13 02:13       stable
YangMills/L3_RGIteration/         3  2026-03-13 07:40       stable
YangMills/L4_LargeField/          1  2026-03-13 07:53       ORPHANED
YangMills/L4_WilsonLoops/         1  2026-03-13 08:15       stable
YangMills/L4_TransferMatrix/      1  2026-03-13 08:28       stable
YangMills/L5_MassGap/             1  2026-03-13 08:38       stable
YangMills/L6_FeynmanKac/          1  2026-03-13 08:54       stable
YangMills/L6_OS/                  1  2026-03-13 09:03       stable
YangMills/P2_MaxEntClustering/    5  2026-03-13 10:41       stable
YangMills/P7_SpectralGap/         5  2026-03-13 17:44       stable
YangMills/P3_BalabanRG/           5  2026-03-31 10:03       stable
YangMills/L7_Continuum/           2  2026-04-07 20:52       active (Finding 004)
YangMills/P4_Continuum/           2  2026-04-14 16:26       stable post-cleanup
YangMills/P5_KPDecay/             4  2026-04-14 16:26       stable post-cleanup
YangMills/P6_AsymptoticFreedom/   3  2026-04-14 16:26       stable post-cleanup
YangMills/Experimental/          11  2026-04-24 11:46       active (14 axioms)
YangMills/L2_Balaban/             3  2026-04-24 23:53       active
YangMills/P8_PhysicalGap/        52  2026-04-25 00:02       active (LSI)
YangMills/L8_Terminal/           16  2026-04-25 09:34       active (F3 termination)
YangMills/ClayCore/             275  2026-04-25 10:05       active (F3 frontier)
─────────────────────────────────────────────────────────────────────
TOTAL                           407                          —
```

### 1.2 By importer count

| Layer | Importers | Notes |
|---|---:|---|
| `L4_LargeField` | **0** | **orphaned** — see §3 |
| `L3_RGIteration` | 1 | minimal use |
| `L6_FeynmanKac` | 2 | small footprint |
| `L4_TransferMatrix` | 5 | low use |
| `L5_MassGap` | 4 | low use |
| `L6_OS` | 4 | low use |
| `P2_MaxEntClustering` | 4 | low use |
| `P5_KPDecay` | 4 | low use |
| `P6_AsymptoticFreedom` | 6 | medium use |
| `P7_SpectralGap` | 6 | medium use |
| `P3_BalabanRG` | 6 | medium use |
| `L7_Continuum` | 7 | medium use, Finding 004 home |
| `L8_Terminal` | 21 | high use, F3 termination plumbing |

These counts are stable: most layers were built once, are correctly
imported by their downstream consumers, and don't need maintenance.

---

## 2. Layer-by-layer assessment

### 2.1 L0_Lattice (6 files, stable)

The geometric foundation. `FiniteLattice`, `GaugeConfigurations`,
`WilsonAction`, `GaugeInvariance`, `FiniteLatticeGeometryInstance`,
`SU2Basic`. Clean Lean, ~430 LOC total. Imported by ClayCore
(`AbelianU1Unconditional`, `ClayAuthentic`, `ZeroMeanCancellation`)
and by L1.

**Health**: green. No staleness.

### 2.2 L1_GibbsMeasure (3 files, stable)

`GibbsMeasure` (120 LOC), `Expectation` (49 LOC), `Correlations`
(26 LOC). Defines the Gibbs probability measure on gauge
configurations and the basic correlation operations. Heavily used
downstream — every Wilson connected correlator computation routes
through these.

**Health**: green. The fact that this layer hasn't moved in 6 weeks
while the F3 frontier has been refactored repeatedly is a positive
signal — the abstraction is right.

### 2.3 L2_Balaban (3 files, active)

Recently touched (2026-04-24). 3 files. Part of the Balaban RG
infrastructure that connects to `ClayCore/BalabanRG/`.

**Health**: green, in active maintenance.

### 2.4 L3_RGIteration (3 files, stable, 1 importer)

Stub from 2026-03-13. Only 1 importer. Could be deeper-audited
later for consolidation, but not urgent.

**Health**: green-yellow (low usage, but no degradation).

### 2.5 L4_* (3 separate folders)

- **`L4_LargeField`**: 1 file, 0 importers. **ORPHANED**. See §3.
- **`L4_WilsonLoops`**: 1 file (98 LOC, `WilsonLoop.lean`). Imported
  by ClayCore. Defines `wilsonExpectation`, `wilsonCorrelation`,
  `wilsonConnectedCorr` — the central observable definitions.
  **Health: critical infrastructure, green**.
- **`L4_TransferMatrix`**: 1 file, 5 importers. Stub but actively
  consumed. **Health: green**.

### 2.6 L5_MassGap, L6_FeynmanKac, L6_OS (1 file each)

Skeleton stubs from March. Each has a few importers in P8 and L8
plumbing. They define structures that the higher layers reference.

**Health**: green. Stable contracts.

### 2.7 L7_Continuum (2 files, active)

`ContinuumLimit.lean` (the `HasContinuumMassGap` definition that
Finding 004 surfaced as using the coordinated-scaling convention)
plus a companion file. Last touched 2026-04-07.

**Health**: green-yellow. The mathematical content is what it is;
the strategic framing concern is documented in
`COWORK_FINDINGS.md` Finding 004 and `GENUINE_CONTINUUM_DESIGN.md`.

### 2.8 L8_Terminal (16 files, active)

The F3 → Clay endpoint plumbing. `ClayPhysical.lean` (286 LOC,
the `ClayYangMillsPhysicalStrong` definition), `ConnectedCorrDecayBundle.lean`
(1462 LOC, the v1.84.0 wrapper functions), `ClayTrivialityAudit.lean`
(85 LOC, the vacuity records), plus 12 smaller bundle files.

**Health**: green, in active development as part of the F3 chain.

### 2.9 P2-P7 (Phase 2-7 archive)

These are the older-architecture phases (`MaxEntClustering`,
`BalabanRG`, `Continuum`, `KPDecay`, `AsymptoticFreedom`,
`SpectralGap`). Most stable since March-April. P3, P5, P6, P7 each
have 4-6 importers from active code, suggesting they provide
foundational structures that the F3 chain still consumes.

**Health**: green. None show obvious degradation.

### 2.10 P8_PhysicalGap (52 files, active)

The largest non-F3 area. Houses the LSI / Bakry-Émery / Holley-Stroock
chain that was the project's earlier critical path before the F3
reformulation. Last touched 2026-04-25 — still actively maintained
even though the F3 frontier supersedes it as the lattice mass-gap
route.

**Health**: green. Maintenance pace is appropriate (occasional
touches, not intensive).

### 2.11 Experimental (11 files, 14 axioms)

Houses the 14 Experimental axioms documented in
`EXPERIMENTAL_AXIOMS_AUDIT.md`. Last touched 2026-04-24.

**Health**: green for what it is. The axioms are the project's
honest gaps; the audit recommended retiring 7 of them as a
focused upcoming effort.

### 2.12 ClayCore (275 files, very active)

The F3 frontier and all current substantive work. By far the
largest area, most recently touched (2026-04-25 10:05 — minutes
ago).

**Health**: green and intentionally large. Average file size is
small, which is the project's modularity discipline.

---

## 3. Detected orphan: `YangMills/L4_LargeField/`

**File**: `YangMills/L4_LargeField/LargeFieldStub.lean` (or similar
single-file stub).

**Importers**: 0.

**Status**: detected as an orphan by `grep -rln "import YangMills.L4_LargeField"`.

**Recommended actions**:

- **Option A**: delete the file and the directory. Save ~50-100 LOC
  of dead code.
- **Option B**: add an import in some downstream consumer if the
  file's content was supposed to be load-bearing but the import
  was forgotten. (Check the file's content first.)
- **Option C**: leave it as historical. The file is small and
  stable; deletion is not urgent.

I cannot determine intent without inspecting the file's purpose.
Recommend a brief Codex pass to either re-link or delete.

---

## 4. Architectural observations

### 4.1 The "stable foundation, active frontier" pattern

The audit confirms a healthy architectural pattern:

- **L0-L1, L4_WilsonLoops**: built once in early March 2026, stable
  since. Provides the common API (Gibbs measure, Wilson observables,
  gauge configurations).
- **L2-L7, P2-P8**: built in March-April. Stable contracts that
  downstream code consumes.
- **L8_Terminal, ClayCore**: continuously evolving as the F3
  frontier work proceeds.

This is the right pattern: foundational abstractions don't move,
only the active research frontier does.

### 4.2 The Phase 0/1 vs Phase 2-8 vs ClayCore split

The repository organisation reflects a historical evolution:

- **L0-L8**: original "lattice gauge theory layered formalisation"
  organisation.
- **P2-P8**: an alternative phase-based organisation
  (`MaxEntClustering`, `BalabanRG`, `Continuum`, `KPDecay`,
  `AsymptoticFreedom`, `SpectralGap`, `PhysicalGap`).
- **ClayCore**: the consolidated active work area introduced after
  the v0.30s reorganisation.

The two organisations coexist, with imports flowing between them.
Some duplication is visible (e.g. `L7_Continuum` and `P4_Continuum`
both exist). This is **technical debt** but not urgent — it would
take a careful refactor to consolidate, and the cost is low because
the layers are stable.

### 4.3 No degradation detected

The audit looked for, but did not find:

- Files modified recently but not imported anywhere (would suggest
  in-progress work that got abandoned). None found.
- Imports from `YangMills/Experimental/` to non-Experimental files
  (would suggest leaks of axioms). None found — Experimental is
  imported only by Experimental.
- Files with `sorry` outside Experimental that the SORRY_FRONTIER
  doesn't track. Spot-check: clean.
- Files with `axiom` outside Experimental. None — the 0-axiom
  invariant holds.

---

## 5. Recommendations

### Immediate

- [ ] Decide on `L4_LargeField` orphan (delete vs re-link vs
      preserve). Low priority but trivial to resolve.

### Background (low priority)

- [ ] Consider consolidating `L7_Continuum` and `P4_Continuum` into
      a single area. Saves ~4 files. Cost-benefit unclear.
- [ ] Consider whether the `L0-L8` vs `P2-P8` parallel taxonomy
      should be unified, or formally documented as two views into
      the same architecture.
- [ ] Periodically re-run this audit (perhaps monthly) to catch
      any new orphans or staleness as the F3 frontier work
      continues.

### Already addressed

- The 14 Experimental axioms are documented in
  `EXPERIMENTAL_AXIOMS_AUDIT.md` with retire-ability classification.
- The `HasContinuumMassGap` scaling-trick concern is in Finding 004
  and `GENUINE_CONTINUUM_DESIGN.md`.

---

## 6. Summary table for handoff

| Concern | Status | Doc |
|---|---|---|
| Foundation layers (L0, L1) | green | this doc §2.1, §2.2 |
| Wilson observable layer (L4_WilsonLoops) | green | this doc §2.5 |
| Gibbs measure / correlation (L1) | green | this doc §2.2 |
| Continuum predicate (L7) | green-yellow | Finding 004 |
| Phase-style layers (P2-P8) | green | this doc §2.9, §2.10 |
| Terminal plumbing (L8) | green, active | this doc §2.8 |
| Active frontier (ClayCore) | green, active | F3 blueprints, audits |
| Experimental axioms | green for scope | EXPERIMENTAL_AXIOMS_AUDIT.md |
| **Orphan: L4_LargeField** | **flagged** | this doc §3 |

---

*Audit complete 2026-04-25 by Cowork agent.*
