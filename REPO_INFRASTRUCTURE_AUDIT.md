# REPO_INFRASTRUCTURE_AUDIT.md

**Author**: Cowork agent (Claude), infrastructure audit 2026-04-25
**Subject**: comprehensive audit of repository infrastructure NOT
covered by previous Cowork audits — specifically the
`AI_ONBOARDING.md`, the `registry/` YAML metadata, the `scripts/`
automation, the `.github/workflows/` CI configuration, the
`dashboard/` JSON, and the `docs/` runbooks/material.

---

## 0. Bottom line

The project's "supporting infrastructure" — i.e., everything OUTSIDE
the strategic markdown docs (`README.md`, `STATE_OF_THE_PROJECT.md`,
etc.) and outside the active Lean code — is **substantially stale**:

| Area | Last refreshed | Severity |
|---|---|---|
| `AI_ONBOARDING.md` | references v1.45.0 (we're at v1.88.0) | **severe** |
| `dashboard/current_focus.json` | 2026-03-12 (44 days old) | **extreme** |
| `registry/ai_context.yaml` | claims `current_phase: "Phase 0"` | **severe** |
| `registry/nodes.yaml` | "Last updated: 2026-04-01" | moderate |
| `registry/critical_paths.yaml` | L0-L8 organisation, no F3 frontier | moderate |
| `registry/bottlenecks.yaml` | B01 KP theorem = active F3 work | mostly accurate |
| `registry/mathlib_blockers.yaml` | M01 Haar product (resolved?) | needs review |
| `scripts/census_verify.py` | references v0.15.0 expected output | severe |
| `.github/workflows/ci.yml` | uses scripts/, builds 1 file only | structurally current |
| `docs/phase1-llogl-obstruction.md` | 2026-04-17, predates F3 frontier | moderate |
| `docs/03_runbooks/` | March 2026 content | moderate |

**No urgent action needed**: Codex appears to be ignoring this
infrastructure (the F3 frontier work proceeds without consulting
`registry/`, `dashboard/`, or `AI_ONBOARDING.md`). The infrastructure
is dead weight, not actively misleading **except** if a new
contributor or AI agent reads it and trusts it as current state.

**Recommendation**: either **refresh** these files or **archive
them** with explicit "no longer maintained" banners. My
recommendation is **archive**, since the active state is now well-
captured by the strategic docs (`STATE_OF_THE_PROJECT.md`,
`README.md`, `AGENT_HANDOFF.md`, `FINAL_HANDOFF.md`,
`COWORK_FINDINGS.md`) and the registry/dashboard infrastructure
duplicates that information without being maintained.

---

## 1. `AI_ONBOARDING.md` — severely stale

### What it claims

```
**Current version: v1.45.0 (C133)**
**BFS-live custom axioms: 1** (`lsi_normalized_gibbs_from_haar`)
```

### What is actually true

```
Current version: v1.88.0
Custom axioms outside Experimental: 0
The lsi_normalized_gibbs_from_haar axiom was eliminated ~2026-04-23
```

### Other stale content

- "The Primary Proof Path (LSI Pipeline)" describes the LSI /
  HolleyStroock route as the active critical path. This was
  superseded by the F3-Mayer + F3-Count cluster expansion in
  early-mid April. Current critical path is in `BLUEPRINT_F3Count.md`,
  `BLUEPRINT_F3Mayer.md`, `F3_CHAIN_MAP.md`.
- "Next Campaign Target" is still listed as proving
  `lsi_normalized_gibbs_from_haar` from Mathlib. Irrelevant — the
  axiom has been eliminated.
- Build commands and oracle commands reference `sun_physical_mass_gap`,
  which is a former entry point. Current entry points are
  `clayMassGap_of_shiftedF3MayerCountPackageExp` and
  `physicalStrong_of_expCountBound_mayerData_siteDist_measurableF`.

### Recommendation

**Replace with a 1-line file pointing to current docs**:

```markdown
# AI Onboarding

This file is archived. For current onboarding, see
`AGENT_HANDOFF.md` (operational), `FINAL_HANDOFF.md` (60-second
TL;DR), or `KNOWN_ISSUES.md` (caveats). The historical content
of this file is preserved in git history.
```

Estimated edit: 5 minutes.

Alternative: **execute a full refresh** matching the v1.88.0
state. ~30 minutes. Less recommended because the strategic docs
already cover this content.

---

## 2. `registry/` directory — stale and duplicative

### Content overview

```
registry/
  ai_context.yaml          (text-mode AI context)
  bottlenecks.yaml         (7 bottleneck entries B01-B07)
  critical_paths.yaml      (3 paths CP-001, CP-002, CP-003)
  dependencies.yaml        (node-to-node graph)
  labels.yaml              (status/evidence label enums)
  layers.yaml              (L0-L8 layer definitions)
  mathlib_blockers.yaml    (2 blockers M01, M02)
  nodes.yaml               (29 nodes registered, "Last updated: 2026-04-01")
```

### Staleness assessment

- `ai_context.yaml`: claims `current_phase: "Phase 0 — Sanitation
  and architecture"`. **Wrong**: Phase 0 closed in early March;
  current focus is the F3 frontier within ClayCore.
- `nodes.yaml`: 29 nodes covering L0-L8, last updated 2026-04-01.
  **Stale**: doesn't include any ClayCore work (~275 files), no
  L2.5/L2.6 entries (closed 2026-04-21/22), no F3 frontier
  (v1.79+).
- `critical_paths.yaml`: 3 paths defined entirely in terms of
  L0-L8 nodes. The F3 frontier (the ACTUAL critical path) is not
  represented.
- `bottlenecks.yaml`: 7 entries:
  - B01 (Kotecký-Preiss theorem) — **partially active** (F3-Count
    work in progress)
  - B02 (Haar product integration) — likely resolved by current L1
    infrastructure
  - B03-B07 (large field, RG induction, RP, OS-Wightman, mass gap
    without parameter) — most still BLACKBOX, outside F3 scope
- `mathlib_blockers.yaml`: M01 (Haar product) — **resolved** in
  current code; M02 (OS/Wightman) — still relevant as
  out-of-scope.
- `labels.yaml`: enum of status labels. Stable; usable.
- `dependencies.yaml`: L0-L8 graph. Doesn't reflect ClayCore
  internal dependencies.

### What "Phase 0 — Sanitation and architecture" was

Per `ROADMAP_MASTER.md` §"Phase 0", that was the initial setup
phase covering "build registry and dependency DAG, freeze evidence
taxonomy, implement consistency checks." Phase 0 completed by
~2026-03-13 when the foundation layers built. The current "Phase"
is approximately Phase 5 (F3 frontier closure) per the
phase-numbering of `ROADMAP_MASTER.md`.

### Recommendation

The `registry/` directory was built early as a structured
project-metadata system, but **has not been maintained as the
project evolved**. Codex doesn't consult it; Cowork doesn't
consult it; it's invisible to the current critical path.

Three options:

1. **Archive**: rename to `registry_archive/` with a
   `README_ARCHIVE.md` explaining it's no longer maintained.
   Preserves history. ~15 minutes.
2. **Refresh**: update all 8 YAML files to reflect ClayCore + F3
   frontier work. Substantial — ~3-5 hours of careful work, much
   of it duplicating `F3_CHAIN_MAP.md` and `STATE_OF_THE_PROJECT.md`.
3. **Delete**: hard delete after archiving via git. Most
   aggressive; loses the registry-as-meta-DSL idea entirely.

**Cowork recommendation**: **Option 1 (archive)**. The strategic
markdown docs cover the same ground better, and the registry's
"single source of truth for AI context" goal has been replaced by
the Cowork governance system.

---

## 3. `scripts/` — automation, partially stale

### Content overview

```
scripts/
  census_verify.py           (axiom census, references v0.15.0)
  check_consistency.py       (sorry-detection, used by CI)
  validate_registry.py       (registry consistency, used by CI)
  p91_old_route_audit.py     (P91 RG audit, references old route)
```

### Staleness

- `census_verify.py`: docstring references `v0.15.0` expected output
  ("Total unique Lean axiom declaration names: 26"). **Severely
  stale** — current axiom count is 14 (all in Experimental). The
  script may still work mechanically but the expected-output
  comments are wrong.
- `check_consistency.py`: used by CI to detect `sorry`. Per
  `ci.yml`, this script "correctly distinguishes `sorry` in code
  from `sorry` appearing only in comments." Probably current.
- `validate_registry.py`: used by CI to validate registry
  consistency. Will be irrelevant if registry is archived per §2.
- `p91_old_route_audit.py`: name suggests it audits an older RG
  route (P91 = Paper 91 from Bałaban?). Possibly historical.

### Recommendation

Keep `check_consistency.py` (used by CI, current). For the others:

- `census_verify.py`: refresh the docstring to match v1.88.0 axiom
  numbers, OR archive if no longer used.
- `validate_registry.py`: archive if registry is archived per §2.
- `p91_old_route_audit.py`: review and archive if not actively
  consulted.

Estimated effort: 30 minutes for the docstring refresh; ~5 minutes
for archiving the others.

---

## 4. `.github/workflows/ci.yml` — structurally current, scope-limited

### What CI does

Per the YAML:

1. **Job 1 (registry)**: validates registry via
   `validate_registry.py`. Will fail if registry has structural
   issues. (Not failing currently — registry is well-formed even
   if stale on content.)
2. **Job 2 (lean-build)**: builds **only**
   `YangMills.P8_PhysicalGap.BalabanToLSI` (one narrow target).
   Then runs `check_consistency.py` for sorry-detection.

### Scope limitation acknowledged

The `ci.yml` itself documents the limitation:

> A full `lake build` of all ~280 BalabanRG modules is not run in
> CI because build time exceeds GitHub Actions free-tier limits.

This is **honest and accurate**. The narrow CI target ensures the
core LSI route compiles, but does not verify the entire repo on
each push.

### Implications

- **The F3 frontier work is NOT verified by CI.** Codex's per-commit
  build verification (and its `#print axioms` traces in
  AXIOM_FRONTIER.md) is the authoritative check for ClayCore
  changes. If Codex hits a bug, CI won't catch it.
- The README's badge "ClayCore oracles" claim is therefore **based
  on Codex's per-commit verification**, not a comprehensive CI
  build.

### Recommendation

The CI is scope-limited but well-documented. No urgent change
needed. **However**:

- If the F3 frontier closes and the project becomes externally
  visible, the CI scope should expand to verify the F3 endpoint
  builds as well. ~30 minute config change.
- The CI's reliance on `validate_registry.py` will break if the
  registry is archived per §2. Either replace the validation step
  or skip it.

---

## 5. `dashboard/current_focus.json` — extreme staleness

### What it says

```json
{
  "date": "2026-03-12",
  "phase": "Phase 0 — Sanitation and architecture",
  "primary_target": "L0.build_validation",
  ...
}
```

### Reality

- Date: 2026-04-25 (44 days later)
- Phase: F3 frontier closure (Phase 4-ish)
- Primary target: `connecting_cluster_count_exp_bound` witness

### Recommendation

**Either refresh or archive.** Refreshing is ~5 minutes; the JSON
is small. If kept, set up a discipline for regular updates (or
auto-generation from `STATE_OF_THE_PROJECT.md`).

If archived, delete `dashboard/current_focus.json` (the dashboard/
folder is otherwise empty).

**Cowork recommendation**: archive. The dashboard concept is
duplicated by `OBSERVABILITY.md` (spec) and the daily auto-audit
output in `COWORK_AUDIT.md`. A single live JSON adds little value.

---

## 6. `docs/phase1-llogl-obstruction.md` and `docs/03_runbooks/`

### `phase1-llogl-obstruction.md`

12KB, dated 2026-04-17. Documents the L·log·L integrability
obstruction in `BalabanToLSI.lean:805` — a sorry that has since
been **eliminated** as part of the v0.97 cleanup. The document is
**historically valuable** (records the obstruction analysis) but
no longer reflects active state.

### `docs/03_runbooks/`

3 files:
- `Mathlib_PR_HaarMeasure.md`: draft for a Mathlib upstream PR for
  finite product Haar measure (Blocker M01). The fact that this
  draft sits here suggests M01 was **considered upstream-worthy**
  but the PR was never submitted. The current code likely
  works around the gap locally.
- `P91_OLD_ROUTE_AUDIT.json` and `P91_OLD_ROUTE_AUDIT.md`: audit
  of an older P91 (Bałaban Paper 91) route. Probably historical.

### Recommendation

The `docs/` folder content is **historically valuable but not
current**. Add a `docs/README.md` (currently absent) that
explicitly says:

> This folder contains historical analysis documents and runbooks.
> For current strategic state, see `DOCS_INDEX.md` at the
> repository root. Files here may not reflect post-v0.97 state.

Estimated effort: 5 minutes.

---

## 7. Cross-cutting observations

### 7.1 The "old governance system" vs the "new governance system"

The repository has **two parallel governance systems**:

1. **Old (March 2026, mostly abandoned)**: `registry/` YAML files,
   `dashboard/current_focus.json`, `scripts/validate_registry.py`,
   `AI_ONBOARDING.md`, `ROADMAP_MASTER.md`. Uses the L0-L8
   node-based organisation. Built around CI consistency checks.
2. **New (April 2026, active)**: `BLUEPRINT_F3*.md`,
   `CODEX_CONSTRAINT_CONTRACT.md`, `COWORK_FINDINGS.md`,
   `AXIOM_FRONTIER.md`, `AGENT_HANDOFF.md`,
   `STATE_OF_THE_PROJECT.md`. Uses the F3 frontier as the
   organising principle. Built around blueprint→execution→audit
   loop.

The two systems do not interfere with each other (they are
non-overlapping mostly), but the old system is **dead weight**
that an arriving contributor or AI agent would have to filter.

### 7.2 Why the old system was abandoned

Likely reasons (inferred):

- The L0-L8 node organisation didn't scale well to the ClayCore
  layer (which has 275 files vs the original ~30 nodes).
- The CI registry check is rigid — it requires every node to be
  registered, but the project's pace of file creation outran the
  registry maintenance.
- The blueprint → audit pattern proved more valuable than the
  registry → CI pattern for the kind of work being done.

### 7.3 What the new system does NOT replicate

The old system had two valuable properties that the new system
should preserve or substitute:

- **CI integration**: `validate_registry.py` and
  `check_consistency.py` provide automated verification on every
  push. The new strategic docs are not CI-verified. The
  `scripts/check_consistency.py` (sorry detection) is still useful
  and should be preserved.
- **Cross-paper dependency tracking**: the registry tied Lean
  nodes to the 68 companion papers via `nodes.yaml`. The new
  system doesn't track paper-to-Lean correspondence.

### 7.4 Recommended consolidation

A future maintenance pass could:

1. **Archive the registry/, dashboard/, AI_ONBOARDING.md** with a
   "no longer maintained" banner each.
2. **Preserve `scripts/check_consistency.py`** and update CI to
   not depend on `validate_registry.py` (which becomes obsolete
   when registry is archived).
3. **Add a paper-to-Lean correspondence table** to `STATE_OF_THE_PROJECT.md`
   or a new `PAPERS_INDEX.md` to preserve the cross-reference
   value of the old registry.
4. **Update `.github/workflows/ci.yml`** to remove the registry
   job and (if scope permits) expand the lean-build job to verify
   the F3 endpoint.

Estimated total effort: ~2 hours for a careful pass.

---

## 8. Summary table for handoff

| Area | Status | Priority | Effort |
|---|---|---|---|
| `AI_ONBOARDING.md` | severely stale (v1.45 vs v1.88) | medium | 5 min archive / 30 min refresh |
| `registry/ai_context.yaml` | wrong phase | medium | archive or refresh |
| `registry/nodes.yaml` | 3-week stale | low | accept staleness or archive |
| `registry/critical_paths.yaml` | doesn't reflect F3 | low | archive |
| `registry/bottlenecks.yaml` | mostly historical | low | review B01 |
| `registry/mathlib_blockers.yaml` | M01 may be resolved | low | review |
| `scripts/census_verify.py` | docstring stale | low | refresh docstring |
| `scripts/check_consistency.py` | current, used by CI | none | keep |
| `scripts/validate_registry.py` | depends on registry | tied to §2 | archive if registry archived |
| `scripts/p91_old_route_audit.py` | historical | low | archive |
| `.github/workflows/ci.yml` | scope-limited but honest | low | revisit when F3 closes |
| `dashboard/current_focus.json` | 44 days stale | medium | archive |
| `docs/phase1-llogl-obstruction.md` | historical | none | keep as history |
| `docs/03_runbooks/*` | historical | low | add docs/README.md |

**Total effort to fully address**: ~2-3 hours of cleanup work.

**Most valuable single action**: archive `AI_ONBOARDING.md` and
`dashboard/current_focus.json` with redirecting banners (~10
minutes total). These are the highest-visibility stale files.

---

## 9. What this audit changes

This audit produces **observational findings only**. No edits to
the repository have been performed. The findings are documented
here for Lluis's decision; if approved, a future Cowork session
could execute the archival actions.

For tracking purposes, this set of findings can be summarised as
a single compound finding:

> **Compound finding 007 (proposed)**: The repository's "old
> governance infrastructure" (`registry/`, `dashboard/`,
> `AI_ONBOARDING.md`, parts of `scripts/`) is dead weight. None of
> it is consumed by the current Codex daemon or the Cowork
> governance system. Recommend archiving or refreshing as
> documented in §1-§7 of `REPO_INFRASTRUCTURE_AUDIT.md`.

If Lluis approves filing this as Finding 007 in
`COWORK_FINDINGS.md`, I can do that in the next turn.

---

*Infrastructure audit complete 2026-04-25 by Cowork agent.*

---

## Addendum — 5 root-level orphan files (2026-04-25 ~11:25 local)

A follow-up sweep identified **5 small root-level Lean files**
that are historical campaign verification artifacts, all with
**0 importers**:

| File | Size | Content | Origin |
|---|---|---|---|
| `Test.lean` | 344 B | `#check` of decay-related theorems | exploratory, 2026-03-12 |
| `TestC71Full.lean` | 938 B | C71 (Phase 4) prototype verification | campaign C71, 2026-04-21 |
| `TestC72Proto.lean` | 2181 B | C72 (Phase 5) prototype verification | campaign C72, 2026-04-21 |
| `OracleC69.lean` | 383 B | `#print axioms` for C69-H/C69-T1 | campaign C69, 2026-04-21 |
| `OracleC96.lean` | 177 B | `#print axioms` for C96 theorem | campaign C96, 2026-04-21 |

Total: ~4 KB combined, 0 importers, no consumers active in the
current state.

**Classification**: same category as the Finding 007 dead weight —
historical campaign artifacts that have not been cleaned up. They
do not run as part of `lake build YangMills` (none are imported
by the root file). They are pure documentation of what specific
oracle traces or `#check` outputs looked like at the time of
specific campaigns.

**Recommendation**: include in any Finding 007 archival pass. If
Lluis decides Option A (archive), move these to a
`historical_oracle_traces/` folder along with the registry/
content. If Option B (refresh) or C (defer), leave as-is.

This is **not a new finding worth its own number** — just an
extension of the already-filed Finding 007 about repo dead weight.

---

*Addendum prepared 2026-04-25 ~11:25 by Cowork agent.*

