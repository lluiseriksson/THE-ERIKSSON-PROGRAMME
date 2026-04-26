# ROADMAP_AUDIT.md

**Author**: Cowork agent (Claude), audit pass 2026-04-25
**Subject**: staleness audit of strategic roadmap documents
**Files audited**:
- `STATE_OF_THE_PROJECT.md` (243 lines, mtime 2026-04-21)
- `ROADMAP.md` (93 lines, mtime 2026-04-21, internal date 2026-03-13)
- `ROADMAP_MASTER.md` (77 lines, mtime 2026-03-27)
- `UNCONDITIONALITY_ROADMAP.md` (1676 lines, mtime 2026-04-24)

**Method**: read each top-to-bottom, identify factual claims about
project state, compare against current code state at HEAD (2026-04-25,
v1.73.0 per README), flag stale claims and propose remediation.

---

## 0. Bottom line

- `UNCONDITIONALITY_ROADMAP.md`: **mostly fresh**. Top banner v0.98.0
  (2026-04-24) accurately reflects current state. Lines 102+ are
  explicitly archival; one structural cleanup recommendation but no
  factual issues.
- `STATE_OF_THE_PROJECT.md`: **severely stale**. Top entry is v0.34.0
  (L2.5 closure, 2026-04-21). Since then 39 versions and ~330 commits
  have shipped, including the closure of L2.6, the AbelianU1
  unconditional witness for N_c=1, the Peter–Weyl reclassification,
  and the F3 frontier transition. **Recommend full rewrite**, not
  trim.
- `ROADMAP.md`: **moderately stale**. Internal date 2026-03-13 (six
  weeks old). The Phase 5 / Phase 6 framing is still valid in spirit
  but the specific mechanism has shifted from generic
  "ConnectedCorrDecay via KP" to "F3-Mayer + F3-Count packages with
  exponential count frontier". **Recommend update of nodes section,
  preserve high-level phase structure**.
- `ROADMAP_MASTER.md`: **high-level still valid, exit criteria stale**.
  Phase 0-4 labels remain accurate. The "10-15 year horizon" framing
  is unchanged. Phase 1 / Phase 2 exit criteria need revision to
  reflect the F3 frontier reformulation. **Low-priority refresh**.

The single highest-value action is to rewrite `STATE_OF_THE_PROJECT.md`
to reflect the post-v0.97.0 zero-axioms state and the F3 frontier as
the active critical path.

---

## 1. `UNCONDITIONALITY_ROADMAP.md` audit

### 1.1 Current top banner (lines 1-40)

The v0.98.0 banner accurately reports:

- `lake build YangMills` succeeds: ✓ confirmed by repository state.
- Zero non-Experimental Lean axioms: ✓ confirmed via `git grep`
  reproduced in `AXIOM_FRONTIER.md` 0-axiom census.
- `SORRY_FRONTIER.md` records zero `sorry`: ✓ confirmed.
- `ClayYangMillsTheorem` audited as vacuous via
  `clayYangMillsTheorem_trivial`: ✓ confirmed in
  `L8_Terminal/ClayTrivialityAudit.lean`.
- First non-vacuous Clay-grade endpoint is
  `ClayYangMillsPhysicalStrong`: **partially stale**. Since the
  AbelianU1 closure (2026-04-23), the **first non-vacuous Clay-grade
  endpoint with an actual witness** is `ClayYangMillsMassGap 1` (the
  N_c=1 unconditional case), not `ClayYangMillsPhysicalStrong`. The
  document should mention this update.
- Four-step route to 100% unconditional in items (1)-(4):
  - (1) F1/F2/F3 → `ClusterCorrelatorBound`: ✓ valid; **add link**
    to `BLUEPRINT_F3Count.md` and `BLUEPRINT_F3Mayer.md`.
  - (2) ClayCore LSI → SU(N) DLR transfer: ✓ valid as written.
  - (3) SU(N) Dirichlet/Lie sidecar: ✓ valid.
  - (4) Physical endpoint wiring: ✓ valid.

**Recommended edit (small)**: between the top banner and the historical
section, insert a 3-line update noting the AbelianU1 N_c=1 witness and
linking to the F3 blueprints. Otherwise the document is fresh.

### 1.2 Historical content (lines 42+)

The "Historical v1.46 status update (2026-04-11) — Path B, Honest
Labelling" section beginning at line 42 is explicitly labelled as
historical. The reasoning is sound: keeping the historical record lets
future readers reconstruct the trajectory. No edits needed.

The campaign-by-campaign records at line 102+ (down to line 1676) are
the version-by-version commit log. These are useful for archaeology
but not for current orientation. A reasonable cleanup option:

- **Option (a)**: extract lines 102+ to a separate
  `UNCONDITIONALITY_HISTORY.md` and replace with a stub
  "for historical campaign records, see HISTORY.md".
- **Option (b)**: leave as-is; the document is readable in sections.

I recommend (a) for clarity. Saves ~80% of the file size and keeps
the active roadmap visible. Low priority — purely cosmetic.

---

## 2. `STATE_OF_THE_PROJECT.md` audit

### 2.1 What the file currently says

The file is a stack of dated entries from oldest (v0.32.0, 2026-04-14)
at the bottom to most recent (v0.34.0, L2.5, 2026-04-21) at the top.
Total 243 lines.

The v0.34.0 top entry accurately describes the L2.5 closure on the
day it landed (`sunHaarProb_trace_normSq_integral_le`). Below that,
v0.33.0 (axiom elimination, holleyStroock orphaning) and v0.32.0
(structural collapse of the Clay axiom) are accurate as historical
records but **describe a state that has been substantially superseded**.

The v1.46 entry (lines 99-202) describes the project as having one
project axiom (`lsi_normalized_gibbs_from_haar`) and ~30% honest
progress. Per the v0.98.0 banner of `UNCONDITIONALITY_ROADMAP.md`,
**that axiom is no longer present**. `lake build YangMills` succeeds
with zero non-Experimental axioms.

The status update at the bottom (2026-04-14) describes ~34% progress
with 3 sorries in `BalabanToLSI.lean`. Per current state, **zero
sorries exist outside `YangMills/Experimental/`**, and the entire
LSI/HolleyStroock route has been **deprioritised** in favour of the F3
frontier.

### 2.2 What is stale

Lines | Stale claim | Current reality
---|---|---
1-37 | "Next: L2.6" | L2.6 fully closed 2026-04-22 (commits f9ec5e9, 95175f3, 70403d1)
99-103 | v1.46.0, axiom count 1, ~30% progress | v1.73.0, axiom count 0, ~50% (per README bars)
127-148 | "lsi_normalized_gibbs_from_haar" axiom | removed
149-162 | "Primary Proof Chain" via LSI / HolleyStroock | superseded by F3-Mayer + F3-Count
176-202 | "What is not yet proved" — 3 LSI sub-pieces | not on critical path; F3 is
206-243 | Status update 2026-04-14 — 3 sorries in BalabanToLSI | zero live sorries

**Approximately 80% of the file describes a state that no longer
applies.** The remaining 20% (the architectural framing) is fine.

### 2.3 Recommendation

Full rewrite. Replace the file with:

- One paragraph describing current state (v1.73.0, zero axioms, L2.6
  closed, AbelianU1 N_c=1 closed, F3 frontier active).
- One paragraph describing the active critical path (F3-Mayer +
  F3-Count blueprints, link).
- One paragraph describing the residual obstacles (lattice-animal
  count proof at d=4, BK estimate, mass gap for N_c ≥ 2).
- A section "What this is NOT" pointing to `ClayTrivialityAudit.lean`
  for the vacuity caveats.
- A "Last refreshed" timestamp.
- A note that older v0.32 / v0.33 / v0.34 / v1.46 entries are
  preserved in `STATE_OF_THE_PROJECT_HISTORY.md` (move them).

Estimated rewrite effort: 1 hour for human author, or one Codex
session if delegated. I can produce a draft in this turn if approved.

---

## 3. `ROADMAP.md` audit

### 3.1 What the file currently says

Internal date 2026-03-13. Describes:

- Explicit hypotheses already discharged: `LatticeMassProfile.IsPositive`
  (Phase 3), `∃ m_inf, 0 < m_inf` (Phase 2), `HasContinuumMassGap`
  (Phase 4 interface).
- Active explicit hypotheses: `ConnectedCorrDecay` (Phase 5),
  `HasAsymptoticFreedomControl` (Phase 6).
- Phase 5 nodes F5.1 / F5.2 / F5.3 (KP hypotheses, Balaban bootstrap,
  decay from RG).
- Phase 6 nodes F6.1 / F6.2 / F6.3 (beta function, coupling
  convergence, asymptotic freedom discharge).
- Build status table with commits 529ec9f, 7ed016a, cb64793, 6261867.
- External mathematics declared as black boxes.

### 3.2 Staleness assessment

| Section | Status | Notes |
|---|---|---|
| Architecture / discharged hypotheses (lines 6-9) | accurate | three Phase-2-to-4 discharges still hold |
| Active hypotheses (lines 11-13) | partially stale | both still active, but mechanism has shifted |
| Phase 5 nodes F5.1-F5.3 (lines 21-37) | superseded | the discharge route is now via F3-Mayer + F3-Count, not via the KP / Balaban-bootstrap chain originally written. The high-level statement (Phase 5 = discharge ConnectedCorrDecay) is correct. |
| Phase 6 nodes F6.1-F6.3 (lines 41-58) | accurate | the asymptotic-freedom discharge route is unchanged |
| Phase 7 assembly (lines 62-72) | accurate | the assembly logic is unchanged |
| Build status table (lines 76-83) | stale | commits referenced are 4+ weeks old |
| Explicit hypotheses remaining (lines 86-87) | accurate | both still open |
| External mathematics (lines 89-93) | accurate | KP, OS, lattice RP, Balaban CMP all still apply |

### 3.3 Recommendation

Targeted edit, not rewrite. Specifically:

1. Update internal date to 2026-04-25.
2. Replace Phase 5 nodes section with reference to F3 blueprints
   (or reword to make F5.1 = F3-Count witness, F5.2 = F3-Mayer
   witness, F5.3 = packaged ClusterCorrelatorBound).
3. Refresh build status table commits (or replace with
   "see `git log` and `README.md`").
4. Add line acknowledging AbelianU1 N_c=1 closure as the first
   non-vacuous concrete witness, distinct from the still-open N_c≥2
   target.

Estimated edit effort: 20 minutes for human author. I can produce a
diff in this turn if approved.

---

## 4. `ROADMAP_MASTER.md` audit

### 4.1 What the file currently says

77 lines, dated 2026-03-27. Phase 0-4 labels with goals and exit
criteria for each.

### 4.2 Staleness assessment

| Phase | Status |
|---|---|
| Phase 0 — Sanitation and architecture | accurate; "active" is still true at the meta-level |
| Phase 1 — Reusable infrastructure | accurate goals; exit criteria need refresh — "abstract Kotecký-Preiss" is now the F3 framework, "polymer combinatorics" is the lattice-animal frontier |
| Phase 2 — Balaban/Eriksson core closure | accurate goals |
| Phase 3 — OS/Wightman | accurate, not on active path |
| Phase 4 — Inconditional closure | accurate, but the "remove remaining imports" framing is post hoc — the more accurate framing is "produce non-vacuous Clay-grade witnesses" |
| Always-on goals | accurate |

The document is high-level enough that staleness is mild. The exit
criteria are the part that drifts.

### 4.3 Recommendation

Low priority. Two small edits:

1. Phase 1 exit criteria: add "F3 packages produce non-vacuous
   `ClusterCorrelatorBound` for SU(N_c) Wilson at small β."
2. Phase 4 framing: "remove remaining imports" → "produce non-vacuous
   Clay-grade witnesses with zero declared axioms outside
   `YangMills/Experimental/`."

Estimated edit effort: 10 minutes. Defer until after a major release.

---

## 5. Proposed action items

### 5.1 Immediate (next 1-2 sessions)

For Lluis (human review):

- [ ] Approve the `STATE_OF_THE_PROJECT.md` full rewrite. This is
      the single most misleading document for new readers (and for
      anyone using the file to assess project state).
- [ ] Approve the `ROADMAP.md` targeted edit (Phase 5 nodes update,
      build status refresh).

For Codex (autonomous):

- [ ] If approved, execute both edits. The rewrite of
      `STATE_OF_THE_PROJECT.md` should preserve old entries in
      `STATE_OF_THE_PROJECT_HISTORY.md`.

For Cowork agent (next turn):

- [ ] Produce draft text for `STATE_OF_THE_PROJECT.md` rewrite if
      requested.

### 5.2 Background (deferrable)

- [ ] `ROADMAP_MASTER.md` exit-criteria refresh.
- [ ] `UNCONDITIONALITY_ROADMAP.md` historical-content extraction to
      `UNCONDITIONALITY_HISTORY.md`.
- [ ] Add a top-level pointer document `DOCS_INDEX.md` listing all
      strategic documents and their last-refresh dates, so readers can
      orient quickly. Estimated 30 lines.

---

## 6. Cross-document consistency check

Cross-referenced facts as they appear in each document:

| Fact | UNCONDITIONALITY (v0.98) | STATE_OF_THE_PROJECT | ROADMAP | ROADMAP_MASTER |
|---|---|---|---|---|
| Current axiom count outside Experimental | 0 | 1 ("lsi_normalized_gibbs_from_haar") | not stated | not stated |
| Current sorry count | 0 | 3 | not stated | not stated |
| Active critical path | F3 + ClayCore LSI + Lie sidecar + endpoint wiring | LSI/HolleyStroock | ConnectedCorrDecay via KP + RG | "abstract Kotecký-Preiss + cluster expansion" |
| First non-vacuous Clay endpoint with witness | `ClayYangMillsPhysicalStrong` (claimed; partially stale) | none mentioned | none mentioned | none mentioned |
| AbelianU1 N_c=1 unconditional | not mentioned | not mentioned | not mentioned | not mentioned |
| Peter–Weyl status | not mentioned | not mentioned | not mentioned | "OS framework" not specifically tied to PW |
| Mass-gap target shape | F3 → ClusterCorrelatorBound | LSI → spectral gap | ConnectedCorrDecay decay | "abstract OS framework" |

**Inconsistency severity**: high between UNCONDITIONALITY and the
other three. UNCONDITIONALITY (v0.98) is fresh; the others are 4-6
weeks behind on substantive matters.

The fix is the rewrite/edit cycle in §5.

---

*End of audit. Last updated 2026-04-25.*
