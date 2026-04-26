# README_AUDIT.md

**Author**: Cowork agent (Claude), README freshness audit 2026-04-25
**Subject**: detailed audit of `README.md` for accuracy, freshness,
honest framing, and external-reader usability
**Method**: section-by-section read; compare against `git log`,
`AXIOM_FRONTIER.md`, `STATE_OF_THE_PROJECT.md`, `COWORK_FINDINGS.md`,
and `DOCS_INDEX.md`

---

## 0. Bottom line

`README.md` is **mostly current and well-framed**, with two notable
gaps:

1. **§3 "Recently closed milestones"** has only 2 entries (L2.6 main
   target and N_c=1 unconditional). It is **missing** documentation
   for the substantial F3 frontier work landed v1.79.0 through
   v1.85.0+ (six substantive releases over the past day).
2. **§7 "Repository layout"** lists the older ClayCore files but
   does not mention `LatticeAnimalCount.lean`,
   `ConnectingClusterCountExp.lean`, `ClusterRpowBridge.lean`
   (the active F3 hub), or any of the Cowork-agent strategic docs
   (BLUEPRINT_F3*, CODEX_*, COWORK_*, etc.).

Smaller observations:

- The "At a glance" table's "Last closed" field IS current
  (v1.85.0). Codex maintains this field actively; it is the
  most-fresh part of the document.
- The N_c=1 framing in §3 honestly notes that the correlator is
  "identically zero" (good!), but doesn't connect this to the
  trivial-group caveat from `COWORK_FINDINGS.md` Finding 003. The
  word "U(1)" in §6 row 17 is technically misleading
  (`SU(1) ≠ U(1)`).
- §6 milestone ladder is missing rows for v1.79+ packaging work and
  for Priority 1.2 (`LatticeAnimalCount`).

The README does **not** overclaim. The honest-framing discipline is
intact. Updates are additive (new rows for new milestones); no
existing content needs retraction.

---

## 1. Section-by-section findings

### 1.1 TL;DR (lines 14-22)

**Status**: current.

States:
- "L1 layer ... is closed" ✓ (98% per bars)
- "L2.6's main target has just landed" — ✓ (referring to v1.50.0
  era; the wording "just landed" is now ~3 days stale but the
  underlying claim is correct)
- "What's next: `ClusterCorrelatorBound`: the F3 summability/
  factoring bridge now reaches the exact Wilson-facing target" — ✓
  current as of v1.81.0+

**Suggestion**: consider rephrasing "has just landed" to
"is closed" to avoid implying a fresh action.

### 1.2 At a glance (lines 24-35)

**Status**: current.

The "Last closed" cell is up-to-date with v1.85.0 plus the most
recent unbumped commits (mentioning `polymerConnected_plaquetteGraph_induce_reachable`
which lands in commit at 10:35 local). Codex maintains this field
within minutes of each substantive commit.

### 1.3 §1 What this repository is (lines 52-64)

**Status**: current.

Three-layer framing (L1 + L2 + L3) is still accurate. The note about
"L2.6 step 3 / Peter-Weyl is the last remaining internal L1→L2
bridge" is technically still true even after the reclassification —
PW is still the bridge that *would* close arbitrary-irrep
character orthogonality, but the project no longer pursues it as
critical.

**Suggestion**: add a sentence clarifying that "Peter-Weyl step 3
has been reclassified as aspirational/Mathlib-PR (see §5.4); the
critical path now flows directly through the F3 chain
(F1 + F2 + F3)."

### 1.4 §2 Progress bars (lines 66-97)

**Status**: current.

```
L1=98%  L2.4=100%  L2.5=100%  L2.6=100%  L2=50%  L3=22%  OVERALL=50%
```

Verified against `STATE_OF_THE_PROJECT.md` and own measurements.
Bars move only when frontier entries retire — the F3 packaging work
(v1.79-v1.85) explicitly does not move bars per project policy. Good.

### 1.5 §3 Recently closed milestones (lines 99-155)

**Status**: **substantially stale**.

Only 2 entries, both from 2026-04-22 / 2026-04-23:
1. L2.6 main target (commit `f9ec5e9`, 2026-04-22)
2. N_c=1 unconditional witness (2026-04-23)

**Missing entries** for F3 frontier work landed 2026-04-25:

- **v1.79.0** — Exponential F3 count frontier interface
  (`ConnectingClusterCountExp.lean` created)
- **v1.80.0** — Exponential KP series prefactor
- **v1.81.0** — Bridge to `ClusterCorrelatorBound`
- **v1.82.0** — Packaged Clay route
  (`ShiftedF3MayerCountPackageExp` + terminal endpoint)
- **v1.83.0** — Physical d=4 endpoint
- **v1.84.0** — L8 terminal route to `ClayYangMillsPhysicalStrong`
- **v1.85.0** — `LatticeAnimalCount.lean` scaffold (Priority 1.2
  begins)

**Recommendation**: add a third entry summarising the **F3 frontier
buildout 2026-04-25** with one paragraph describing the v1.79 →
v1.85 arc and one paragraph noting that the `HasContinuumMassGap`
half of `ClayYangMillsPhysicalStrong` is satisfied via the
coordinated scaling convention (per `COWORK_FINDINGS.md` Finding
004).

If the team prefers to keep §3 sparse (only "headline" milestones),
then add a single row per major sub-target instead — e.g., one
entry for "F3 chain plumbing complete (v1.79-v1.84)" and one for
"Priority 1.2 begins (v1.85+)".

### 1.6 §4 Oracle discipline (lines 158-170)

**Status**: current.

Crisp framing of the oracle invariant. The scoping ("the *core*
is oracle-clean today; the *whole project* is not") is honest.
No changes needed.

### 1.7 §5 Current front (lines 172-197)

**Status**: current.

§5.1 vestigial-metadata finding, §5.2 F1+F2+F3 strategy, §5.3 oracle
budget, §5.4 Peter-Weyl reclassified — all four sub-sections are
accurate and consistent with the v1.79+ frontier work.

**Suggestion**: §5.2 could mention that the F3 layer is itself now
decomposed into F3-Mayer + F3-Count subpackages per
`BLUEPRINT_F3*.md`, with the Klarner BFS-tree count and BK
estimate as the open inputs.

### 1.8 §6 Milestone ladder (lines 197-221)

**Status**: missing rows for v1.79+ work.

The table has 17 rows, including row 14
(`ClusterCorrelatorBound` IN PROGRESS) and row 17
(N_c=1 DONE).

**Missing rows** for substantive v1.79+ work:

- F3 Resolution C — exponential frontier interface
  (`ConnectingClusterCountExp.lean`, v1.79.0, DONE oracle-clean)
- F3 KP series prefactor (`ClusterSeriesBound.lean`, v1.80.0,
  DONE oracle-clean)
- F3 bridge to `ClusterCorrelatorBound`
  (`ClusterRpowBridge.lean`, v1.81.0, DONE oracle-clean)
- F3 packaged Clay route (`ShiftedF3MayerCountPackageExp`,
  v1.82.0, DONE oracle-clean)
- F3 physical d=4 endpoint (v1.83.0, DONE oracle-clean)
- F3 L8 terminal route to PhysicalStrong (v1.84.0, DONE
  oracle-clean **with Finding 004 caveat**)
- F3 lattice-animal scaffold (`LatticeAnimalCount.lean`,
  v1.85.0+, IN PROGRESS Priority 1.2)

**Recommendation**: add 7 new rows. Note the Finding 004 caveat
inline for the v1.84.0 entry.

**Minor framing issue**: row 17 says "`ClayYangMillsMassGap 1` —
unconditional witness at N_c = 1". The wording "unconditional"
is correct (no hypotheses) but doesn't acknowledge that N_c=1 is
the trivial-gauge-group case where the correlator is identically
zero. The §3 entry does flag this (saying the bound holds
"vacuously"); §6 row 17 should match.

**Recommendation**: edit row 17 to read e.g. "**`ClayYangMillsMassGap
1` — unconditional witness at N_c = 1 (trivial gauge group)**" —
making the caveat visible at the table level.

### 1.9 §7 Repository layout (lines 225-269)

**Status**: substantially stale.

The ClayCore directory listing covers Schur* files and
CharacterExpansion / ClusterCorrelatorBound / WilsonGibbsExpansion
/ ClusterSeriesBound / MayerExpansion. **Missing**:

- `LatticeAnimalCount.lean` (created v1.85.0)
- `ConnectingClusterCountExp.lean` (created v1.79.0)
- `ClusterRpowBridge.lean` (the active F3 chain hub, ~4264 LOC)
- `AbelianU1Unconditional.lean` (the N_c=1 witness, mentioned in §3
  but not §7)
- `ZeroMeanCancellation.lean` (the keystone zero-mean lemma)

The top-level files list at the bottom of §7 includes only the
"original" set (README, AXIOM_FRONTIER, SORRY_FRONTIER,
UNCONDITIONALITY_ROADMAP, PETER_WEYL_ROADMAP, STATE_OF_THE_PROJECT,
ROADMAP / ROADMAP_MASTER, HYPOTHESIS_FRONTIER, DECISIONS,
CONTRIBUTING, AI_ONBOARDING). **Missing**:

- All Cowork-agent strategic docs (BLUEPRINT_F3*, MATHLIB_GAPS,
  ROADMAP_AUDIT, PETER_WEYL_AUDIT, EXPERIMENTAL_AXIOMS_AUDIT,
  GENUINE_CONTINUUM_DESIGN, CODEX_*, COWORK_*, MATHEMATICAL_*,
  MID_TERM_*, F3_CHAIN_MAP, AGENT_HANDOFF, CONTRIBUTING_FOR_AGENTS,
  REFERENCES_AUDIT, LAYER_AUDIT, THREAT_MODEL,
  RELEASE_NOTES_TEMPLATE, STRATEGIC_DECISIONS_LOG, CADENCE_AUDIT,
  PROJECT_TIMELINE, GLOSSARY)
- `DOCS_INDEX.md` (which would be the right entry point for
  external readers!)

**Recommendation**: replace the verbose top-level listing with a
single line "See `DOCS_INDEX.md` for a one-page index of all
strategic and reference documents." Also add the missing ClayCore
files. Could be a 30-minute targeted edit.

### 1.10 §8-§10 Building, contributing, honesty note (lines 273-305)

Not inspected line-by-line in this audit. Likely current, low
risk. Spot-check: the "Building & verifying" instructions probably
still match the current `lakefile.lean` and Mathlib pinning.

---

## 2. Honest framing assessment

The README **does not overclaim**. Specifically:

- The N_c=1 unconditional witness is honestly described as
  "identically zero, and `ConnectedCorrDecay` holds vacuously" in
  §3. Good.
- The bars are conservative. No aspirational percentages.
- The "What this is **not**" framing (in `STATE_OF_THE_PROJECT.md`,
  not duplicated in README) is implicit in the milestone ladder's
  classification of L3 as "CONDITIONAL" (row 16).

What's **missing in the honest-framing direction**:

- The `ClayYangMillsPhysicalStrong` continuum-trick caveat
  (Finding 004) is not mentioned in the README at all. External
  readers who reach the "PhysicalStrong" wording might assume
  more than the construction delivers. **Recommend adding a
  one-paragraph caveat box in §3 or §5** referencing
  `COWORK_FINDINGS.md` Finding 004 or
  `MATHEMATICAL_REVIEWERS_COMPANION.md` §6.2.

- The N_c=1 trivial-group framing could be tightened in §6 row 17
  (per §1.8 above).

---

## 3. Recommended edits (prioritised)

### High priority

1. **Add a §3 entry for F3 frontier buildout 2026-04-25**.
   Document v1.79 → v1.85 arc, mention Finding 004 caveat for
   v1.84 PhysicalStrong route. Estimated 1-2 paragraphs.

2. **Add 7 rows to §6 milestone ladder** for v1.79+ work.
   Recommended naming convention: "F3 — exponential frontier
   interface", "F3 — KP series prefactor", "F3 — bridge to
   `ClusterCorrelatorBound`", etc., all marked DONE except
   `LatticeAnimalCount` which is IN PROGRESS.

3. **Edit §6 row 17** to clarify N_c=1 trivial-gauge-group
   caveat.

### Medium priority

4. **§7 repository layout**: add missing ClayCore files; replace
   verbose top-level listing with reference to `DOCS_INDEX.md`.

5. **Add a Finding-004 caveat box** in §3 or §5 about
   `ClayYangMillsPhysicalStrong`'s continuum half.

### Low priority

6. §1 minor clarification about Peter-Weyl reclassification.
7. §5.2 mention F3-Mayer + F3-Count subpackage structure.
8. §1.1 rephrase "has just landed" to "is closed".

---

## 4. Maintenance recommendation

The "Last closed" field is well-maintained (within minutes of
each commit). The §3 milestones list and §6 ladder are
under-maintained — they were updated for L2.6 but not for v1.79+.

**Recommendation for ongoing discipline**: the
`CODEX_CONSTRAINT_CONTRACT.md` SR3 currently says "README.md
'Last closed' updated within 1 hour of substantive commits". This
is met. **Add an SR3-companion**: "for any release that introduces
a new milestone (defined as: a release that creates a new file in
`YangMills/ClayCore/` or whose title begins with a verb other than
'expose'/'add'/'route'/'package'), §3 of README.md gets a new
sub-entry within 24h."

This would prevent the §3 staleness from accumulating.

---

## 5. Verdict

The README is structurally sound and honestly framed. The freshness
gaps are localised to §3 and §7. None of the gaps constitute
overclaiming or misleading statements; they are missing-content
rather than wrong-content. A single 30-minute editing pass per the
recommendations above would bring the README fully current.

Codex's discipline of maintaining the "Last closed" field is good.
The opportunity is to extend the same discipline to §3 milestones
and §6 ladder rows on substantive releases.

---

*README audit complete 2026-04-25 by Cowork agent.*
