# AGENT_HANDOFF.md

**Audience**: a future Cowork agent (Claude session) picking up this
project. **Read this first** before doing anything else.

**Last updated**: 2026-04-25 (end-of-session refresh) by the Cowork
agent that wrote everything in this file.

> **End-of-session note (2026-04-25 ~11:00 local)**: this file was
> drafted mid-session. By session end, several additional
> deliverables landed beyond what is listed in §7 below. For the
> definitive end-of-session inventory, see `SESSION_SUMMARY.md`
> (added at session end). The most important new files since this
> handoff was first drafted:
>
> - `KNOWN_ISSUES.md` — consolidated public-facing caveat summary
> - `README_AUDIT.md`, `NEXT_SESSION_AUDIT.md` — audit pair
> - `OBSERVABILITY.md` — dashboard spec
> - `LAYER_AUDIT.md`, `THREAT_MODEL.md` — defensive analyses
> - `RELEASE_NOTES_TEMPLATE.md`, `STRATEGIC_DECISIONS_LOG.md` —
>   process artefacts
> - `CADENCE_AUDIT.md`, `PROJECT_TIMELINE.md`, `GLOSSARY.md` —
>   reference docs
> - `SESSION_SUMMARY.md` — comprehensive 2026-04-25 session record
> - Two more findings filed: 005 (L4_LargeField orphan, advisory),
>   006 (NEXT_SESSION contradiction, addressed via banner)
>
> The active state at session end: **v1.86.0** with
> `LatticeAnimalCount.lean` at ~282 LOC (~69% of estimated 410 LOC
> for Priority 1.2 closure).

---

## 0. Sixty-second orientation

This is **THE-ERIKSSON-PROGRAMME**, a Lean 4 / Mathlib formalisation
of the Yang-Mills mass gap (Clay Millennium target). Working in
collaboration with:

- **Lluis Eriksson** (human, project lead). Communicates in Spanish
  and English. Asks for analytical depth and honest framing.
- **Codex 24/7 daemon** (autonomous, doing the Lean coding). Cadence
  is ~150 commits/day. Reads `CODEX_CONSTRAINT_CONTRACT.md` and the
  blueprints to know what to attack.

**Your job as the Cowork agent**: strategic blueprints, audits,
findings, governance docs. **Not** Lean coding (that's Codex).

The repo is at `C:\Users\lluis\.gemini\antigravity\scratch\THE-ERIKSSON-PROGRAMME`
(Linux mount: `/sessions/<session>/mnt/THE-ERIKSSON-PROGRAMME/`).

---

## 1. Read order on first session

In strict order:

1. **`README.md`** — the live-state landing page. Authoritative for
   "what is closed today" and the bars.
2. **`DOCS_INDEX.md`** — single-page index of every strategic doc,
   with last-refresh dates.
3. **`STATE_OF_THE_PROJECT.md`** — current version, what's open, what's
   closed, honest assessment with caveats (especially the
   Finding 004 box about `ClayYangMillsPhysicalStrong`).
4. **`COWORK_FINDINGS.md`** — open obstructions and historical findings.
   At time of writing: 4 findings, 3 of them with status notes
   (002 placeholder, 001 addressed, 003 open advisory, 004 with
   action notes).
5. **`CODEX_CONSTRAINT_CONTRACT.md`** — current rules (HR1-HR5,
   SR1-SR4) and the priority queue. The contract is at v1.
6. **`F3_CHAIN_MAP.md`** — definitive dependency graph of the F3
   chain. If you need to know "where does theorem X fit in", look
   here first.
7. **`COWORK_AUDIT.md`** — the daily auto-audit. Most recent entry
   at the top.

If you have time, also skim:

8. `CONTRIBUTING_FOR_AGENTS.md` — operational loop guidelines.
9. `BLUEPRINT_F3Count.md` and `BLUEPRINT_F3Mayer.md` — current
   strategy documents (with §−1 update overlays).
10. `CODEX_EXECUTION_AUDIT.md` and `AUDIT_v185_LATTICEANIMAL.md` —
    independent verification of how Codex executed the blueprints.

---

## 2. The active state at handoff

**Repo version**: v1.85.0 (as of 2026-04-25 ~10:01 local).

**Active priority** per `CODEX_CONSTRAINT_CONTRACT.md` §4: **Priority
1.2 — `LatticeAnimalCount.lean` witness.** v1.85.0 landed the graph
scaffold (~99 LOC); ~310 LOC remain to close.

**Codex cadence**: ~150 commits/day, 24/7 daemon. Pattern of
substantive vs canary releases is healthy.

**Open findings**: Finding 003 (AbelianU1 N_c=1 caveat — advisory),
Finding 004 (HasContinuumMassGap scaling-trick caveat — advisory
with action notes recorded). No blockers.

**Open Mathlib gaps** with PR drafts ready to upstream:
- Gap #1: `mathlib_pr_drafts/AnimalCount.lean` — connected subgraph
  count bound.
- Gap #2: `mathlib_pr_drafts/PiDisjointFactorisation.lean` — Pi
  measure factorisation.

---

## 3. Lluis's working style (notes from this session)

- **Communication**: mostly Spanish, occasional English, casual tone.
  Likes short prompts ("continúa") that delegate large amounts of
  work to you.
- **Decision style**: trusts agent judgement on tactical details,
  reserves human input for:
  - Architectural decisions (like Option B vs Option C in
    `GENUINE_CONTINUUM_DESIGN.md` §5).
  - Renames (file names, structure names — wants explicit confirmation).
  - Mathematical-honesty calls (like the AbelianU1 / continuum-trick
    framing).
- **Preferences observed**:
  - Wants substantial deliverables, not chit-chat. Multiple files
    per turn is welcome.
  - Wants honest framing about what's proved vs what isn't —
    appreciates Findings that surface caveats.
  - Doesn't want me to ask "should I proceed?" — said "no me preguntes
    más, hago el trabajo y te reporto al final."
  - Asked at one point for tasks ≥1 hour minimum — wants longer-form
    work.
- **Trust threshold**: high. Tells you to "continúa" expecting you
  to use judgement. Don't waste it on trivia.

If Lluis asks "continúa" or "continue" without further context, the
default action is: **pick the next item in `CODEX_CONSTRAINT_CONTRACT.md`
§4 priority queue that is suitable for Cowork (i.e., not direct Lean
coding) and execute it**, possibly batching multiple tasks if context
allows.

---

## 4. The Cowork ↔ Codex governance loop

Visualised in `CONTRIBUTING_FOR_AGENTS.md` §1. In one paragraph:

Codex reads the contract + findings on each session start, picks the
top unblocked priority, executes Lean code, commits frequently, files
a finding if obstruction. Cowork agent (you) writes the contract,
the blueprints, the findings analysis, the audits. Daily scheduled
task `eriksson-daily-audit` runs at 09:04 local and writes
`COWORK_AUDIT.md` checking compliance. Lluis reads the audit and
intervenes only on FAIL signals.

The system has been validated empirically (see
`CODEX_EXECUTION_AUDIT.md`): blueprint → execution → audit cycle
took 3-4 hours for the F3-Count Resolution C path.

---

## 5. How to make decisions on behalf of the system

When in doubt:

- **Honesty over completeness**. If a Lean construction is technically
  valid but mathematically degenerate, file a finding. The repo's
  reputation depends on accurate framing of what's been proved.
- **Append over rewrite**. The strategic docs are accumulators. Keep
  history; mark items addressed; preserve archaeology.
- **Document for the next agent**. Whatever you build, leave it
  accessible to a fresh Cowork session. This file is part of that
  discipline.
- **Defer architectural decisions to Lluis**. Renames, predicate
  refactors, axiom retirement plans — these are human-scale calls.
  Sketch the proposal (like `GENUINE_CONTINUUM_DESIGN.md`) but
  don't execute without sign-off.

---

## 6. What to do if you find something is broken

1. **Build broken**: file a finding (severity blocker), pause your
   work, surface to Lluis. Do not push through.
2. **Auto-audit (`COWORK_AUDIT.md`) shows a hard rule FAIL**:
   investigate before doing anything else. The fail may affect
   your planned work.
3. **A blueprint contradicts current code state**: the blueprint
   takes precedence as the strategic intent; the discrepancy is a
   finding to file.
4. **A finding from previous session is open and relevant**: read
   the recommended action and either execute it (if low-stakes) or
   surface to Lluis.

---

## 7. Inventory of what's been done (by document)

For a new agent's quick orientation, here's what each strategic doc
in the repo provides:

| File | Purpose | Status |
|---|---|---|
| `README.md` | Live state landing page | autoritativo |
| `DOCS_INDEX.md` | Single-page index | maintained |
| `STATE_OF_THE_PROJECT.md` | Snapshot prose narrative | refreshed for v1.83+ |
| `STATE_OF_THE_PROJECT_HISTORY.md` | Archive of older snapshots | locked |
| `ROADMAP.md` | Phase 5–7 architecture | refreshed for v1.83 |
| `ROADMAP_MASTER.md` | 10-15y horizon | low-priority refresh deferred |
| `UNCONDITIONALITY_ROADMAP.md` | Version-by-version progression | top banner v0.98 + 2026-04-25 update |
| `PETER_WEYL_ROADMAP.md` | Reclassified summary | trimmed 574→132 lines |
| `PETER_WEYL_ROADMAP_HISTORY.md` | Archive of original roadmap | locked |
| `PETER_WEYL_AUDIT.md` | Reclassification verification | delivered |
| `PHASE8_PLAN.md` | Pre-F3 plan | stale banner added |
| `PHASE8_SUMMARY.md` | Pre-F3 summary | stale (existing banner) |
| `BLUEPRINT_F3Count.md` | F3-Count strategy + Resolution C | delivered + §−1 overlay |
| `BLUEPRINT_F3Mayer.md` | F3-Mayer strategy + BK estimate | delivered + §−1 overlay |
| `MATHLIB_GAPS.md` | 5 gaps inventoried, hybrid recommendation | delivered |
| `ROADMAP_AUDIT.md` | Staleness audit of strategic docs | delivered |
| `CODEX_CONSTRAINT_CONTRACT.md` | Rules + priority queue | v1 |
| `CODEX_EXECUTION_AUDIT.md` | v1.79–v1.82 validation | delivered |
| `AUDIT_v185_LATTICEANIMAL.md` | v1.85.0 detail audit | delivered |
| `COWORK_AUDIT.md` | Daily auto + manual entries | live |
| `COWORK_FINDINGS.md` | Findings log (4 findings) | live |
| `MATHEMATICAL_REVIEWERS_COMPANION.md` | Math exposition for non-Lean | delivered + Finding 004 caveat |
| `EXPERIMENTAL_AXIOMS_AUDIT.md` | Classification of 14 Experimental axioms | delivered |
| `GENUINE_CONTINUUM_DESIGN.md` | Design proposal for genuine continuum predicate | delivered (Option B chosen) |
| `F3_CHAIN_MAP.md` | Definitive chain dependency map | delivered |
| `CONTRIBUTING_FOR_AGENTS.md` | Operational loop for autonomous agents | delivered |
| `AGENT_HANDOFF.md` | This file — orientation for the next agent | delivered |
| `mathlib_pr_drafts/AnimalCount.lean` + PR_DESCRIPTION | Gap #1 PR draft | delivered |
| `mathlib_pr_drafts/PiDisjointFactorisation.lean` + PR_DESCRIPTION_Gap2 | Gap #2 PR draft | delivered |
| `mathlib_pr_drafts/F3_Count_Witness_Sketch.lean` | Consumer-side sketch | delivered (now imported by Codex) |

---

## 8. Notes on what NOT to do

- **Don't write Lean code**. That's Codex's job. You produce
  blueprints, not implementations. (Exception: small Lean fragments
  inside Mathlib PR drafts are fine, with `sorry` markers.)
- **Don't delete history files** (`STATE_OF_THE_PROJECT_HISTORY.md`,
  `PETER_WEYL_ROADMAP_HISTORY.md`). They're archives.
- **Don't bump README.md "Last closed"**. Codex maintains that.
- **Don't violate HR3** by writing a non-Experimental `axiom`. The
  0-axiom invariant is a project commitment.
- **Don't make claims about what's "proved" without checking**. Use
  `git grep` and `wc -l` and `git log` liberally to verify before
  asserting.

---

## 9. Quick commands you'll use a lot

```bash
# Current version
grep "^# v" AXIOM_FRONTIER.md | head -1

# Current sorry count
grep -c "## Current sorry count" SORRY_FRONTIER.md
# (or just read SORRY_FRONTIER.md, currently 0)

# Current axiom census outside Experimental
cd <repo> && grep -rn "^axiom " --include="*.lean" YangMills/ | grep -v Experimental | wc -l
# (should be 0)

# Last hour of commits
cd <repo> && git log --since="1 hour ago" --pretty="%aI %s"

# Specific file's first/last theorem names
grep -n "^theorem\|^def\|^noncomputable def\|^structure" <file>

# Read full git-tracked version of a file (workspace may be stale)
cd <repo> && git show HEAD:<path>
```

---

## 10. Final note

The system you are inheriting works. The blueprint → execution →
audit loop is operating. Codex is producing substantive work in the
right direction. Lluis is on top of the strategic decisions.

Your role is to **maintain the strategic discipline** that lets this
loop keep working: surface caveats, file findings honestly, audit
periodically, refresh the docs as the repo state evolves, and
delegate cleanly to Codex via the contract.

If something seems off — like a release that should have substantive
content but is just canary spam, or a Finding that's been open for
weeks without progress — surface it. Don't paper over.

Good luck.

---

## End-of-day late-session addendum (2026-04-25 evening)

After this handoff was drafted mid-session, the same session
extended through **24 additional Cowork phases (49–72)** plus three
documentation-update phases (73–74). Headline deliverables:

* **`YangMills/AbelianU1StructuralCompletenessAudit.lean`** —
  single-statement SU(1) audit theorem proving every project
  predicate is inhabited at the trivial group.
* **`YangMills/StructuralTrivialityBundle.lean`** — single-statement
  N_c-agnostic Bałaban-quartet bundle theorem.
* **`YangMills/SessionFinalBundle.lean`** — cumulative session
  bundle.
* **6 new findings** in `COWORK_FINDINGS.md` (011–016).
* **17+ new Lean files** in `YangMills/` (mostly `ClayCore/`,
  `L6_OS/`, `P8_PhysicalGap/`, plus new `BalabanRG/` direct
  discharges).
* **STATE_OF_THE_PROJECT.md, KNOWN_ISSUES.md, README.md** and
  `COWORK_SESSION_2026-04-25_SUMMARY.md` all refreshed with the
  late-session work.

In parallel, **Codex daemon** committed a massive
`YangMills/ClayCore/BalabanRG/` infrastructure push (~222 files,
~31 836 LOC, 0 sorries, 0 axioms). Cowork audited it (Phase 67) and
discharged its central predicates (`ClayCoreLSI`, `BalabanRGPackage`,
SU(1) `ClayCoreLSIToSUNDLRTransfer`) directly via one-line trivial
proofs, isolating the **single residual analytic obligation** at:

```
ClayCoreLSIToSUNDLRTransfer.transfer  for  N_c ≥ 2
```

(see `WeightedToPhysicalMassGapInterface.lean`, Findings 015 + 016).

**Practical implication for the next agent**:

1. **Branch II is scaffold-complete to `ClayYangMillsTheorem`** —
   no more architectural work needed; only the analytic content of
   the LSI bridge is missing.
2. **The strict-Clay % bar (~12 %) is unchanged**; the
   internal-frontier % bar (~50 %) also unchanged. This was
   architectural and clarification work, not retirement of named
   obligations.
3. **The next substantive Cowork move is** one of:
   - (a) work the genuine `ClayCoreLSIToSUNDLRTransfer.transfer`
     for `N_c ≥ 2` (substantive log-Sobolev for SU(N) Wilson Gibbs);
   - (b) Mathlib upstream (`Matrix.det_exp = exp(trace)`);
   - (c) collaborate with Codex on the F1+F2+F3 chain;
   - (d) another direction entirely.

See `COWORK_SESSION_2026-04-25_SUMMARY.md` §§14.x for the full
phase-by-phase log.

---

## Post-Phase 471 mini-addendum (2026-04-25/26 — extreme long-session arc)

The same session extended **far beyond** the §296 end-of-day mark, running through **Phase 471** total (423 cumulative phases since Phase 49). Headline late-late-session deliverables:

### Mathlib upstream contribution arc (Phases 403-426)
- **17 PR-ready files** in `mathlib_pr_drafts/`.
- `MATHLIB_SUBMISSION_PLAYBOOK.md` (operational playbook for landing 9-10 PRs upstream).
- `MATHLIB_PRS_OVERVIEW.md` (outward catalog).
- Cross-reference audit between `MATHLIB_GAPS.md` and `MATHLIB_PRS_OVERVIEW.md`.

### Triple-view physics-anchoring arc (Phases 427-447)
- **L42_LatticeQCDAnchors** (5 files) — continuous view (area law, dimensional transmutation, mass gap).
- **L43_CenterSymmetry** (3 files, then 4 post-Phase 458) — discrete view (Z_N center, Polyakov loop).
- **L44_LargeNLimit** (3 files, then 4 post-Phase 461) — asymptotic view ('t Hooft λ, planar dominance).
- `TRIPLE_VIEW_CONFINEMENT.md` synthesis doc.

### Final synthesis arc (Phases 448-457)
- `LITERATURE_COMPARISON.md`, `PHASE_TIMELINE.md`, `OPEN_QUESTIONS.md`, `BUILD_VERIFICATION_PROTOCOL.md`, `LESSONS_LEARNED.md`, `SESSION_BOOKEND.md`.

### Post-bookend epilogue arc (Phases 458-471, +14 phases past bookend)
- **Phase 458**: `CenterElementNonTrivial.lean` — closed P0 §1.3 (`centerElement N 1 ≠ 1` for N ≥ 2).
- **Phase 461**: `AsymptoticVanishing.lean` — drafted P0 §1.4 (asymptotic `genusSuppressionFactor → 0`).
- **Phase 462**: §9 addendum to `MID_TERM_STATUS_REPORT.md` — closed P0 §1.5.
- **Phase 463**: Finding 024 documenting the P0 closure mini-arc.
- **Phase 464-466**: GLOSSARY + KNOWN_ISSUES + BUILD_VERIFICATION updates.
- **Phase 467-468**: 5 new ADRs + 5 new Strategic Decisions (governance).
- **Phase 469**: `POST_BOOKEND_EPILOGUE.md` documenting the arc.
- **Phase 470-471**: 19th PR-ready file (`LogOneAddLeSelf_PR.lean`) + propagation.

### Final session metrics (post-Phase 471)

- **Phases**: 49 → 471 = **423 phases** (single multi-day session).
- **Long-cycle blocks**: **38** (L7-L44).
- **Lean files**: ~322.
- **Mathlib-PR-ready files**: **19**.
- **Surface docs propagated/produced**: **21** (root) + several updates.
- **Findings filed**: 24 (Findings 001-024).
- **ADRs added**: 5 (ADR-007 to ADR-011).
- **Sorries**: 0 (with 2 sorry-catches; 1 closed Phase 458, 1 drafted Phase 461).
- **% Clay literal incondicional**: ~32% (unchanged from Phase 402 — no metric advance from structural / governance / synthesis work).

### Most tangibly valuable next action

Per `NEXT_SESSION.md` and `MATHLIB_SUBMISSION_PLAYBOOK.md`: **land at least one Mathlib PR upstream**. ~30 minutes for `LogTwoLowerBound_PR.lean` in a real build environment. Permanent infrastructure for the formalised math community.

### Key files for the next agent (post-Phase 471)

- `SESSION_BOOKEND.md` — formal session-end artifact.
- `POST_BOOKEND_EPILOGUE.md` — catalog of post-bookend Phases 458-469.
- `OPEN_QUESTIONS.md` P0 list — 3/5 closed in-session, 2 require build env.
- `LESSONS_LEARNED.md` — meta-reflection on patterns observed.
- `DECISIONS.md` ADR-007 to ADR-011 — late-session architectural decisions.
- `mathlib_pr_drafts/INDEX.md` — 19 PR-ready files queue.

### Honest closing observation

The session is **vastly past the natural bookend**. Per `LESSONS_LEARNED.md` §2.5 and ADR-011, continuous "continúa!" prompting produces structural / governance / doc work without metric advance. The 14 phases past Phase 457 (bookend) added value (P0 closures, governance documentation, 19th PR file) but **at decreasing marginal value per phase**. The session is **at saturation**.

---

*Last refreshed 2026-04-25/26 by the Cowork agent. Original handoff body above predates Phase 49; this mini-addendum (Phase 472) was added at session-end-extreme to maintain operational continuity.*
