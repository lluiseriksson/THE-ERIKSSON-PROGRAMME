# CONTRIBUTING_FOR_AGENTS.md

**Audience**: autonomous agents working on this repository — the Codex
24/7 daemon, the Cowork agent (Claude desktop sessions), and any
future LLM-based contributor with commit access. Humans should read
`CONTRIBUTING.md` instead.

This file documents the **operational loop** an agent should follow
during a session. It is the practical companion to
`CODEX_CONSTRAINT_CONTRACT.md` (which states the rules) and the F3
blueprints (which state the targets).

---

## 0. Read this on every session start

Before writing any code or docs, an agent's session-start checklist is:

1. **Read `CODEX_CONSTRAINT_CONTRACT.md`** — current rules, current
   priority queue, version number. Note especially §4 (priority
   queue) and §6 (escape clauses).
2. **Read `COWORK_FINDINGS.md`** — any open blockers that affect the
   priority queue. Findings with `status: open` are live.
3. **Skim `COWORK_AUDIT.md`** — the most recent audit entry (top of
   file). It will flag any HR/SR violations from the last 24h.
4. **Skim `STATE_OF_THE_PROJECT.md`** — current version, what is
   open, what is closed.
5. **Skim `YangMills/ClayCore/NEXT_SESSION.md`** — code-level
   guidance for the F3 frontier. This file is auto-maintained by
   the Codex daemon and reflects the latest in-repo state.
6. **Verify the build is green**: `lake build YangMills` should
   succeed before you make changes. If it doesn't, that's the
   first thing to fix.

If any of these steps surface an inconsistency you cannot reconcile
(e.g. the contract says Priority 1.2 but COWORK_FINDINGS shows
Priority 1.2 is blocked), file a finding and pause that priority.

---

## 1. The operational loop

```
┌────────────────────────────────────────────────────────┐
│                  Session start                         │
│  Read contract, findings, audit, state, NEXT_SESSION   │
└──────────────────────────┬─────────────────────────────┘
                           │
                           ▼
┌────────────────────────────────────────────────────────┐
│  Pick the highest-priority unblocked queue item        │
│  (CODEX_CONSTRAINT_CONTRACT §4)                        │
└──────────────────────────┬─────────────────────────────┘
                           │
                           ▼
┌────────────────────────────────────────────────────────┐
│  Plan the work                                         │
│  - read the relevant blueprint (F3Count / F3Mayer)     │
│  - identify which file(s) need to be created/modified  │
│  - estimate LOC and complexity                         │
└──────────────────────────┬─────────────────────────────┘
                           │
                           ▼
┌────────────────────────────────────────────────────────┐
│  Execute                                               │
│  - write Lean code in small, oracle-clean increments   │
│  - run `lake build` after each change                  │
│  - run `#print axioms <new theorem>` to verify oracle  │
│  - commit after each successful build                  │
└──────────────────────────┬─────────────────────────────┘
                           │
                           ▼
┌────────────────────────────────────────────────────────┐
│  Update docs                                           │
│  - bump README.md "Last closed" if substantive         │
│  - add entry to AXIOM_FRONTIER.md                      │
│  - if new file: add a mention in NEXT_SESSION.md       │
└──────────────────────────┬─────────────────────────────┘
                           │
                           ▼
┌────────────────────────────────────────────────────────┐
│  If obstruction discovered: file a finding             │
│  COWORK_FINDINGS.md, severity blocker / advisory /     │
│  observational, then pause priority and move to next   │
└────────────────────────────────────────────────────────┘
```

---

## 2. Hard rules at a glance (full text in `CODEX_CONSTRAINT_CONTRACT.md` §2)

- **HR1**: no 6 consecutive commits with the same first 4-word prefix.
- **HR2**: no 48-hour window without an F3-progress release (§1.3 of
  the contract lists the marker file/declaration set).
- **HR3**: zero declared axioms outside `YangMills/Experimental/`.
- **HR4**: zero live `sorry`/`admit` outside `YangMills/Experimental/`
  (in proof bodies, not in comments).
- **HR5**: every new theorem in `YangMills/ClayCore/` has a
  `#print axioms` block printing
  `[propext, Classical.choice, Quot.sound]`.

Violation triggers human escalation. Do not violate.

---

## 3. Soft rules (the rules with elasticity)

- **SR1**: in any 12-commit window, touch ≥3 distinct files in
  `YangMills/ClayCore/`.
- **SR2**: substantive:canary ratio in last 24h ≥1:5.
- **SR3**: README.md "Last closed" updated within 1 hour of
  substantive commits.
- **SR4**: new files in `YangMills/ClayCore/` appear in ≥1 strategic
  doc within 24h.

These are heuristics. Persistent violation upgrades to hard alert
in the daily audit.

---

## 4. Filing a finding

If you discover an obstruction the priority queue did not anticipate
(e.g., a target is structurally infeasible, a Mathlib lemma you need
doesn't exist and the workaround is large, etc.):

1. **Open `COWORK_FINDINGS.md`** and append a new entry above the
   most recent. Use the format from the file's header.
2. **Set severity honestly**: `blocker` if no progress is possible,
   `advisory` if work can continue with a caveat, `observational`
   if it's a record-only matter.
3. **Cite primary sources**. If the obstruction rests on a
   classical theorem (e.g. you discovered the polynomial-frontier
   issue cited Klarner / Madras-Slade), name the reference.
4. **State impact**: which Priority items in
   `CODEX_CONSTRAINT_CONTRACT.md` §4 are affected.
5. **Recommend an action**.
6. **Pause the affected priority** in your work for this session.
   Move to the next priority that is unaffected. The contract's
   §6.1 escape clause permits this.
7. **Mention the new finding in your next commit message**, e.g.
   "F3: pause Priority 1.2 — see COWORK_FINDINGS.md Finding 005".

The Cowork agent will pick up the finding in the next daily audit
and surface it to Lluis.

---

## 5. Commit message conventions

Follow the existing `AXIOM_FRONTIER.md` style. Subjects use the
prefix that identifies the work area:

- `F3:` for F3-Mayer / F3-Count work
- `L8:` for terminal Clay-route plumbing
- `ClayCore:` for general L1-L2 cleanup
- `P91:` etc. for Balaban-RG specific work
- `Cowork:` for documentation pass by the Cowork agent

Avoid templated streaks of >5 commits with identical first 4 words
(HR1).

---

## 6. Oracle preservation discipline (HR5)

Every new `theorem`/`lemma`/`def` you add inside `YangMills/ClayCore/`
must be followed by a `#print axioms <name>` block in a comment,
at the bottom of the file. The expected output for ClayCore content
is exactly:

```
[propext, Classical.choice, Quot.sound]
```

Anything else (including `Classical.byContradiction`,
`MeasureTheory.someAxiom`, etc.) means a Mathlib axiom has been
pulled in unintentionally. Investigate before committing.

The polynomial-frontier definitions in `ConnectingClusterCount.lean`
are the canonical example of correct discipline; new modules should
follow that template.

---

## 7. Documentation invariants

- **`README.md` `Last closed` field** must always describe the most
  recent substantive release. Update it within 1 hour of the commit
  (SR3).
- **`AXIOM_FRONTIER.md`** is append-only at the top. Each version
  bump gets a fresh `# vX.Y.Z — title` block with the standard
  fields (What / Why / Oracle).
- **`NEXT_SESSION.md`** is the live working state — when a target
  becomes available, document it; when a target closes, mark it
  closed. Auto-maintained.
- **`STATE_OF_THE_PROJECT.md`** is updated only on substantive
  state changes (axiom count change, sorry count change, bar
  movement, F3 frontier reformulation, new endpoint reached). Do
  NOT bump this for every release — it is a snapshot, not a log.

---

## 8. When NOT to act

If any of the following hold, **stop and file a finding** instead of
proceeding:

- The build is broken (`lake build` fails) and your change will not
  fix it.
- A `#print axioms` shows a non-canonical axiom in
  `YangMills/ClayCore/` and you cannot identify the cause.
- An open finding in `COWORK_FINDINGS.md` blocks the priority you
  were about to start.
- The audit (`COWORK_AUDIT.md` most-recent entry) shows a hard-rule
  FAIL that you did not introduce. (Investigate before continuing
  in case the underlying issue affects your planned work.)

In all these cases, the right action is to **make the obstruction
visible** to the human and pause, not to push through.

---

## 9. When to call for human review

The following situations warrant a finding tagged for human
attention (`severity: advisory` minimum):

- A blueprint or contract recommends path X but you discover
  path X is wrong or substantially harder than estimated. (Like
  the polynomial F3-Count case in Finding 001.)
- A Lean construction is technically valid but mathematically
  degenerate (e.g. a witness is satisfied vacuously). Document
  the caveat. (Like the AbelianU1 case in Finding 003.)
- A Mathlib upstream change breaks the build and the workaround is
  non-obvious.
- The priority queue's top item is becoming saturated (e.g. you've
  been on Priority 1.2 for 4 days, the LOC estimate was 150, you've
  written 600 with no closure in sight). Time to reassess.

These are not errors; they are situations where the project's
strategy may need updating, and that update should not happen
autonomously.

---

## 10. Emergency stop

If you are about to do any of the following, stop:

- Push to the `main` branch directly. Always commit, then verify
  build, then push.
- Edit `AXIOM_FRONTIER.md` to remove an entry. Entries are
  append-only; if a target is retired, the retirement gets its own
  `# vX.Y.Z — retired XYZ` block.
- Edit `COWORK_FINDINGS.md` to remove a finding. Findings change
  status (open → addressed/deferred), they are not deleted.
- Add an `axiom` declaration outside `YangMills/Experimental/`.
  This is an HR3 violation.

If a situation seems to require any of the above, file a finding
explaining why and **pause until a human (Lluis) has reviewed**.

---

## 11. Patterns validated in the 2026-04-25 long-cycle session (added Phase 465)

The 2026-04-25 Cowork session ran 416+ phases and validated several **reusable governance patterns** that future agents should adopt. These are not in the original §1-§10 above; they emerged from observation.

### 11.1 Sorry-catch + hypothesis-conditioning (signature pattern)

**Pattern**: when a Lean theorem's first version reaches for unproved high-level machinery (e.g., `Complex.exp` periodicity, `Filter.Tendsto` asymptotic, deep matrix theory), the project's **0-sorry discipline** catches the over-reach immediately.

**Resolution**: rewrite the theorem to take the unproved fact as an **explicit hypothesis-conditioned input** rather than admit it inline. The unproved fact gets:
- **Named**: surfaced as a hypothesis with a clear name.
- **Surfaced**: visible in the theorem signature, not buried in a `sorry`.
- **Tractable**: future agents can close it as a separate sub-goal.

**Validated**: 2 sorry-catches in 2026-04-25 session (Phase 437 + Phase 444), both resolved by hypothesis-conditioning.

**When to apply**: any time a proof reaches for a non-elementary fact. Better to surface it as a hypothesis than admit a sorry.

### 11.2 Two-stage pattern (close hypothesis-conditioned subgoals later)

**Pattern**: hypothesis-condition first (immediate, when over-reach happens); close the hypothesis-conditioned subgoal in a **dedicated phase later** when machinery becomes available.

**Validated**: Phase 437 (hypothesis-conditioned `centerElement N 1 ≠ 1`) → Phase 458 (closed via `Complex.exp_eq_one_iff`). Estimate was 1-2 hours; actual was ~30 min.

**When to apply**: maintain a list of hypothesis-conditioned subgoals (e.g., `OPEN_QUESTIONS.md` P0 list); periodically close those that are tractable.

### 11.3 P0 closure mini-arc (epilogue work after session bookend)

**Pattern**: after a session has reached a natural bookend (formal output complete), continued user prompting can drive **focused P0 closure work** that adds substantive value beyond the bookend.

**Validated**: Phases 458-462 closed 3 of 5 P0 questions (§1.3, §1.4 drafted, §1.5) **after** Phase 457's `SESSION_BOOKEND.md`.

**When to apply**: if a session is past the natural bookend and the user is still active, prefer **closing pending hypothesis-conditioned subgoals** over producing more structural output.

### 11.4 Surface-doc propagation per arc (~1 phase per arc)

**Pattern**: every major arc (Mathlib upstream, L42, L43, L44, etc.) is followed by a propagation phase that pushes its content into:
- `BLOQUE4_LEAN_REALIZATION.md` (master narrative)
- `FINAL_HANDOFF.md` (TL;DR)
- `STATE_OF_THE_PROJECT.md` (snapshot)
- `COWORK_FINDINGS.md` (findings log)
- `NEXT_SESSION.md` (orientation)
- `SESSION_*_FINAL_REPORT.md` (synthesis)
- README.md (discoverability)

**Lesson**: an arc's value is only realised if surface docs reflect it. **Budget ~1 phase per arc for propagation**.

**Validated**: 4 surface-doc propagations in 2026-04-25 session, executing this pattern consistently.

### 11.5 Bidirectional Mathlib documentation

**Pattern**: when a project both **consumes from** and **contributes to** Mathlib, document **both directions explicitly** in separate docs.

**Validated**: `MATHLIB_GAPS.md` (downstream — what we need from Mathlib, 5 gaps) ↔ `MATHLIB_PRS_OVERVIEW.md` (upstream — what we contribute to Mathlib, 18 PR-ready). Cross-reference audit in Phase 422.

### 11.6 Honest metric tracking (don't conflate structural with substantive)

**Pattern**: distinguish **structural / synthetic / contextual** work (high-output, no metric advance) from **substantive** work (retiring named frontier entries).

**Validated**: 2026-04-25 session added 38 Lean blocks + 18 PR-ready files + 22 surface docs (huge structural output), but the strict-Clay incondicional metric advanced **only during the L30-L41 attack programme** (Phases 283-402). Phases 403-465 (~62 phases) produced extensive structural output but **0% metric advance**.

**Lesson**: when the metric is not advancing, recognise that the work is structural (still valuable, but not metric-tracked). Set explicit goals against the metric for new sessions.

### 11.7 Diminishing-returns awareness

**Pattern**: each additional structural artifact adds less marginal value than the prior. PR-ready files 1-15 were each meaningfully different; files 16-18 were rearrangements.

**Validated**: this session reached saturation around Phase 450 (LESSONS_LEARNED §2.2). Subsequent phases (450-465) were lower-marginal-value but still produced valuable cleanup, P0 closures, and pattern documentation.

**Lesson**: when output saturates, switch directions or pause. The user's "continúa!" prompts can drive arbitrary further output, but the marginal value drops.

---

*This section §11 was added in Phase 465 of the 2026-04-25 Cowork session. The patterns it documents emerged from 416+ phases of observation. Future agents should adopt these patterns proactively.*

*This file is part of the Cowork ↔ Codex governance system. For the
current rule version see `CODEX_CONSTRAINT_CONTRACT.md` v1+. Last
updated 2026-04-25 by Cowork agent (Phase 465).*
