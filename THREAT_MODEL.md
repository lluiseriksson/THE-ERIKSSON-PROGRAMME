# THREAT_MODEL.md

**Author**: Cowork agent (Claude), strategic risk pass 2026-04-25
**Subject**: failure modes of THE-ERIKSSON-PROGRAMME and how to detect
each early
**Audience**: Lluis Eriksson (project lead), future Cowork agents,
external reviewers evaluating project robustness

This is a **defensive** document: not predictions of what will go
wrong, but a structured catalogue of what **could** go wrong and how
the existing governance system would surface each. Reading this
should make the project's failure modes concrete enough that they
stop being unknown unknowns.

---

## 0. Threat severity scale

- **Existential**: would invalidate the project's mathematical
  contribution or the formalisation correctness.
- **Major**: would set the project back substantially (weeks-months)
  but is recoverable.
- **Minor**: would cost a session or two but is easy to recover from.
- **Cosmetic**: documentation issues, naming, etc.

---

## 1. Mathematical / scientific failure modes

### 1.1 The Brydges–Kennedy estimate doesn't apply as expected

**Scenario**: when the F3-Mayer witness is being constructed
(`BLUEPRINT_F3Mayer.md` §4.1, Priority 2.3), the BK forest estimate
turns out to be tighter or looser than the blueprint claims, or
requires additional hypotheses (e.g. tighter regularity on the
plaquette fluctuation than the project supplies).

**Severity**: major.

**Likelihood**: low. BK has been applied to lattice gauge theory
for 40 years; the technique is well-trodden. The project's
formulation matches the literature.

**Detection**:
- Codex hits a structural obstacle in `BrydgesKennedyEstimate.lean`
  that cannot be patched in <500 LOC.
- The smallness regime `β < 1/(28 N_c)` widens or narrows
  unexpectedly during witness construction.
- A new finding is filed in `COWORK_FINDINGS.md` with severity
  `blocker`.

**Mitigation**:
- The blueprint `BLUEPRINT_F3Mayer.md` §6 risk register identifies
  alternatives (Battle-Federbush variant, simpler weaker estimate)
  if BK proper is too heavy.
- The project's modular structure means a partial witness can
  still feed into `ShiftedF3MayerCountPackageExp.ofSubpackages`
  with adapted constants.

**Recovery cost**: 1-3 weeks of refactor.

### 1.2 The lattice-animal count `(2d-1)^n` is structurally too loose

**Scenario**: when the Klarner BFS-tree count is being formalised
(Priority 1.2.3), the bound turns out to require a tighter `K`
than `2d - 1` to satisfy the smallness `K · r < 1` for the project's
target β-regime.

**Severity**: minor (the convergence regime narrows; doesn't
invalidate).

**Likelihood**: low. The literature has explicit bounds; the project
already documents both tight (`2d-1=7`) and loose (`4d²=64`)
variants in `mathlib_pr_drafts/F3_Count_Witness_Sketch.lean`.

**Detection**: the Codex daemon finds that the Klarner bound it
proves doesn't unlock the target β regime when consumed by the
F3-Mayer chain. Surfaced via failed build of the integration
endpoint.

**Mitigation**: tighter constants from the literature
(Madras-Slade gives `μ_d ≤ 4.7` for d=4 self-avoiding walks, but
polymer counts may use a different constant). The blueprint
includes the consumer-side flexibility via `mono_dim` machinery.

**Recovery cost**: a few sessions of constant-optimisation.

### 1.3 A foundational Mathlib theorem changes signature

**Scenario**: a Mathlib `master` update changes the API of
`MeasureTheory.Measure.haarMeasure`, `Matrix.specialUnitaryGroup`,
or `MeasureTheory.Constructions.Pi`. The project's build breaks.

**Severity**: minor (Mathlib changes are routine and recoverable).

**Likelihood**: medium. Mathlib `master` is unstable by design.

**Detection**: `lake build YangMills` fails. The daily auto-audit
flags an HR4-style violation if any `sorry` is introduced as a quick
patch.

**Mitigation**: pin `lean-toolchain` and `lakefile.lean` to specific
revisions; update on a controlled cadence rather than tracking
master continuously. The project currently tracks `master` (per
README badge `Mathlib master`); that is a deliberate
high-frequency-update choice.

**Recovery cost**: usually <1 day of patches per Mathlib update.

### 1.4 The continuum-trick caveat (Finding 004) becomes externally embarrassing

**Scenario**: an external reviewer or reader notices that
`ClayYangMillsPhysicalStrong` is satisfied via the coordinated
scaling and accuses the project of overclaiming.

**Severity**: cosmetic (in technical terms) but **major** in
reputational terms if uncaught.

**Likelihood**: medium-high *if* the project announces externally
without first executing Option C of `GENUINE_CONTINUUM_DESIGN.md`.

**Detection**:
- Pre-emptive: the caveat is now documented in `STATE_OF_THE_PROJECT.md`,
  `MATHEMATICAL_REVIEWERS_COMPANION.md`, `MID_TERM_STATUS_REPORT.md`,
  and `COWORK_FINDINGS.md` Finding 004. Anyone reading the
  project's strategic docs will encounter the qualifier before the
  technical claim.
- Reactive: external comments / questions. Surfaced via channels
  outside this audit's scope.

**Mitigation**:
- Continue the discipline: every external description includes the
  qualifier.
- Execute Option C of `GENUINE_CONTINUUM_DESIGN.md` (refactor
  `HasContinuumMassGap` to take a spacing scheme parameter)
  **before** any external announcement of "Clay-grade endpoint".

**Recovery cost**: if pre-empted, $0$. If embarrassment occurs, a
reputational clarification is needed but the technical content is
sound.

### 1.5 An unknown axiom leaks into ClayCore via Mathlib

**Scenario**: a `#print axioms` block in a ClayCore theorem starts
showing an axiom beyond `[propext, Classical.choice, Quot.sound]`.
The cause is a Mathlib lemma that was previously theorem-grade but
has been refactored to depend on a new axiom (e.g.,
`Classical.byContradiction` if not already pulled in transitively,
or `Quotient.lift_mk` etc.).

**Severity**: major. Violates HR5.

**Likelihood**: low. Mathlib's invariants strongly discourage new
axioms.

**Detection**:
- Codex per-commit `#print axioms` check (HR5 in the contract).
- Daily auto-audit `eriksson-daily-audit` independently verifies.
- Per-build CI (when invoked).

**Mitigation**:
- Identify the Mathlib lemma that pulled the axiom in.
- Either work around (use a different lemma) or open a Mathlib
  issue.
- File a finding and pause affected work until resolved.

**Recovery cost**: <1 day.

---

## 2. Process / governance failure modes

### 2.1 Codex daemon enters a canary-spam loop

**Scenario**: the autonomous Codex daemon iterates on cosmetic
ergonomic variations (`mono_dim_apply`, `_ofBound` accessors, etc.)
without progressing on the priority queue. Days pass with high
commit count but zero F3-progress markers.

**Severity**: minor (wasteful but recoverable).

**Likelihood**: medium. Was actually observed at v1.73-v1.78 (six
consecutive `mono_dim_apply` releases).

**Detection**:
- HR1 (no 6+ canary streak) and HR2 (no 48h F3 drought) trigger.
- Daily audit reports the violation in `COWORK_AUDIT.md`.

**Mitigation**:
- The contract's HR1+HR2 bounds the loop's duration.
- Lluis intervenes per the contract's escalation pathway.
- The blueprint → execution → audit cycle (validated empirically
  to take ~3-4 hours) provides a corrective signal.

**Recovery cost**: 1-2 hours to redirect Codex to the next priority.

### 2.2 The Cowork session ends mid-task without handoff

**Scenario**: this Cowork session ends abruptly (context window
exhausted, app closed, etc.) leaving partial work, an unresolved
finding, or a half-written blueprint.

**Severity**: minor.

**Likelihood**: medium (sessions are session-scoped, not persistent).

**Detection**:
- Lluis notices that strategic docs aren't being maintained.
- A future Cowork agent reads `AGENT_HANDOFF.md` and
  `COWORK_FINDINGS.md` to reconstruct state.

**Mitigation**:
- `AGENT_HANDOFF.md` is the persistent handoff document.
- Findings are append-only; partial work is documented.
- The daily auto-audit continues running independent of any
  Cowork session.

**Recovery cost**: a future agent's first session is spent reading
the handoff and inventory. Subsequent sessions resume normally.

### 2.3 A finding stays open for >2 weeks without progress

**Scenario**: Finding 003 (AbelianU1 caveat) or Finding 004
(continuum-trick) remain `status: open` for an extended period
without the recommended actions being executed.

**Severity**: minor.

**Likelihood**: medium (action items can drift).

**Detection**: by the discipline of "Avoid leaving findings as
`open` for >2 weeks" stated in `COWORK_FINDINGS.md` format spec.
A future audit pass will surface long-open findings.

**Mitigation**:
- Periodic Cowork sessions check `COWORK_FINDINGS.md` status.
- The daily auto-audit could be extended to flag findings open
  >7 days.
- Lluis can manually close, defer, or address.

**Recovery cost**: 1 session to address each lingering finding.

### 2.4 The contract becomes stale relative to actual work

**Scenario**: the priority queue in `CODEX_CONSTRAINT_CONTRACT.md`
§4 lists Priority 1.2 as the active item, but Codex has moved on
to Priority 2.x without updating the contract.

**Severity**: minor.

**Likelihood**: high (contract update is a manual step).

**Detection**: the daily audit's "highest-priority queue item"
recommendation diverges from observed Codex activity.

**Mitigation**:
- The contract has an "Update procedure" (§7) calling for weekly
  revision.
- Lluis or Cowork agent bumps version when a priority closes.

**Recovery cost**: 30 minutes per refresh.

---

## 3. Operational / infrastructure failure modes

### 3.1 The repository is corrupted

**Scenario**: a force-push, branch deletion, or filesystem
corruption damages the repo state.

**Severity**: existential if catastrophic, minor if recoverable
from git history.

**Likelihood**: low.

**Detection**: build failure, missing files, history anomalies.

**Mitigation**:
- Repo is presumably hosted on a remote (GitHub) with full history.
- Local clones can restore.
- The strategic docs (this and the others in the repo root) are
  also preserved in git.

**Recovery cost**: a few hours if remote is intact; substantial if
both local and remote are lost.

### 3.2 The Codex daemon stops running

**Scenario**: the autonomous Codex daemon (whatever infrastructure
runs it) crashes, hits an API quota, or is paused.

**Severity**: minor (the project simply pauses; no degradation).

**Likelihood**: medium.

**Detection**: cadence drops to zero in the daily audit. `git log
--since` shows no commits.

**Mitigation**:
- The system is designed to tolerate variable cadence.
- Lluis can manually drive Codex (or any other Lean agent)
  through the contract's priority queue.

**Recovery cost**: $0$ — the project waits for the daemon to
resume.

### 3.3 Mathlib `master` has a long-lived breakage

**Scenario**: a Mathlib master commit introduces a bug or
incompatibility that takes weeks to fix upstream. The project's
build is broken throughout.

**Severity**: major.

**Likelihood**: low (Mathlib has CI; serious breakages are rare
and quickly fixed).

**Detection**: build failures persist across multiple Codex
sessions. Daily audit flags consistent failures.

**Mitigation**:
- Pin to a known-good Mathlib commit while waiting for upstream
  fix.
- Resume `master` tracking once upstream lands the fix.

**Recovery cost**: pin/unpin a few times; usually <1 week.

---

## 4. External / human failure modes

### 4.1 Lluis is unavailable for an extended period

**Scenario**: Lluis cannot supervise the project for weeks.
Decisions that need human review (renames, axiom retirement
approvals, scope changes) accumulate.

**Severity**: minor (the autonomous side keeps running per the
contract; only strategic decisions wait).

**Likelihood**: medium.

**Detection**: open findings of severity `advisory` accumulate.

**Mitigation**:
- The contract's escape clauses (§6) let Codex continue on
  unblocked priorities.
- Cowork agent can write design proposals (like
  `GENUINE_CONTINUUM_DESIGN.md`) so that when Lluis returns the
  options are pre-analysed.

**Recovery cost**: $0$ during absence; one session of catch-up
reviews on return.

### 4.2 An external mathematician publishes a refutation

**Scenario**: a paper or comment claims that the project's
formalisation is wrong or its claims are overstated.

**Severity**: existential if correct, recoverable if wrong.

**Likelihood**: low. The project's documents are unusually
self-critical (Findings 003, 004 explicitly flag overclaiming
risks).

**Detection**: external communication.

**Mitigation**:
- Take the criticism seriously; verify.
- If criticism is correct, file a finding, retract, fix.
- If criticism is wrong, respond with the relevant evidence
  (Lean theorem statements, `#print axioms` outputs, etc.).

**Recovery cost**: hard to estimate. Depends on the criticism.

### 4.3 The project becomes more popular than expected

**Scenario**: external attention (academic interest, press,
contributors) overwhelms the human-supervision capacity.

**Severity**: cosmetic (good problem to have).

**Likelihood**: low to medium. The project's external profile is
currently low.

**Detection**: increased issue count, PR submissions, citations
in academic work.

**Mitigation**:
- `CONTRIBUTING.md` and `CONTRIBUTING_FOR_AGENTS.md` provide
  process guidance.
- The strategic docs are well-organised for external readers
  (`DOCS_INDEX.md`, `MATHEMATICAL_REVIEWERS_COMPANION.md`,
  `MID_TERM_STATUS_REPORT.md`).
- Lluis can delegate review to trusted contributors.

**Recovery cost**: moderate; depends on volume.

---

## 5. Composite / cascade failure modes

### 5.1 BK estimate fails AND Mathlib gap appears

**Scenario**: Priority 2.3 hits an obstacle, and during the
attempted workaround Codex needs a Mathlib lemma that doesn't exist
and is large to formalise.

**Severity**: major.

**Likelihood**: low.

**Detection**: two findings filed in close succession, both
blocking.

**Mitigation**: open `mathlib_pr_drafts/` PRs for the missing
lemma in parallel with the Lean workaround. Use the existing PR
infrastructure (PRs already drafted for Gaps #1, #2, #3).

### 5.2 Codex spam + Lluis unavailable + Mathlib breakage

**Scenario**: triple compound failure. Codex hits canary spam
exactly when Lluis is unavailable to redirect, and Mathlib master
breaks during the same period.

**Severity**: cascade — no single severity but loss of effective
forward progress.

**Likelihood**: very low.

**Detection**: daily audit flags multiple HR violations + build
failures + cadence anomaly.

**Mitigation**:
- The system is designed to be resilient via independent
  governance layers (contract, audit, findings, blueprints).
- A future Cowork session could restart the system using
  `AGENT_HANDOFF.md`.

---

## 6. Early-warning signals (consolidated)

The following daily-audit fields, taken together, give an early
warning across most threats above:

| Audit field | Threats it warns about |
|---|---|
| Cadence (commits/24h) | 2.1 (canary spam), 3.2 (daemon down) |
| HR1 (canary streak) | 2.1 |
| HR2 (F3 drought) | 1.1, 1.2, 2.1 |
| HR3 (axiom drift) | 1.5 |
| HR4 (sorry) | 2.1 (covering with sorry) |
| HR5 (oracle preservation) | 1.5 |
| SR2 (substantive ratio) | 2.1 |
| Build status | 1.3, 1.5, 3.1, 3.3 |
| New file in F3 markers | 1.1, 1.2 (substantive progress) |
| Open findings count | 2.3 |

A clean audit ⇒ no detected threat from this catalogue. A flagged
audit ⇒ inspect the specific field and consult this threat model
to identify the underlying scenario.

---

## 7. Threat model maintenance

This document should be revisited when:

- A new failure mode is observed (file as a new §1.x or §2.x entry).
- An existing risk's likelihood changes (e.g., 1.3 likelihood
  drops if Mathlib pinning is adopted).
- A threat materialises (move from "could happen" to "did happen";
  document the actual recovery and update mitigation).

---

*Prepared 2026-04-25 by Cowork agent. This is an inventory, not a
prediction. The project is healthy as of the audit date.*
