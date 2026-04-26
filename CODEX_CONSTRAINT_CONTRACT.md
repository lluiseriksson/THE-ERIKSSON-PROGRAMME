# CODEX_CONSTRAINT_CONTRACT.md

**Version**: v1 (2026-04-25)
**Author**: Cowork agent (Claude), under supervision of Lluis Eriksson
**Audience**: the autonomous Codex 24/7 daemon driving commits to this repo
**Purpose**: prevent canary-spam drift — ensure throughput translates into
actual progress on the F3 frontier rather than ergonomic variations.

---

## 0. Why this exists

At ~150 commits/day, Codex is producing more output than any human can
review in detail. The risk pattern observed empirically (e.g.
v1.71→v1.72→v1.73 all `mono_dim_apply` canaries on different structures)
is **canary-spam drift**: throughput stays high but the named open
packages remain untouched.

The contract below is the **machine-checkable scaffolding** that
distinguishes productive cadence from drift. The autonomous daemon
should read this on every session start; the daily audit
(`eriksson-daily-audit` scheduled task) evaluates compliance and
flags violations.

This is heuristic, not theorem-grade. False positives are tolerated
(prefer over-flagging to under-flagging). False negatives — drift that
goes undetected — are the failure mode to minimise.

---

## 1. Definitions

### 1.1 Canary release

A commit / release whose primary contribution is one or more of:

- An `_apply` accessor on an existing structure (no new mathematical
  content).
- A `mono_dim` / `mono_count_dim` raising of a polynomial exponent.
- An `ofBound` / `ofAtFamily` / `ofGlobalMayer` constructor with the
  same body shape as an existing one.
- A `toPhysical` / `toPhysicalOnly` / `toAt` / `toDim` projection where
  the witness already exists at a more general scope.
- A renaming, file split, or import rearrangement.
- A `#print axioms` declaration (oracular canary).

Canaries are **legitimate work** — they're how an API gets ergonomic.
The contract bounds their *concentration*, not their existence.

### 1.2 Substantive release

A commit / release whose primary contribution is one or more of:

- Creation of a new `.lean` file under `YangMills/ClayCore/` or its
  subdirectories that closes a named open target from `NEXT_SESSION.md`,
  `BLUEPRINT_F3Count.md`, or `BLUEPRINT_F3Mayer.md`.
- A theorem with a proof body of ≥30 lines containing real mathematical
  content (not just `simp` / `rfl` / structural manipulation).
- The construction of a witness for any of the named open frontier
  predicates (see §1.3).
- Retiring an axiom from `YangMills/Experimental/` to a proven theorem.

### 1.3 F3 progress markers

**These are the named declarations that mark substantive F3 progress.**
They are the things the contract asks Codex to attack:

| Marker | Location (target) | Status as of 2026-04-25 |
|---|---|---|
| `connecting_cluster_count_exp_bound` | `YangMills/ClayCore/LatticeAnimalCount.lean` (new file) | open |
| `physicalShiftedConnectingClusterCountBoundExp_witness` | `YangMills/ClayCore/ConnectingClusterCountExp.lean` | open |
| `interpolatedClusterAverage` | `YangMills/ClayCore/MayerInterpolation.lean` (new file) | open |
| `truncatedKFromInterpolation` | `YangMills/ClayCore/MayerInterpolation.lean` | open |
| `truncatedK_zero_of_not_polymerConnected` | `YangMills/ClayCore/MayerInterpolation.lean` | open |
| `haar_integral_factorise_disjoint_links` | `YangMills/ClayCore/HaarFactorization.lean` (new file) | open |
| `truncatedK_abs_le_normSup_pow` | `YangMills/ClayCore/BrydgesKennedyEstimate.lean` (new file) | open |
| `physicalConnectedCardDecayMayerWitness` | `YangMills/ClayCore/PhysicalConnectedCardDecayWitness.lean` (new file) | open |
| `physicalShiftedF3MayerCountPackage` (assembly) | `YangMills/ClayCore/ClusterRpowBridge.lean` (existing) | open, blocked on the above |
| `wilsonUniformRpowBound_from_F3` | TBD | open, blocked on above |
| `clayMassGap_smallBeta_for_N_c` (N_c ≥ 2) | TBD | open, terminal |

A release counts as **F3-progress** if it creates or substantively
modifies (≥10 LOC of mathematical content) any file containing a
target marker, OR closes a marker.

---

## 2. Hard rules (MUST NOT)

These rules are absolute. Violation should trigger an immediate human
review.

### HR1 — No 6+ consecutive canaries with same prefix

If the last 5 commits all share the same first 4 words of subject
line (e.g. all start with "F3: expose mono_dim"), the next commit
MUST NOT extend that streak. The next commit must either be
substantive (§1.2) or change the topic.

**Detection**: `git log -6 --pretty=%s | awk '{print $1,$2,$3,$4}'`
shows 6 identical lines.

### HR2 — No 48h F3-progress drought

In any rolling 48-hour window, at least one F3-progress release
(§1.3) MUST occur. If the window is approached, the daemon should
prioritise an F3 marker over any other work.

**Detection**: `git log --since="48 hours ago" --name-only` does not
include any of the F3 marker files (or new files at the marker paths).

### HR3 — No axiom drift outside Experimental

`git grep -n -E "^axiom " -- "*.lean" | grep -v Experimental` must
return empty after every commit. If a commit introduces a
non-Experimental axiom, the next commit MUST revert or relocate it.

**Detection**: trivial git grep.

### HR4 — No `sorry` / `admit` outside comments and history

Any commit containing live `sorry` or `admit` (not inside `/-` ... `-/`
or `--` comments) outside `YangMills/Experimental/` MUST be reverted
or completed within 24h.

**Detection**: ripgrep with multiline support, exclude comments.

### HR5 — Oracle preservation

Every new theorem in `YangMills/ClayCore/` should declare
`#print axioms <theorem_name>` and the printed list must be
`[propext, Classical.choice, Quot.sound]`. This is already the
project's discipline; the contract makes it a hard rule.

**Detection**: parse `#print axioms` lines from commit diffs.

---

## 3. Soft rules (SHOULD)

Violation triggers a soft warning in `COWORK_AUDIT.md`, not human
escalation. Multiple soft rule violations in a 24h window are upgraded
to a hard alert.

### SR1 — Diversify file targets

In any 12-commit window, at least 3 distinct files in
`YangMills/ClayCore/` should be touched. If the same file dominates
≥10 of the last 12 commits, that's a soft warning.

### SR2 — Maintain progress signal-to-noise

In any 24h window, the ratio (substantive releases : canary releases)
should be at least 1:5. (At 150 commits/day, this means ≥25
substantive per day. At minimum 1:10 is acceptable for sustained
canary phases — but only for at most 3 consecutive days.)

### SR3 — README "Last closed" must be updated

Any release that constitutes substantive progress (§1.2) should be
reflected in `README.md` "Last closed" block within 1 hour of the
commit. The README is the public-facing source of truth.

### SR4 — Proportional documentation

For any new file created in `YangMills/ClayCore/`, a corresponding
mention should appear in either `NEXT_SESSION.md`, `STATE_OF_THE_PROJECT.md`,
or `AXIOM_FRONTIER.md` within 24h. Files that exist but appear in no
strategic doc are candidates for being orphaned.

---

## 4. Current priority queue

These are the deliverables Codex should attack, **in order**.
Skipping a higher-priority item to work on a lower-priority one
without explicit human approval is a soft violation.

The queue is updated by Lluis (or by Cowork agent under his
supervision) as items close. The current queue (as of 2026-04-25):

### Priority 1 — F3-Count witness (Resolution C)

Smallest, most actionable. Approximately 400 LOC across 1-2 new files.

1.1. **Empirical sanity check** (~50 LOC of `#eval` or `example`):
     verify that the polynomial form of `ShiftedConnectingClusterCountBound`
     is structurally infeasible per `BLUEPRINT_F3Count.md` §6. If
     confirmed, deprecate the polynomial frontier.

1.2. **`LatticeAnimalCount.lean`** (~150 LOC): prove the BFS-tree
     bound `count(m) ≤ Δ^(m-1)` for connected anchored subgraphs of
     a max-degree-Δ graph. Specialise to plaquette graph at d=4,
     get `K = 7` (or looser, e.g. `K = 64`).

1.3. **`physicalShiftedConnectingClusterCountBoundExp_witness`**:
     instantiate the witness for `d = 4`, packaged as
     `PhysicalShiftedF3CountPackage`.

### Priority 2 — F3-Mayer scaffolding

Approximately 600 LOC across 4 new files. Sequential.

2.1. **`MayerInterpolation.lean`** (~250 LOC): the BK interpolation
     polynomial, vanishing at `s=0`, agreement with cluster average at
     `s=1`.

2.2. **`HaarFactorization.lean`** (~150 LOC): independence of disjoint
     plaquette link sets under the Wilson-Gibbs measure. Project-local
     wrapper around `MeasureTheory.Measure.pi`.

2.3. **`BrydgesKennedyEstimate.lean`** (~250 LOC): the analytic boss.
     The bound `|K(Y)| ≤ ‖w̃‖_∞^|Y|`. **Critical milestone.**

### Priority 3 — F3 packaging

3.1. **`PhysicalConnectedCardDecayWitness.lean`** (~100 LOC): combine
     2.1-2.3 to produce `physicalConnectedCardDecayMayerWitness` for
     `β < log(2)/N_c`.

3.2. **Combined `PhysicalShiftedF3MayerCountPackage` assembly**: glue
     1.3 and 3.1 in `ClusterRpowBridge.lean`.

### Priority 4 — Terminal Clay theorem

4.1. **`wilsonUniformRpowBound_from_F3`**: produce
     `WilsonUniformRpowBound N_c β C` from the F3 packages, with
     `r = 4 N_c β`, `K = 7`, validity `β < 1/(28 N_c)`.

4.2. **`clayMassGap_smallBeta_for_N_c`**: produce
     `ClayYangMillsMassGap N_c` for `N_c ≥ 2` from 4.1, mirroring the
     `clayMassGap_small_beta_of_uniformRpow` chain that already
     consumes the rpow bound.

### Priority 5 — Background / non-blocking

5.1. Mathlib upstream PRs per `MATHLIB_GAPS.md` (Gap #1 has a draft
     ready in `mathlib_pr_drafts/`).
5.2. Trim of `PETER_WEYL_ROADMAP.md` per `PETER_WEYL_AUDIT.md` §5.
5.3. Deprecation markers per `PETER_WEYL_AUDIT.md` §6.

---

## 5. Detection rules (for `eriksson-daily-audit`)

The daily audit task should evaluate the following checks and report
each as PASS / FAIL / WARN:

```
[HR1] git log -10 --pretty=%s | check no 6+ identical 4-word prefixes
[HR2] git log --since="48 hours ago" --name-only | check ≥1 marker file touched
[HR3] git grep -n -E "^axiom " -- "*.lean" | grep -v Experimental | empty?
[HR4] rg --multiline 'sorry|admit' YangMills/ --exclude Experimental/ | empty (modulo comments)
[HR5] git log -50 --pretty=%H | check each commit's #print axioms blocks parse to canonical oracle
[SR1] git log -12 --name-only | YangMills/ClayCore/*.lean | unique file count ≥3
[SR2] git log --since="24 hours ago" --pretty=%s | substantive:canary ratio ≥1:5
[SR3] README.md "Last closed" version field matches latest substantive commit
[SR4] new files in YangMills/ClayCore/ in last 24h have a mention in {NEXT_SESSION, STATE_OF_THE_PROJECT, AXIOM_FRONTIER}
```

The audit task's prompt should be updated to evaluate these checks
and append results to `COWORK_AUDIT.md` in addition to the existing
canary-spam / axiom-drift / orphan-file checks. (Subset overlap is
acceptable — redundancy in audit is better than gaps.)

---

## 6. Escape clauses

The contract is heuristic. There are legitimate reasons to violate it:

### 6.1 Substantive obstruction discovered

If during work on a Priority N item, Codex discovers that the item is
malformed (e.g. the structural infeasibility flagged in
`BLUEPRINT_F3Count.md` §2 for the polynomial frontier), it MAY:
- Write a finding to `COWORK_FINDINGS.md` (create if absent).
- Pause that Priority N item.
- Move to the next priority while flagging.

This is exactly what should have happened (and did, via Lluis) for
the polynomial F3-Count frontier.

### 6.2 Mathlib upstream block

If a Priority item depends on a Mathlib lemma that does not exist,
Codex MAY:
- Open the corresponding PR draft in `mathlib_pr_drafts/`.
- Move to the next priority while waiting.

### 6.3 Human override

Lluis can override any constraint by editing this document and
incrementing the version number in the header. The daemon should
re-read the contract on each session start.

---

## 7. Update procedure

This contract should be **revisited weekly** (or whenever a Priority
item closes). The procedure:

1. Cowork agent (or Lluis) audits compliance against the rules.
2. Items 1.x → 4.x are renumbered as they close (closed items move to
   §8 below).
3. Hard rules are tightened or relaxed based on observed cadence.
4. Version number incremented; date updated.

### Version history

- **v1 (2026-04-25)**: initial contract drafted by Cowork agent.

---

## 8. Closed items (archive)

(empty — items move here when they close)

---

*This contract is a tool, not a law. Its purpose is to make drift
detectable, not to constrain Codex's creativity. If the rules become
obstacles to genuine progress, edit them.*
