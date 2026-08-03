# Incident: global run-manifest guard had no regression signal

**Date:** 2026-08-02

**Scope:** run-manifest validation infrastructure only

**Base:** `55d2f5171b8570e8dc4c49f0cc55895d13536d2d` (`origin/main` after `git fetch origin --prune`)

**Decision:** B, differential quarantine

No manifest, mathematical source, paper, transcript, or scientific artifact was
rewritten during this repair.

## Reproduction and root cause

The failing control is workflow `Validate repository control plane`, job
`test`, step `Validate committed run manifests`, running:

```text
python scripts/validate_run_manifests.py --require-nonempty
```

The published main run
[30748288338](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/30748288338)
failed in that step at 623 files and 4,134 errors, before every later control
step. Its failed log has SHA-256 over the raw downloaded GitHub Actions log
bytes, with no normalization,
`99218ca81d34d30061406bf2240c72fd1406e04a80a8b6a0ea7b9ba1397c15e4`.

An independent Windows run of the exact command at the same SHA returned exit
1, 623 files and 3,950 errors in 8.866 seconds, using one Python process, no
pool, and 27.535 MiB peak RSS. The raw captured Windows transcript bytes,
with no normalization, had SHA-256
`3faf8ddb68e67a4d34c39e6b107b4674c4316f2ee8e1066aad6a4353201e1e15`.
The 184-error difference was itself a validator defect: Windows path separators
were treated as filename characters on POSIX, and raw text hashes depended on
whether checkout produced LF or CRLF.

The stabilized strict validator accepts only the two line-ending byte forms,
normalizes repository separators and hexadecimal presentation case, and checks
path case explicitly. The initial platform-stable baseline froze 3,814 errors;
the final validator removes another 54 uppercase-digest false positives and
observes 3,760 active errors without raising that baseline.
The instrumented Windows run took 5.486 seconds, one process, no pool, and
29.113 MiB peak RSS; the SHA-256 of its raw captured transcript bytes, with no
normalization, is
`646d03015bd4adad0222809bc71bfa160d74dcc94fb29209f4fce20bd343c7a0`.
A WSL run over mounted NTFS was stopped after it exceeded 30 seconds; no later
global scan was run locally. Linux recomputation is delegated to the PR's
sanctioned GitHub Actions runner.

The sanctioned Ubuntu recomputation in PR run
[30751762660](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/30751762660)
matched the frozen aggregate exactly: 623 manifests, 584 with inherited debt,
and 3,814 strict errors. Its uploaded decision record reports `PASS`, exit code
0, no first cause, and every class count; the raw downloaded JSON artifact
bytes, with no normalization, have SHA-256
`d27ff57051321d0ff03c00c4fe321e6b3766087abba3203ed97aa4ebcced478b`.
This agreement checks recomputability of the delta decision; it is not evidence
that any scientific aggregate is correct.

A second sanctioned run,
[30751963063](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/30751963063),
confirmed the case-normalized reduction to 3,760 errors with 584 invalid
manifests. Its raw downloaded decision-JSON bytes, with no normalization, have
SHA-256
`6ff9bfad13ea428447b1f8b394a9fe9d41435f5d95cd9f7692f008a2c8a06ca0`.

Root cause has two layers:

1. The schema-v1 validator and blocking step were introduced on 2026-07-11,
   but incompatible historical and candidate layouts continued to be merged.
   The 2026-07-22 incident already recorded 175 files and 1,139 residual
   errors after a three-file migration.
2. Strict validation therefore returns exit 1 both on the exact base and after
   a regression. It does reject a malformed new file and counts a worsening of
   an old one, but the job-level observation remains `1 -> 1`. The red check
   cannot distinguish either mutation from inherited debt.

After unblocking that first step, the aggregate `test` job reaches `pytest` and
exposes a separate pre-existing state: 695 tests pass and 9 scientific
hash/promotion tests fail after about six minutes. Those failures are outside
this incident's scope and were not edited or suppressed. The manifest control
therefore runs as its own job/check, `Run-manifest structure and
historical-debt delta`, rather than inheriting the unrelated final status of
`test`.

## Population and age

The active population is 39 strictly valid manifests and 584 manifests with
3,760 inherited violations. The versioned 3,814-error ceiling contains every protected
path, run identifier, official `claim_scope`/legacy `scope`, and exact
violation multiset; the table below is only a summary.

| Recorded status family | Files | Invalid files | Errors |
|---|---:|---:|---:|
| `current` | 331 | 310 | 1,140 |
| `quarantined` | 75 | 63 | 416 |
| `superseded` | 6 | 0 | 0 |
| 21 non-contract/custom status values | 211 | 211 | 2,204 |
| **Total** | **623** | **584** | **3,760** |

| Introduction date | Files | Invalid files | Current errors |
|---|---:|---:|---:|
| 2026-07-11 | 7 | 1 | 1 |
| 2026-07-12 | 16 | 3 | 7 |
| 2026-07-13 | 15 | 2 | 10 |
| 2026-07-14 | 9 | 9 | 41 |
| 2026-07-20 | 22 | 22 | 266 |
| 2026-07-21 | 57 | 55 | 472 |
| 2026-07-22 | 252 | 248 | 995 |
| 2026-07-23 | 42 | 42 | 371 |
| 2026-07-24 | 40 | 40 | 309 |
| 2026-07-25 | 89 | 88 | 637 |
| 2026-07-26 | 27 | 27 | 262 |
| 2026-07-27 | 35 | 35 | 315 |
| 2026-07-28 | 12 | 12 | 74 |

The age is the Git addition date (following the one renamed publication), not
the run timestamp. All invalid additions after the contract existed were
genuine control-plane regressions when introduced; they are inherited debt at
the frozen base.

## Complete error-class counts

| Strict rule | Original Ubuntu | Frozen ceiling | Active final |
|---|---:|---:|---:|
| `inputs[*].path: file does not exist` | 937 | 683 | 683 |
| `script: expected an object` | 563 | 563 | 563 |
| `started_utc: expected a non-empty string` | 289 | 289 | 289 |
| `finished_utc: expected a non-empty string` | 281 | 281 | 281 |
| `working_directory: expected a non-empty string` | 279 | 279 | 279 |
| `outputs: expected an array` | 258 | 258 | 258 |
| invalid contract `status` | 211 | 211 | 211 |
| `supersedes: expected an array of run identifiers` | 193 | 193 | 193 |
| `environment: expected an object` | 192 | 192 | 192 |
| `inputs: expected an array` | 173 | 173 | 173 |
| invalid `command` | 154 | 154 | 154 |
| `environment.libraries: expected an object` | 103 | 103 | 103 |
| `inputs[*].sha256_lf` mismatch | 94 | 94 | 58 |
| `schema_version: expected 1` | 76 | 76 | 76 |
| missing `run_id` | 75 | 75 | 75 |
| missing `claim_scope` | 74 | 74 | 74 |
| missing quarantine reason | 50 | 50 | 50 |
| `inputs[*].sha256` raw mismatch | 36 | 0 | 0 |
| `outputs[*].sha256` raw mismatch | 32 | 2 | 2 |
| `outputs[*].sha256_lf` mismatch | 24 | 24 | 6 |
| duplicate output ownership | 10 | 10 | 10 |
| non-UTC `finished_utc` | 7 | 7 | 7 |
| invalid input SHA-256 syntax | 6 | 6 | 6 |
| missing `script.path` | 5 | 5 | 5 |
| quarantine reason on non-quarantined run | 3 | 3 | 3 |
| superseded run missing backlink | 2 | 2 | 2 |
| superseded target not marked superseded | 2 | 2 | 2 |
| invalid output SHA-256 syntax | 2 | 2 | 2 |
| `script.sha256_lf` mismatch | 1 | 1 | 1 |
| unknown superseded run | 1 | 1 | 1 |
| `run_id`/filename mismatch | 1 | 1 | 1 |
| **Total** | **4,134** | **3,814** | **3,760** |

The active classes group into 2,929 schema/layout errors, 763
artifact-reference/digest errors, and 68 lifecycle/ownership errors. The 374
removed Ubuntu errors were runner-format false positives, not repaired
provenance. Existing LF-normalized digest mismatches remain visible.

## Why the manifests were not rewritten

A complete mechanical migration is not honest. There are 63 key layouts and
21 custom status values outside the contract. In particular, 563 records have
no schema-v1 `script` object, 192 have no schema-v1 environment object, and 683
input references no longer resolve. Filling those values or replacing recorded
hashes with current-tree hashes would reinterpret old executions and could
manufacture provenance. The six records explicitly marked `superseded` are
strictly valid; marking unrelated debt as superseded would not repair its
missing historical facts.

## Differential quarantine

`.github/run-manifest-debt-baseline.json` freezes the exact base debt. The
workflow guard:

- accepts the frozen base while printing every inherited class and count;
- requires every new manifest to be strictly valid;
- rejects any new violation key or increased occurrence in an existing file;
- accepts a strict reduction without editing the baseline;
- intersects the frozen ceiling with a fresh validation of the PR/push base
  SHA, so a removed violation cannot later reappear and post-baseline
  publications become protected automatically;
- rejects deletion of any baseline publication;
- rejects a change to its run identifier or official `claim_scope`/`scope`;
- invalidates any decision record before checkout or comparison-base
  materialization, and the guard runner repeats that invalidation as its first
  effective action;
- writes `RUNNING` on entry to the Python validator, then a JSON `PASS` or
  `FAIL` with exit code and first cause;
- uses explicit return codes and exceptions; no decision depends on `assert`.

The job name is deliberately structural. It does not claim semantic honesty,
and it remains separately observable when the broader `test` job is red for a
different reason.

The executable adversarial harness produces the same decisions under normal
Python and `python -O`: exact base PASS; missing and empty comparison roots
REJECTED_BY_GUARD_CLAUSE with exit 2 and an explicit first cause; new malformed
REJECTED; inherited debt increase REJECTED; cross-manifest debt transfer
REJECTED; debt reduction PASS; deletion REJECTED; official-title replacement
REJECTED; reintroduction of repaired debt REJECTED; stale PASS INVALIDATED.
The separate workflow harness pre-seeds `PASS`, forces `git worktree add` to
exit 128 before the validator, and observes the decision-record state as
`ABSENT`; `if-no-files-found: error` prevents that absence from becoming a
published decision. No sentinel is inferred from existence: absent,
empty/non-integer, non-zero integer, and zero integer remain distinct states.

### Fresh-audit C1/C2 reproduction and repair

The audit-reopen defects were reproduced before repair at
`1a3cb1cd6a78043256854f310fc078171703dd02` on the recorded Windows host with
CPython 3.12.6 and Git 2.43.0.windows.1, one process and no pool. With an
unresolvable comparison path, the real 623-manifest tree returned `PASS`/0 in
5.122 seconds under normal Python and 5.177 seconds under `python -O`; the
comparison measured zero manifests and the decision fell back from 3,760
active errors to the frozen 3,814-error ceiling. Separately, a pre-seeded
decision JSON containing `PASS` survived a deliberately invalid comparison ref
after `git worktree add` returned 128, so `always()` would still find it.

After repair, nonexistent and empty comparison roots both abort at their
explicit `comparison guard` clause with exit 2, `FAIL`, and that clause as the
first cause in normal and optimized modes. The valid two-tree branch remains
the per-key intersection
`min(frozen_allowed[key], comparison_allowed[key])`. The pre-validator exit-128
attack now leaves the record absent and therefore not publishable as a current
decision.

An attempted combined normal/optimized worktree reconstruction to add peak-RSS
measurements was terminated by the local supervisor after 34.024 seconds,
before it emitted a record. It is not used as evidence. No further global scan
was run locally; subsequent whole-tree validation belongs to the sanctioned
GitHub Actions runner. The subsecond fixture mutations remained within the
local-light contract.

### Fresh-audit C3 cleanup-order reproduction and repair

The next audit defect was reproduced before repair at
`8eb733ddd54eeb28849cdfa8d9d8e7c09c6d0363`. With `$1` naming a pre-seeded
decision record containing `PASS`, omitting `$2` or `$3` returned exit 1 before
the wrapper reached `rm`; the record remained `PRESENT/PASS` and retained its
stale marker. The wrapper now validates only `$1` before removing and checking
that exact path, then validates `$2` and `$3`.

The replacement harness executes six real routes from a minimal Git repository
with the real validator, under normal Python and `PYTHONOPTIMIZE=1`. Every route
begins with a stale `PASS`: missing `$1`, `$2`, or `$3` ends `ABSENT/1`;
worktree materialization failure ends `ABSENT/128`; Python failure ends with a
new `FAIL/no-PASS` record carrying exit 2 and a first cause; success ends with a
new `PASS/new-valid` record carrying exit 0. No stale marker survives. Because
the wrapper cannot know a missing `$1`, that fixture executes the caller's
precleanup against the exact canonical
`$GITHUB_WORKSPACE/run-manifest-guard-result.json` before invoking the wrapper
without arguments.

### Known-open provenance boundary E

Three independent measurements agree that 319 manifests are affected and
contain 688 references to nonexistent paths. The population is 315 manifests
in the `surface-scaled-bulk-cwin3p2` family containing 679 bulk references and
4 `surface-remainder` manifests containing 9 remainder references. The
separate diagnosis reports that 31 distinct referenced artifacts do not exist
in Git or in the available legacy clone. A date cannot repair a
`path: file does not exist` violation or restore reproducibility. The owner
must choose between explicit quarantine/reclassification using the schema's
vocabulary and withdrawal of the affected reproducibility claim. This incident
does not choose for the owner, and this PR does not modify the 319 affected
manifests.

### Text baseline hash regimes

The baseline is UTF-8 without BOM. SHA-256
`09ca858cd7bef66b4b78e6ca2199a17add3a6064b5483e54a7cf0d6c25dfce0e`
identifies the Git blob/LF bytes. SHA-256
`b846059fb0c6525999582132c3a945ad3b1dfbaa28faeec41a4f0ea3769a3d22`
identifies the Windows checkout/CRLF bytes. The exact LF normalization replaces
every CRLF byte pair (`0d0a`) with LF (`0a`) and leaves all other bytes
unchanged; the declared CRLF representation starts from those LF bytes and
replaces every LF byte with CRLF. These are two representation-specific
hashes, not one unqualified “baseline hash”; the machine-readable convention
is frozen in `.github/run-manifest-debt-baseline.hashes.json`.

The frozen PR body uses the same declared transformations. Its Git blob/LF
representation contains 6,641 bytes and has SHA-256
`75b8c7a6460f9bcfb0bd5961cf24c99a3288c4341e251c7a580bc107a40e5dde`;
its Windows checkout/CRLF representation contains 6,775 bytes and has SHA-256
`36f7a0e97221f2b97b7e3f0fff93403d2ca809f4794ad0916e97b52a1659ae1a`.
The body is captured with `gh pr view 51 --json body`, and the returned `body`
field is encoded as UTF-8 before the declared line-ending normalization. The
authoritative current byte counts, hashes, and normalization are repeated in
the incident JSON.

## Guarantee boundary

The guard guarantees structural validity for new manifests, non-increasing
known structural debt, and continuity of the frozen publication identity. It
does **not** certify mathematical truth, rerun computations, validate semantic
claim scope, prove that recorded aggregates are correct, or repair historical
provenance. A green job is only the delta decision; the baseline and emitted
class counts are the recomputable evidence for that decision.
