## Summary

Restore regression signal to the global run-manifest control with a versioned,
reviewable differential quarantine. This PR does not modify any run manifest,
Lean source, paper, transcript, or scientific artifact.

Base audited: `55d2f5171b8570e8dc4c49f0cc55895d13536d2d`.

## Root cause and decision

The strict schema-v1 command already failed on the exact base: 623 manifests,
4,134 errors on the published Ubuntu run and 3,950 on Windows. The check
therefore returned exit 1 both before and after a new regression. Historical
records span 63 layouts and 21 non-contract status values; filling missing
execution facts or replacing old hashes would manufacture provenance.

This PR chooses route B, differential quarantine. It removes 374 runner-format
false positives, observes 3,760 active strict violations, and freezes an
explicit 3,814-error ceiling: 39 manifests are strict-valid and 584 carry
visible inherited debt.

## Changes

- add a baseline keyed by protected publication path, run ID, official
  `claim_scope`/legacy `scope`, and exact violation multiset;
- pass when debt is unchanged or reduced, and fail on any invalid new manifest
  or increased existing violation;
- intersect the frozen ceiling with the exact PR/push base so repairs ratchet
  automatically and cannot later reappear;
- reject deletion or retitling of a protected publication;
- make repository path and LF/CRLF validation runner-independent;
- publish a dedicated check/job named
  `Run-manifest structure and historical-debt delta`, independent of unrelated
  downstream `pytest` debt;
- emit and upload a JSON decision record containing status, exit code, first
  cause, and recomputable class counts;
- run explicit adversarial scenarios under normal Python and `python -O`.

## Fresh-audit C1/C2 repairs

The audit-reopen defects were reproduced at
`1a3cb1cd6a78043256854f310fc078171703dd02` before repair:

- a nonexistent comparison root measured zero manifests and returned `PASS`/0
  in both normal and optimized Python by falling back from 3,760 active errors
  to the frozen 3,814 ceiling;
- a pre-seeded decision record with `status=PASS` survived a comparison
  worktree failure with exit 128 before the validator.

The repaired validator requires a resolvable comparison directory containing
at least one measured manifest and aborts with exit 2 plus an explicit
`comparison guard` first cause otherwise. When both trees exist, its ceiling
remains `min(frozen_allowed[key], comparison_allowed[key])`. The workflow now
invalidates the decision record as its first step, repeats that invalidation as
the guard runner's first effective action, and treats an absent artifact as an
upload error rather than a decision.

## Evidence and validation

The full diagnosis, environment, timings, hashes, age distribution, and all
before/after rule counts are frozen in:

- `docs/incidents/INCIDENT-RUN-MANIFEST-GLOBAL-GUARD-20260802.md`
- `docs/incidents/INCIDENT-RUN-MANIFEST-GLOBAL-GUARD-20260802.json`

Local targeted results:

- `tests/test_run_manifests.py`: 17 passed;
- normal adversarial harness: exact base PASS, malformed new REJECTED,
  missing/empty comparison REJECTED_BY_GUARD_CLAUSE, inherited worsening
  REJECTED, cross-manifest transfer REJECTED, repair PASS, deletion REJECTED,
  retitle REJECTED, repaired-debt reintroduction REJECTED, stale PASS
  INVALIDATED;
- `python -O`: identical decisions;
- pre-validator worktree failure: exit 128, decision record `ABSENT`, stale
  PASS not publishable;
- the broader `test` job now reaches its separate pre-existing result (695
  passed, 9 scientific/hash tests failed); those failures are not suppressed
  or modified by this PR;
- no Lean/Lake command was run.

## Guarantee boundary

This guard guarantees structural validity of new manifests, non-increasing
known structural debt, and continuity of frozen publication identity. It does
not certify mathematical truth, replay computations, validate semantic claim
scope, or prove recorded aggregates correct.

## Frozen text hash convention

The baseline's Git blob/LF and Windows checkout/CRLF SHA-256 values and exact
byte transformations are recorded separately in
`.github/run-manifest-debt-baseline.hashes.json`. The exact hashes of this
frozen PR body are recorded by the same two byte regimes in
`.github/PULL_REQUEST_BODY_RUN_MANIFEST_GUARD_20260802.sha256`: Git blob/LF is
the UTF-8 body with every CRLF pair replaced by LF; Windows checkout/CRLF is
derived by replacing every LF byte in that representation with CRLF. Neither
digest is called simply “the hash.”

Draft only. Please perform a fresh audit of the baseline, adversarial harness,
workflow result artifact, and guarantee boundary. Do not merge on this
author's self-assessment.
