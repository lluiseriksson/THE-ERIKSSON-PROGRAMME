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

This PR chooses route B, differential quarantine. It also removes 320
Ubuntu-only path-separator/EOL false positives before freezing the remaining
3,814 strict violations: 39 manifests are strict-valid and 584 carry visible
inherited debt.

## Changes

- add a baseline keyed by protected publication path, run ID, official
  `claim_scope`/legacy `scope`, and exact violation multiset;
- pass when debt is unchanged or reduced, and fail on any invalid new manifest
  or increased existing violation;
- reject deletion or retitling of a protected publication;
- make repository path and LF/CRLF validation runner-independent;
- replace the misleading strict-red workflow step with
  `Guard run-manifest structure and historical-debt delta`;
- emit and upload a JSON decision record containing status, exit code, first
  cause, and recomputable class counts;
- run explicit adversarial scenarios under normal Python and `python -O`.

## Evidence and validation

The full diagnosis, environment, timings, hashes, age distribution, and all
before/after rule counts are frozen in:

- `docs/incidents/INCIDENT-RUN-MANIFEST-GLOBAL-GUARD-20260802.md`
- `docs/incidents/INCIDENT-RUN-MANIFEST-GLOBAL-GUARD-20260802.json`

Local targeted results:

- `tests/test_run_manifests.py`: 16 passed;
- normal adversarial harness: exact base PASS, malformed new REJECTED,
  inherited worsening REJECTED, repair PASS, deletion REJECTED, retitle
  REJECTED, stale PASS INVALIDATED;
- `python -O`: identical decisions;
- no Lean/Lake command was run.

## Guarantee boundary

This guard guarantees structural validity of new manifests, non-increasing
known structural debt, and continuity of frozen publication identity. It does
not certify mathematical truth, replay computations, validate semantic claim
scope, or prove recorded aggregates correct.

Draft only. Please perform a fresh audit of the baseline, adversarial harness,
workflow result artifact, and guarantee boundary. Do not merge on this
author's self-assessment.
