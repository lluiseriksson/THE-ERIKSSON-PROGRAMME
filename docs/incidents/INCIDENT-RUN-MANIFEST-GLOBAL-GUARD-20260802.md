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
step. Its failed log has SHA-256
`99218ca81d34d30061406bf2240c72fd1406e04a80a8b6a0ea7b9ba1397c15e4`.

An independent Windows run of the exact command at the same SHA returned exit
1, 623 files and 3,950 errors in 8.866 seconds, using one Python process, no
pool, and 27.535 MiB peak RSS. The output had SHA-256
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
29.113 MiB peak RSS; its output SHA-256 is
`646d03015bd4adad0222809bc71bfa160d74dcc94fb29209f4fce20bd343c7a0`.
A WSL run over mounted NTFS was stopped after it exceeded 30 seconds; no later
global scan was run locally. Linux recomputation is delegated to the PR's
sanctioned GitHub Actions runner.

The sanctioned Ubuntu recomputation in PR run
[30751762660](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/30751762660)
matched the frozen aggregate exactly: 623 manifests, 584 with inherited debt,
and 3,814 strict errors. Its uploaded decision record reports `PASS`, exit code
0, no first cause, and every class count; the JSON artifact content has
SHA-256 `d27ff57051321d0ff03c00c4fe321e6b3766087abba3203ed97aa4ebcced478b`.
This agreement checks recomputability of the delta decision; it is not evidence
that any scientific aggregate is correct.

A second sanctioned run,
[30751963063](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/30751963063),
confirmed the case-normalized reduction to 3,760 errors with 584 invalid
manifests. Its decision JSON has SHA-256
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
- writes `RUNNING` before evaluation, then a JSON `PASS` or `FAIL` with exit
  code and first cause, so an old PASS cannot survive a failed run;
- uses explicit return codes and exceptions; no decision depends on `assert`.

The executable adversarial harness produces the same decisions under normal
Python and `python -O`: exact base PASS; new malformed REJECTED; inherited debt
increase REJECTED; debt reduction PASS; deletion REJECTED; official-title
replacement REJECTED; reintroduction of repaired debt REJECTED; stale PASS
INVALIDATED.

## Guarantee boundary

The guard guarantees structural validity for new manifests, non-increasing
known structural debt, and continuity of the frozen publication identity. It
does **not** certify mathematical truth, rerun computations, validate semantic
claim scope, prove that recorded aggregates are correct, or repair historical
provenance. A green job is only the delta decision; the baseline and emitted
class counts are the recomputable evidence for that decision.
