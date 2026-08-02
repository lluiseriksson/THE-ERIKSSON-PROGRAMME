# Scientific pytest triage — 2026-08-02

## Scope and frozen measurement

This triage reuses, without rerunning, the six-ref measurement frozen in
`audit/SCIENTIFIC-TEST-DEBT-SIX-REF-MEASUREMENT-20260802.md`.  All six runs
returned the same ordered nine failing nodeids, phases, and first-cause
fingerprints.  This report changes their nominal classification; it does not
change the measured observations.

The classification rule is dependency-closed:

1. **A — vestigial** applies only when the tested route is not consumed by a
   current live repository contract.
2. **B — irreparable / evidence lost** applies when the test's pass predicate
   directly or transitively consumes the manifest archive whose inputs task
   (34) proved unavailable in every published reachable history.
3. **C — real repairable debt** applies when the obligation remains live and
   every input needed by its pass predicate exists.

Under that rule the measured partition is **A=0, B=4, C=5**.  The earlier
uniform nine-item debt ceiling is invalid.

## Nine-row nominal classification

| Nodeid | Frozen first cause | Document / input scope | Class | Evidence | Disposition |
|---|---|---|---|---|---|
| `tests/test_surface_bulk_3_6.py::test_canonical_surface_bulk_3_6_transcript` | `AssertionError: worktree script hash mismatch` | `scripts/validate_surface_bulk_3_6.py`; `certify_bulk_arb.py`; committed `[3,6]` transcript and source commit | **C** | Script, transcript, and recorded Git blob exist.  The validator applies a raw-byte check before its already present LF-normalized check.  `audit_surface_terminal_prerequisites` consumes this certificate and G6 names the prerequisite reconstruction as terminal evidence. | Keep the test.  Put only this repairable fingerprint under the C ratchet. |
| `tests/test_surface_final_seal.py::test_surface_final_seal` | `AssertionError: assert ['terminal pr...dit failed: '] == []` | Closure board, `surface-complete` TeX/PDF/build manifest, terminal prerequisites, G2 weak terminal cover, and closed-form anchors | **B** | Its immediate failure is the repairable `[3,6]` prerequisite, but its complete PASS predicate later calls `audit_surface_g2_weak_terminal_cover`, which calls finite-role and the evidence-lost G2 archive.  A release seal cannot be classified C while one of its mandatory predicates is B. | Keep visible as an evidence-loss exception pending owner decision E.  Do not call it debt or claim the seal is scientifically green. |
| `tests/test_surface_finite_role_relay.py::test_finite_role_relay_is_complete_and_logically_bound` | `AssertionError: assert 'NONE' == 'FINITE_ROLE_PROVED'` | `audit_surface_finite_role_relay.py`; finite G2 archive; direct Wronskian sign implication; `surface-complete` Theorem A | **B** | `audit_role()` directly calls `G2.audit_summary()`.  The promotion document says the historical **H_tail relay** is unused, but immediately replaces it with the direct Wronskian cover; the closure board still names that finite cover as terminal G2 evidence.  Therefore this nodeid is not A.  Its direct archive dependency is B. | Keep visible as B pending E; do not retire a currently load-bearing direct-cover predicate. |
| `tests/test_surface_g2_relay_admissibility.py::test_terminal_promotion_is_bound_to_the_frozen_ownership_fingerprint` | `AssertionError: assert 'NONE' == 'FINITE_BULK_SIGN_CERTIFIED'` | `audit_surface_g2_relay_admissibility.py`; `surface-scaled-bulk-*.json`; production/replay ownership fingerprint | **B** | Root evidence-loss case.  Task (34) rederived 679 missing references in 315 `surface-scaled-bulk-cwin3p2*` manifests, collapsing to 31 missing identities.  Across 243 published refs/tags, 6,442 reachable commits and 24,431 blobs, it found zero path, basename, or declared-digest match.  The outputs exist, but the archive's input reproducibility cannot be reconstructed. | Declare the loss and link it to owner decision E: quarantine/reclassification or withdrawal of the reproducibility assertion. |
| `tests/test_surface_g2_terminal_cover.py::test_surface_g2_terminal_domain_cover` | `AssertionError` | `audit_surface_g2_weak_terminal_cover.py`; finite-role audit plus high-beta weak-main lanes | **B** | `audit()` calls `finite_role.audit_role()` and requires `FINITE_ROLE_PROVED` before the high-beta lanes.  It is therefore transitively dependent on the B archive.  The closure board makes this composition live (`G2_WEAK_TERMINAL_COVER_PROVED`), so it is not A. | Keep visible as B pending E.  Do not count it in repairable debt. |
| `tests/test_surface_high_beta_lambda3_joint_validator.py::test_committed_lambda3_joint_pair` | `AssertionError: unexpected transcript digest` | Lambda-three production/replay pair and the recorded certificate dependency ledger | **C** | Production, replay, validator, certificate and every recorded dependency path exist.  The validator reaches a stale expected transcript digest before checking the live rho/adverse/margin obligations.  G2's live high-beta composition consumes this certificate. | Keep and ratchet as repairable C. |
| `tests/test_surface_high_beta_lambda3_weak_relay_inputs.py::test_lambda3_transcript_implies_tighter_weak_relay_bounds` | `AssertionError: unexpected lambda-three digest: 64cb5cb855fc3ddf90ea4efd06567c677cb4f880aaa5ca2d53eb70683387eb36` | Same lambda-three pair, dependency hashes, and the tighter `rho<7/200`, `adverse<43/50` weak-relay thresholds | **C** | All inputs exist and the first cause is a stale expected digest, not a missing artifact.  The weak G2 terminal composition consumes these bounds. | Keep and ratchet as repairable C. |
| `tests/test_surface_terminal_prerequisites.py::test_terminal_prerequisites_are_rebuilt_from_evidence` | `AssertionError` | v88 sanitation, optional-Hcube removal, two Theorem-B witnesses, bulk `[3,6]`, `[6,15]`, `[15,20]`, left-edge and right-edge transcripts | **C** | Every direct module and transcript exists.  The current exception comes from the repairable `[3,6]` raw-hash check.  G6 explicitly names terminal-prerequisite reconstruction as live evidence. | Keep and ratchet as repairable C. |
| `tests/test_validate_surface_remainder_delta0_sixth_coefficient_transcript.py::test_authoritative_sixth_head_transcript_validates` | `AssertionError: assert 'ee5fb3edfda1...4675a87cf5556' == '27725eaac35f...6681d1eeeec9c'` | `surface-remainder-delta0-sixth-head-20260712T143105Z.json`; sixth-head script, coefficientwise dependency, and transcript | **C** | The suggested B classification does not reproduce.  This manifest is not one of task (34)'s four affected remainder manifests: its script, dependency and output all exist with recorded hashes.  The test asserts a CRLF raw digest against an LF checkout even though the following assertion already checks the correct LF digest.  The exact-head research record remains referenced by `surface-complete`, while explicitly carrying no terminal relay load. | Keep as a live, repairable research-evidence obligation and ratchet as C.  Do not imply that it bears on the submitted paper. |

## Why class A is empty

The quoted sentence in
`docs/SURFACE-FINITE-BULK-TERMINAL-PROMOTION-20260728.md` distinguishes two
routes.  The historical manifest promotion depended on the unproved
`(H_tail)` extraction relay and is not used.  The next sentence states that
the terminal proof instead uses the exact identity `W = 4 F_B^2 E'` and the
strict-sign archive directly.  The same document's reproduction section
names the G2-admissibility and finite-role tests, while the current closure
board names the finite Arb cover and weak G2 union as G2/G6 evidence.

Consequently, deleting those nodeids as vestigial would remove a predicate
that the current repository still declares load-bearing.  No other failing
nodeid tests a demonstrably dead route.  No A path is removed in this change.

## Evidence-loss boundary from task (34)

The accepted read-only forensic result was made at published main
`ad2d645feeab1942a0d401b15017896e06e28dcb`.  Its final published-ref snapshot
had SHA-256
`bdbcb0e3346f57ed291208358f28bb5ccf411203e9d99e1614d22ef49ec78c8d`.
It found:

- 315 affected scaled-bulk manifests, 679 references, 31 missing normalized
  identities;
- four affected remainder manifests, nine references, six missing normalized
  identities;
- zero exact paths, basenames, SHA-256, or SHA256-LF identities in published
  reachable history;
- committed production/replay outputs and separate canonical Arb certificates,
  which preserve their own mathematical load but do not restore missing input
  reproducibility.

This triage does not rerun that 2.51-GB forensic scan and does not decide E.

## Submitted Surface paper boundary

The submitted Surface paper is
`papers/surface-theorem/surface_theorem.tex` (the title recorded in its
submission package).  Exact case-insensitive searches returned zero matches
for every document basename, validator basename, and promoted verdict used by
the nine-row table, including `FINITE_BULK_SIGN_CERTIFIED`,
`FINITE_ROLE_PROVED`, `G2_WEAK_TERMINAL_COVER_PROVED`,
`TERMINAL_PREREQUISITES_PROVED`, the lambda-three transcript names, and the
sixth-head name.  The submitted paper is not implicated.

The distinct `papers/surface-complete` working manuscript does mention the
sixth-head basename and its submission package names `audit_surface_final_seal`.
That distinction is why this report does not make the broader and false claim
that no file under `papers/**` mentions any auxiliary artifact.

## Control predicate after triage

The replacement check is named:

`Scientific pytest triage: repairable-debt ratchet (5) + declared evidence-loss set (4)`

It may pass only when:

- every active failure is either an exact B fingerprint or an exact active C
  fingerprint from the comparison head;
- no new nodeid, changed phase/cause, collection error, timeout, or missing
  classified execution exists;
- a repaired C item is reported as an improvement and a later reintroduction
  against the previous head fails;
- B remains visibly separated and linked to E, never labelled debt;
- missing/corrupt classification, unresolved refs, or stale decision output
  fails closed.

This predicate does not certify any scientific claim, restore lost evidence,
or decide owner decision E.
