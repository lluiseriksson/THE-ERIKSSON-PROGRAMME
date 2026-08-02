# Owner decision: quarantine manifests with unrecoverable evidence references

- **Decision date:** 2026-08-02
- **Owner:** Lluis Eriksson
- **Decision:** `E_DECIDED: quarantine`
- **Scope:** run-manifest lifecycle state only

## Context and measured boundary

The accepted forensic sweep found 319 run manifests whose declared
`script.path` or `inputs[*].path` evidence is absent from every inspected
published reachable history and from the inspected disk. Those manifests carry
688 missing references: 315 manifests and 679 references in the
`surface-scaled-bulk-cwin3p2` family, plus four manifests and nine references in
the `surface-remainder` family. The prior sweep found 31 distinct material
files absent from all reachable history and from the inspected disk. This
decision does not rerun or enlarge that forensic search.

The exact 319-file result inventory is
`docs/decisions/QUARANTINED-RUN-MANIFESTS-20260802.txt`. It is a transparent
output of the measurable selector, not an input to the migration.

All 688 `path: file does not exist` facts remain true after this migration and
remain countable by the run-manifest guard. Quarantine is a lifecycle
reclassification, not a material repair, a reduction of evidence debt, or a
claim that reproducibility has been restored. The 810 existing recursively
declared `outputs[*].path` references in the affected population are outside
scope and remain untouched.

## Alternatives considered

1. **Quarantine/reclassification.** Mark every affected manifest
   `status: quarantined`, retain a mandatory reason, and keep the original
   references and digests.
2. **Withdraw the reproducibility assertion.** Remove the affected assertion
   from the live evidence layer because it cannot be fulfilled with the
   available material.

The owner chose quarantine. It states explicitly that the manifests cannot
currently fulfil their declared reproducibility role without erasing the
historical assertion. More importantly, the missing paths and recorded digests
remain intact as recovery keys: an object later found in a backup can be
authenticated against the original record. Withdrawal by deletion would
destroy that recovery index and make the decision less reversible.

## Effect on PR #56 class B

The four class-B tests recorded by PR #56 move from `E_UNDECIDED` to
`E_DECIDED: quarantine`:

- `tests/test_surface_final_seal.py::test_surface_final_seal`
- `tests/test_surface_finite_role_relay.py::test_finite_role_relay_is_complete_and_logically_bound`
- `tests/test_surface_g2_relay_admissibility.py::test_terminal_promotion_is_bound_to_the_frozen_ownership_fingerprint`
- `tests/test_surface_g2_terminal_cover.py::test_surface_g2_terminal_domain_cover`

They stay red and visible. They are evidence-loss exceptions, not repairable
debt, and this decision does not retire, weaken, edit, or mark any test as
passing. PR #56 is not modified here; this record is the target a later update
may link.

## Preserved recovery keys

The migration may change only the top-level `status` and
`quarantine_reason`. Every declared path and every recorded digest is preserved
byte for byte as a JSON string value. Existing quarantine reasons are retained
verbatim inside the new owner-decision reason. Existing output references are
neither selected nor rewritten.

## Exact reversal conditions

A manifest may leave this evidence-loss quarantine only when all of the
following are recorded and independently reviewable:

1. Every missing `script.path` and `inputs[*].path` object for that manifest is
   recovered from an identified source and committed at the exact
   repository-relative path and case preserved in the manifest.
2. The recovered bytes match the preserved `sha256`; where `sha256_lf` is
   present, the repository's defined LF-normalized check also matches. A
   mismatch is a rejected recovery, not permission to edit the recorded
   digest.
3. No declared script/input reference in that manifest remains absent; partial
   recovery does not restore `current` status.
4. The strict manifest validator and the differential guard from PR #51 both
   pass against the exact publication base without suppressing or rebaselining
   a violation.
5. A fresh reviewer verifies the source, byte identities, complete-reference
   condition, and guard result, and the owner records authorization to remove
   this quarantine reason.
6. Any independent pre-existing quarantine or candidate-only condition is
   discharged on its own evidence. Recovery alone is not scientific promotion.

Only after all six conditions may an otherwise live manifest return to
`status: current` with `quarantine_reason: null`. If an independent quarantine
still applies, the manifest remains quarantined with that reason. The Git
history of this decision and the pre-migration state is part of the reversal
record.
