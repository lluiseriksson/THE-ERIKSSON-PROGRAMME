# Run-manifest control-plane backlog — 2026-07-31

## Observed state

The `Validate repository control plane` job on draft PR #39 executed

```text
python scripts/validate_run_manifests.py --require-nonempty
```

and reported:

```text
run manifest validation failed: 623 file(s), 4134 error(s)
```

PR #39 changes no manifest and does not change the validator.  Its edit to
`HYPOTHESIS_FRONTIER.md` is sufficient to trigger the path-filtered workflow,
exposing the pre-existing inventory to the current validator.

## Why this is a separate blocker

This red check is not evidence against the mathematics of PR #39.  It is also
not harmless: while the unchanged historical inventory fails, every qualifying
PR receives the same red signal.  A genuinely new control-plane regression is
then difficult to distinguish from the baseline backlog.

## Repair contract

The repair must preserve the validator's semantic strength.  Acceptable routes
include a reviewed migration of historical manifests or an explicit,
versioned quarantine/baseline whose scope shrinks monotonically.  Disabling the
job, accepting every legacy shape, or changing failure into success without a
machine-readable debt ledger would manufacture a green and is not acceptable.

This document records the blocker only.  It does not choose or implement the
migration and does not relabel any invalid manifest as valid.
