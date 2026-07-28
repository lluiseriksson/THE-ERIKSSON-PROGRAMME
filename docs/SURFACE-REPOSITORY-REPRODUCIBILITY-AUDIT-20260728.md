# Surface repository reproducibility audit (2026-07-28)

## Scope

This record separates the terminal mathematical seal from the integration
state of the full repository.  It follows the external clean-checkout audit of
`f7c54b62` in `SURFACE-SEAL-REVERIFICATION-CLAUDE-20260728.md`.

## Confirmed terminal state

The weak-main Surface-Theorem path is independent of the historical sharp
K2/K4/S1'''/S2''' lane.  On a detached checkout, the final audit reaches

```text
FINAL-SEAL PASS: terminal gates, manuscript, and PDF are present
```

The TeX and PDF remain the 33-page artifacts frozen at `f7c54b62`; this
test-layer repair does not edit or rebuild either artifact.

## Test-layer repair

The audit reproduced six collection errors caused by the unversioned
`scripts/surface_bessel_gap_taylor.py`.  The module is now versioned rather
than hiding the tests.  Its own rigorous smoke check passes.

Collection then exposed historical assumptions that predated the corrected
full-moment normalization:

- the committed supersession inventory is 21 affected manifests, 11 still
  marked current; the local `hybrid009` manifest was never versioned and its
  stale hashes cannot be promoted post hoc;
- the corrected order-five companion sufficient bound is
  `2.201391366...` times the registered budget, so the test is now a rigorous
  negative result rather than a false positive;
- the historical grid-96 late-edge endpoint box is unresolved after the
  normalization repair;
- the K4 lower-prefix archive contains five byte-identical candidate
  production/replay pairs and lacks the final `k4_0030` pair; all are
  explicitly non-terminal;
- historical endpoint/K4 transcripts whose source dependencies changed are
  required to be rejected, while genuinely unchanged LF/CRLF forms are
  accepted through `surface_eol_hashes.sha256_variants`.

## Full-repository blockers outside the terminal seal

The branch is not integration-green and must not be described as such:

- PR #31 differs from `main` by 6,047 files and 1,338,152 insertions;
- `test_changed_run_coverage.py` reports 2,015 changed computational
  artifacts without a covering run-manifest;
- `validate_run_manifests.py --require-nonempty` reports 624 invalid legacy
  manifest files and 4,113 errors.

These are repository-governance debts, not failures of the terminal weak-main
mathematics.  They require a separate, preregistered archive/manifest
sanitation effort.  No test, budget, hash, or workflow guard is weakened here
to manufacture a green CI result.

## Exact status

- terminal weak-main seal: `PASS`;
- claim audit of the frozen paper: `READY_FOR_CLAIM_AUDIT`;
- full repository / PR #31 integration: `BLOCKED`;
- merge to `main`: not performed;
- submission: owner action, not performed by this repair.
