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

## Clean-checkout result after the repair

On repair commit `39472d4e4499442b405249960a55704c07f39384`, the literal
workflow test command completed as

```text
python -m pytest -q
1 failed, 699 passed in 519.15s
```

The sole failure is
`test_repository_branch_has_no_uncovered_changed_artifacts`, with exactly
2,015 uncovered changed artifacts.  All other tests pass.  On the same
checkout,

```text
python scripts/audit_surface_final_seal.py
FINAL-SEAL PASS: terminal gates, manuscript, and PDF are present
```

## Exact status

- terminal weak-main seal: `PASS`;
- claim audit of the frozen paper: `READY_FOR_CLAIM_AUDIT`;
- full repository / PR #31 integration before merge: one deliberate
  changed-artifact coverage failure remained;
- merge to `main`: explicitly authorized by the owner after the terminal
  mathematical seal and the public-clone checks;
- submission package: `papers/surface-complete/SUBMISSION-INFO.txt`.

## Public-closure recheck

An external desk subsequently reported two additional failures because it
classified source anchors `0919aa10` and `1fed14e` as outside the published
ancestry.  Before changing either anchor, a new full HTTPS clone was made with
`git clone --no-local` and the public Surface branch was checked out detached.
On that clone both literal commands

```text
git merge-base --is-ancestor 0919aa10 HEAD
git merge-base --is-ancestor 1fed14e HEAD
```

returned exit code zero, and the two allegedly failing tests completed as
`2 passed`.  The recorded anchors are therefore in the public commit closure
and were not rewritten.  The likely failure mode of the contrary audit is an
incomplete or stale object/ref view; this diagnosis does not alter its valid
earlier catches of EOL-sensitive hashes and unversioned dependencies.
