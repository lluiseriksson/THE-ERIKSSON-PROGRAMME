# External re-verification of the repaired seal f7c54b62 (Claude desk, 2026-07-28)

## Confirmed on a fresh detached checkout of f7c54b62

- TeX/PDF LF-blob hashes EXACT: ebe57872... / e8cc61a1...
- `scripts/surface_remainder_delta0_moving_tail.py` now versioned (the
  provenance-vs-git omission is repaired).
- The 4 beta^3 factor is explicit in the covariance display (tex line
  ~1484); the editorial debts flagged in acta v90 are addressed.
- **`python scripts/audit_surface_final_seal.py` -> `FINAL-SEAL PASS`**
  on this desk's clean checkout. The 2026-07-28 portability defect is
  repaired: the seal now reproduces externally. The prior blocked
  verdict on 97a9a7f2 is superseded.

## One residual portability defect (same species, test layer)

`scripts/surface_bessel_gap_taylor.py` is NOT in the Git tree but is
imported at collection time by six tests of the superseded sharp
route (directly by `tests/test_surface_bessel_gap_dispatch.py`;
transitively via `scripts/surface_remainder_centered_delta_carrier.py`
by the k4/centered-delta/s1_delta8 test modules). Consequence on a
fresh checkout:

    python -m pytest -q   ->  "Interrupted: 6 errors during collection"

This is the exact command in `.github/workflows/control-plane.yml`
(step "Run control-plane tests"), so the "32 passed" clean-tree claim
does not reproduce here, and CI on a fresh runner would fail the same
way. The repair inventory covered the transcript ledgers' dependency
paths; the TEST layer's imports were outside its scope.

NO mathematical load: the final seal neither imports nor needs these
modules (verified; the seal passes without them), and the affected
tests belong to the quarantined sharp-positive route.

## Prescription

Either (a) version `surface_bessel_gap_taylor.py` (it presumably
exists on the sealing desk's shared worktree), or (b) quarantine the
six superseded-route tests (skip-if-missing or move out of
`testpaths`), then re-run the clean-tree suite and restate the test
count. One commit either way.

## Addendum: re-verification of 3596957b (post-repair, 2026-07-28)

CONFIRMED on this desk's clean checkout of 3596957b:
- TeX/PDF hashes UNCHANGED (ebe57872... / e8cc61a1...) - the repair
  did not touch the theorem or the paper.
- `surface_bessel_gap_taylor.py` versioned; the six collection
  errors are gone.
- **`FINAL-SEAL PASS` reproduced end-to-end again.**

NOT CONFIRMED: the claim "699 passed, 1 failed". This desk's fresh
run of `python -m pytest -q` on the published branch gives
**3 failed, 697 passed** (same total, 700). The two failures beyond
the declared manifest-coverage one:
- `test_project_state.py::test_repository_project_state_is_valid`
- `test_source_db.py::test_head_refs_prints_source_metadata_commit_anchors`

ROOT CAUSE (third instance of the species): the branch's own state
files reference commits OUTSIDE the published closure. Measured:
`project-state.json` records `lean_core.source_checkpoint =
0919aa10`, and the source-db metadata anchors include `1fed14e`;
`git merge-base --is-ancestor` shows NEITHER is an ancestor of the
codex branch HEAD - and 0919aa10 is not an ancestor of main either.
Both live on unpublished/unmerged branches. Any faithful clone of
the published refs fails these two tests; the sealing desk's local
repository evidently contains ancestry the published refs do not.
(First instance of the species: EOL-single-valued hash; second:
unversioned modules in provenance/test layers; third: state anchors
escaping the published branch.)

NO mathematical load: the FINAL-SEAL consults neither test. But
"claims-ready" requires the published refs to self-validate.
PRESCRIPTION: point the state anchors at commits reachable from the
branch (or publish/merge the referenced lane branches), rerun, and
restate the count from a faithful clone of the PUBLISHED refs -
not from the sealing desk's local repository.
