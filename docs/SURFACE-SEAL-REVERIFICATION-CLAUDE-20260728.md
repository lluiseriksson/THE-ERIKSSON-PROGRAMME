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
