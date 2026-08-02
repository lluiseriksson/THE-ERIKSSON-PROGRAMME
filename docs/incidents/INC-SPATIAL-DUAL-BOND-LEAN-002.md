# INC-SPATIAL-DUAL-BOND-LEAN-002 — archived transcript precedes the final verdict

Date: 2026-08-01

Campaign: task 14, exact local dual-bond identity

Lean source SHA under test: `85847dd19623c692b8345cee864be7837f5c7656`

Preregistered runner SHA: `d41fa43a78370bf93cdc181a9f8d9d0d89ba080b`

## VERIFIED FAILURE OF ARTIFACT ORDERING

The fresh high-memory Colab rerun completed the mathematical and repository
checks successfully.  The visible cell output reported:

```text
Build completed successfully (8172 jobs).       # SpatialDualBond
Build completed successfully (8466 jobs).       # YangMillsCore
lake env lean oracle_check.lean                  # exit 0
python3 scripts/check_consistency.py              # exit 0
artifact_zip_sha256=2a997167334fcb6763c188081cf1d6b02dff3fb3a9e345a2678f5b116fabe48c
SPATIAL DUAL-BOND LEAN PASS
```

The downloaded ZIP matched the announced SHA-256.  Its internal files also
matched `SHA256SUMS`:

```text
f57f9bcdf25acdb74f5c1662d4e2e257a5259e35d5fd51f3e8e5f72512013867  metadata.json
4b82dbdb700fd42242fa7e7905759843913be1a2afd4642d2032da6dbb7898ef  oracle_output.txt
949a750e42ebb38223a446690e368809c8832808b61029554dba3e757059af16  transcript.txt
```

Desktop inspection confirmed that the four decisive commands in the archived
transcript each have exit 0.  It also confirmed that the three new declarations
have exactly `[propext, Classical.choice, Quot.sound]` in `oracle_output.txt`.

However, the notebook called `shutil.make_archive` before these calls:

```python
log(f'jobs_measured={jobs}')
log(f'artifact_zip={archive}')
log(f'artifact_zip_sha256=...')
log('SPATIAL DUAL-BOND LEAN PASS')
```

Consequently the archived `transcript.txt` does not contain `jobs_measured` or
the final PASS, even though both occur in the visible cell output.  The run is
positive evidence for the Lean theorem, but the ZIP is not the self-contained
transcript required by this campaign.

## Repair

The runner must log the measured job count and final PASS before hashing the
artifact directory and creating the ZIP.  The archive path and archive hash may
remain external output because including an archive's own hash inside itself is
impossible.  The repaired runner must be committed before it is executed, and
the full campaign must be rerun.

