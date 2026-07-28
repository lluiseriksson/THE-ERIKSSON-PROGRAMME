# Run-manifest archive migration (preregistered 2026-07-29)

## Trigger

The first control-plane run on the merged Surface-Theorem `main` stopped at
`Validate committed run manifests`.  Measurement on a fresh HTTPS clone of
`471d2d9b` found:

- 623 JSON files under `run-manifests/`;
- 39 individually valid strict schema-v1 manifests;
- 584 individually invalid or pre-schema records;
- six of the 39 individually valid records whose supersession component
  intersects the invalid set;
- 2,162 committed `scripts/**(transcript|output)*.txt` artifacts, of which
  2,132 have no strict-manifest owner.

The directory mixed executable manifests with candidate ledgers, design
records, result summaries, and pre-schema inventories.  Treating all of them
as schema-v1 execution manifests created 3,950 validation errors.

## Frozen terminal criteria

This migration passes only if all of the following hold.

1. `run-manifests/` contains a nonempty, globally closed set accepted without
   error by `validate_run_manifests.py --require-nonempty`.
2. Every removed JSON is preserved byte-for-byte in `run-records/legacy/`.
3. `run-records/legacy-index.json` owns every archived JSON exactly once,
   records its raw and LF-normalized SHA-256, original location, original
   status/schema and the strict errors observed before migration.
4. No archived record is presented as an executable manifest.  A frozen
   record may participate in a mathematical/numerical claim only through an
   explicit domain validator that rechecks its referenced artifacts, hashes,
   partitions and acceptance predicates.  Generic manifest validation and
   changed-artifact coverage never consume it.
5. Every historical computational transcript/output lacking a strict owner is
   frozen by path, raw/LF size, raw SHA-256 and LF-normalized SHA-256 in
   `run-records/historical-artifact-baseline.json`.
6. The historical baseline is not read by
   `validate_changed_run_coverage.py`.  A new or modified computational
   artifact still requires a strict schema-v1 run manifest.
7. The v88 live-reference scan excludes only the explicit `run-records/`
   archive; superseded strings remain forbidden everywhere else in the live
   tree.
8. The archive checker, strict manifest checker, changed-artifact checker and
   their tests all pass from a fresh checkout.
9. Every live reader of a frozen record resolves it through the hash-bound
   archive index; moving records cannot silently disconnect or substitute
   evidence.

## Non-goals

- No timestamps, commands, dependency hashes or run environments are invented.
- No historical candidate is promoted to `current`.
- No current Surface-Theorem seal or manuscript artifact is changed.
- This migration does not claim that a frozen historical artifact is
  reproducible; it makes the absence of strict provenance explicit and
  immutable until a genuine rerun replaces it.

## Mechanical policy

`python scripts/run_record_archive.py bootstrap` performs the one-shot
classification and move.  `python scripts/run_record_archive.py check` is the
permanent CI gate.  Supersession components are archived as a unit: a
strict-valid record is moved too if its declared predecessor/successor would
otherwise leave the strict set.

## Terminal result

The migration completed with:

- 33 strict schema-v1 execution manifests;
- 590 byte-preserved frozen records (508 strict-invalid v1 records, 76
  pre-schema records, and six individually strict records moved to keep their
  supersession components closed);
- 2,139 frozen historical computational text artifacts after removing the
  outputs owned by the final strict survivor set;
- zero strict-manifest errors and zero archive-index/baseline errors;
- the finite Surface relay restored through hash-bound specialized readers:
  524 units seen, 504 admissible, exact `[20,1000/9]` union, 501 canonical
  owners, and the unchanged terminal fingerprint
  `86029ed96f88c53fd0fe18769e33577d4eee56aed553f36943dd490f09b7ae80`;
- `FINAL-SEAL PASS` with the sealed Surface TeX/PDF unchanged;
- all independent workflow gates green and `710 passed` in the full pytest
  suite.

No historical timestamps, commands, environments or dependency hashes were
reconstructed.  Old documentation links were mechanically redirected to the
frozen namespace; logical `run-manifests/<name>` identifiers remain only
inside the terminal fingerprint algorithm so the already published
content-binding fingerprint is preserved.
