# C5 release manifest — c5-v1.0

STATUS: CLOSED at the release commit (the commit carrying this
revision of the manifest, marked by the annotated tag `c5-v1.0`).
All former `[RELEASE-SLOT]`s are filled below; the authoritative
clean-clone release check is GREEN (run 3, transcript committed at
`scripts/c5_release_check_transcript_run3_GREEN.txt`; runs 1–2
failed on registered environment defects — PowerShell ANSI parse,
Windows long-path in lake's mathlib clone — kept with diagnoses,
never deleted).

## Revisions (ids recorded from POST-PUSH git log)

| Object | Value |
|---|---|
| Charter commit (pre-registration, before the page) | `6ecac68b` |
| Amendment 1 (THE PIVOT: RS16 equivalence, crossing target) | `b3da2464` |
| Amendment 2 (per-(nu,c) witnesses, two uniqueness routes) | `f5e872ef` |
| Phase 1, J-C5-1 (BFamily + trichotomy + sufficiency GREEN) | `2c1462b5` |
| Phase 2, J-C5-2 (L by recurrence-inversion + witness GREEN) | `a2a88467` |
| Amendment 3 (phase-3 assault plan, own commit) | `81753200` |
| Phase 3 block A (sandwich) GREEN | `de38eff0` |
| Amendment 4 (PROVENANCE CORRECTION: Turan is classical) | `38df3f90` |
| Block A' (besselIReal_turan named endpoint) GREEN | `2a6ddbe6` |
| Block B (existence window) GREEN | `f1151d44` |
| Blocks C-D-E (threshold, uniqueness, orientation, scale) GREEN | `fce2c323` |
| Amendment 5 (7.32 verdict + naming correction + 3F registered) | `2439fd7c` |
| Amendment 6 (the exact D'' identity, pre-3F, own commit) | `a745be4f` |
| Phase 3F (tangency exclusion, GLOBAL theorem) GREEN — **final mathematics commit** | `f1c87fef5f21fa5623099b7306851e047fb121d3` |
| Amendment 7 (7.58 verdict + THE DIRECTED COLLATION) | `7e1b524c` |
| Amendment 8 (J-C5-4 companion protocol, PRE-RUN, own commit) | `f6ec64ea` |
| Amendment 8 technical note (anchor deviation, PRE-RUN) | `fdb0fe60` |
| Technical note item 4 (depth correction, PRE-RUN) | `ae60ff74` |
| J-C5-4 GREEN (certified run 30/30, script + transcript) | `90818f33` |
| Paper draft v1 (tex+pdf same commit, 10 pp) | `7a97e7ad` |
| Paper v1.1 (independence micropatch, the only draft-audit finding) | `61b1bb330eaf7027bf9500cbc5c0599a3b601c6b` |
| Paper v1.2 + five-role audit resolution (six actas: 0 findings survive unfixed; see AUDIT-RESOLUTION.md) | `99144dd8` |
| Release-check script v2, v3 (pre-run corrections, own commits, measured failures diagnosed) | `0dee72a4`, `4bce8a7f` |
| Amendment 9 (external absolute-scale verdict 5.90 + FIRST EXTERNAL REPRODUCTION of the companion, 30/30 on Python 3.13.5) | `36e7425d` |
| Authoritative clean-clone release check GREEN (run 3 at `4bce8a7f`: 8175 jobs, oracle 110/110, companion 30/30, tectonic, all four hashes match; transcript blob sha256 `D115F2ED...`, see hash table) | transcript in the release commit `d80acd4d` |
| Amendment 10 (external release verification, 6.00 absolute; transcript-hash provenance fix = this revision of the manifest) | post-tag patch |
| Release commit (this manifest, slots closed) | THIS COMMIT — tag `c5-v1.0` (ANNOTATED; tags never move) |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc6` |
| Mathlib pin | `07642720480157414db592fa85b626dafb71355b` (lakefile + manifest agree) |
| tectonic / python-flint | `0.15.0` / `0.9.0` |

## Recorded build facts (at `f1c87fef`, mathematics final)

- `lake build AmosClosure`: GREEN, **8175 jobs**
  (`scripts/c5_lake_build_run7_GREEN_transcript.txt`).
- Axiom oracle: **110 registered statements** (74 inherited from the
  `c4-v1.0` registry + 36 new of this paper), every one printing
  exactly `[propext, Classical.choice, Quot.sound]`
  (`scripts/c5_oracle_output_phase3f.txt`).
- Certified companion (at `90818f33`): 30/30 pairs PASS all four
  certificates at ladder rung 1 (prec 128); 0 UNDECIDED, 0 FAIL;
  independent mpmath pass agrees 30/30 (VERIFIED label).

## Canonical artifact hashes (SHA-256; LF = git blob representation)

CANONICAL: the release commit ships exactly the v1.2 blobs, and the
authoritative clean-clone check (run 3) re-derived all four hashes
from `git show HEAD:` — they match this table.  (v1.1 values,
superseded: tex `1FD2A8FD...`, pdf `69DC6F40...`.)

| Artifact | SHA-256 |
|---|---|
| `papers/c5-crossing/c5_crossing.tex` (v1.2, LF blob) | `502D9C1CCA93421DF764ACEDB9EAF07E0CCBCFCAFB8631F51349354DDC018A08` |
| `papers/c5-crossing/c5_crossing.pdf` (v1.2, binary, 10 pp) | `4E8C564FC8620FC69661BD861B1A4A7FD07361E4C8A95A2768A9611412600374` |
| `scripts/c5_crossing_arb.py` (certified companion) | `3F31FF76D30BC63222FB6D7E284AE744891A5C9FDFA10AC1EADDEE0C2FA43C67` |
| `scripts/c5_crossing_arb_transcript.txt` (30/30, authoritative) | `E2A2F33A431D86B5C0595A7AB971F0A2B24D766F099C3C464B78EA124E6C1C8B` |
| Release-revision tex (final = v1.2, unchanged through release) | `502D9C1C...` (row above) |
| Release-revision pdf (final = v1.2, unchanged through release) | `4E8C564F...` (row above) |
| `scripts/c5_release_check_transcript_run3_GREEN.txt` (git-blob/LF, the canonical form per the EOL rule) | `D115F2EDA9719C18CB5080DA93F7A3D1A79A0C776BA5059DC6873C6215369233` |
| same file, Windows worktree/CRLF bytes as produced by the PowerShell run (provenance note; post-tag correction per Amendment 10 — the tag-time row carried only this value, mislabeled) | `87D2891990EBD5D53A25EF26E7739772ED7C7C7D512C27E483F83FFC3ABB1BC9` |

EOL note (standing, C4 precedent): git normalizes CRLF->LF at blob
formation; compare against `git show <rev>:path`, never a worktree
checkout.

## Reproduction (from a clean clone at the release revision)

```
lake exe cache get
lake build AmosClosure            # expect GREEN, 8175 jobs
lake env lean AmosClosure/Oracle.lean   # expect 110 x [propext, Classical.choice, Quot.sound]
python scripts/c5_crossing_arb.py       # expect 30/30 PASS, 0 UNDECIDED, 0 FAIL (prec 128)
tectonic -X compile papers/c5-crossing/c5_crossing.tex
```

The authoritative pre-tag check sequence is scripted in
`scripts/c5_release_check.ps1`; its transcript is committed with the
release commit.

## Theorem-to-artifact map

The full map is the table of the paper's Reproducibility section
(module `AmosClosure`; files `AmosFamily.lean`, `AmosLowerReal.lean`,
`AmosCrossing.lean`, `AmosTangency.lean`; headline names
`amosFamily_uniform_upper_iff`, `amosFamily_lower_of_one_le`,
`amosFamily_global_crossing`, `amosFamily_crossing_orientation`,
`crossing_no_critical_contact`, `crossing_scale`,
`besselIReal_turan`).  The 74 inherited statements are mapped in the
C2/C3/C4 release manifests.

## Audit expedient

Fabrication-side desks (math referee, hostile editor,
checklist/formal-hygiene) + formal+repro desk + external-tool desk:
the five actas and their dispositions are recorded in
`papers/c5-crossing/AUDIT-RESOLUTION.md`, with charter registration
in `docs/C5-CHARTER.md`.  A bibliography desk (web verification of
all external entries) is recorded in the same resolution table.
Method-deviation disclosures carried by this manifest (X-desk
findings): the companion's bisection midpoints are outward-rounded
BALLS, not the registered exact dyadics (strictly conservative;
disclosed in the paper v1.2 companion section); the in-script
mpmath VERIFIED pass checks box-end signs + finite-difference D'
rather than the registered float-bisection-plus-containment (the
registered form was executed independently at the external-tool
desk, 4/4 including the heavy row, on the acta record); the
protocol-commit set is f6ec64ea + fdb0fe60 + ae60ff74 (the third
carries the implemented depth formula; all three PRE-RUN ancestors
of 90818f33, timing verified).
Release-tree re-audit is post-tag by sequencing; fixes, if any, in
post-tag commits — tags never move (C2/C3/C4 pattern).

## Owner release order

Companion viXra identifiers for C2 (`c2-v1.2.1`), C3 (`c3-v1.0.1`),
C4 (`c4-v1.0`) were not yet assigned at drafting time; per the C4
Amendment-9 precedent the bibliography cites "identifier pending at
the time of this release" and the ids land in a post-tag patch
(`c5-v1.0.x`).  The release click itself is the owner's; this
manifest only stages it.
