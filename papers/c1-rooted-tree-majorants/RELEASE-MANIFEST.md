# C1 release manifest

## Revisions

| Object | Value |
|---|---|
| Lean integration commit | `4f95a5ad8154deef0ef38716073810072332fd37` |
| Manuscript (v6) commit | `a9a440fed54e9da8508689cabf2a9324e94f6fab` |
| Release tag | `c1-v1.0` -> `a9a440fe` (annotated; never moved) |
| Documentation patch tag | `c1-v1.0.1` (this commit: charter Amendments 4-6, build logs, dual-hash witness, this manifest) |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc6` |
| Mathlib pin | `07642720480157414db592fa85b626dafb71355b` (lakefile + manifest agree) |

## Canonical artifact hashes (SHA-256 of the git blob, LF)

| Artifact | Blob SHA-256 |
|---|---|
| `scripts/c1_admissibility_arb.py` | `F114FC4BCF2193C47603FB595B91B4E3EA62ADDC3A1BFEBE0AA0C147C447F1F9` (blob == disk) |
| `scripts/c1_admissibility_transcript.txt` | `46C6C1718B086BD1A2F3E1310B22EE9B749476C4D4B22298B0F3DBF5E3FD4C52` |
| `scripts/c1_admissibility_rerun_20260711.txt` | `46C6C1718B086BD1A2F3E1310B22EE9B749476C4D4B22298B0F3DBF5E3FD4C52` (byte-identical to transcript) |
| `scripts/c1_oracle_output.txt` | `BDB40F62482453D63F1B9BE3E667646CDEE3722F7AE6A93F2D313F2004ACEBFD` |
| `papers/c1-rooted-tree-majorants/c1_rooted_tree_majorants.pdf` (v6, at c1-v1.0) | `CED94765382977D1FD7C5575334F5C0BCCC448402CD178DAE388AA6767046951` |

Windows worktree (CRLF) representations of the transcript hash to
`0319DACA...B73B8F70`; see `scripts/c1_admissibility_rerun_20260711_COMPARISON_v2.txt`
for the dual-hash statement.  Compare against `git show <rev>:path`, not
worktree checkouts.

## Raw build logs (committed in c1-v1.0.1; previously excluded by the repo's `*.log` gitignore rule)

The green build was reached in three recorded runs; all three raw
transcripts are committed unmodified (renamed `.log` -> `.txt` only to
escape the ignore rule):

| Run | File | Outcome |
|---|---|---|
| 1 | `scripts/c1_lake_build_run1_FAIL_transcript.txt` | cold-cone build: 8241/8244 jobs green incl. `MarkedRootedClosure.PaperTheorems`; `NonVacuity` fails (decide maxRecDepth; missing Decidable instance; extra tactic bullet) |
| 2 | `scripts/c1_lake_build_run2_FAIL_transcript.txt` | `Finset.not_mem_singleton` absent in pin; gcongr closed via assumption leaving a dead `exact` |
| 3 | `scripts/c1_lake_build_run3_GREEN_transcript.txt` | `Build completed successfully (8244 jobs)`, exit 0 (SHA-256 `981AB56C1B469A1BC96428B166E28BDCD4057D03BD1ABE6C943B5FA32011EDB0`) |

Note on completeness: lake prints progress lines for executed/slow jobs
and a final job count; cached jobs do not each emit a line.  These are
the complete raw outputs as captured (`*> log` redirection); nothing
was reconstructed after the fact.

## Audit expedient

Charter (docs/C1-CHARTER.md): Amendments 1-3 are inside `c1-v1.0`;
Amendments 4 (release registry, five-role audit) and 5 (formal+repro
PASS 7/7) landed on `main` after the tag by sequencing necessity and
are inside `c1-v1.0.1`.  The tag `c1-v1.0` is the mathematical
artifact; `c1-v1.0.1` is the self-sufficient audit expedient.
