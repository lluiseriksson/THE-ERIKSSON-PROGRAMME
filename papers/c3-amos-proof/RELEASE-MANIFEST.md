# C3 release manifest

## Revisions

| Object | Value |
|---|---|
| Charter commit (pre-registration) | `77fe704c` |
| Riccati phase, J-C3-1 (run 1 GREEN, 8164 jobs) | `19504635` |
| Zone phase 2a exhausted (runs 2-4 FAIL + Amendment 1, same commit) | `70499e22` |
| Zone phase 2a' GREEN (runs 5 FAIL / 6 GREEN, 8165 jobs) | `c05dfc36` |
| Barrier + 28-entry oracle, J-C3-2 (runs 7 FAIL / 8 GREEN, 8166 jobs) | `538562dcdc06a1d6c6ea2522ba57f991c5bdd847` |
| Manuscript v1 | `3984d0b3` |
| Manuscript v1.1 (overfull sweep) | `dabef64c` |
| Release commit (manuscript v1.2 + this manifest + 34-entry oracle) | tag `c3-v1.0` (this commit; tags never move) |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc6` |
| Mathlib pin | `07642720480157414db592fa85b626dafb71355b` (lakefile + manifest agree) |

Commit ids other than the tagged one are recorded post-push from
`git log` on main (the C2 Amendment-4 lesson: pre-rebase ids can be
orphaned by concurrent dashboard-bot commits).

## Canonical artifact hashes (SHA-256; LF = git blob representation)

| Artifact | LF blob | CRLF worktree (where distinct) |
|---|---|---|
| `papers/c3-amos-proof/c3_amos_proof.tex` (v1.2) | `8559877B4C78609B524E02624F292B0398A6E0C16C392DCDDD873143B92C90C1` | `1005CFC67503E951122D1156F8D469731D7B515E53E0CB8F28DBC2606139CF29` |
| `papers/c3-amos-proof/c3_amos_proof.pdf` (v1.2) | `5E49EBCAD5DEFC41B7CE8F9467C6B037C032FA4406B18CB50727D1A5ADCF8369` (binary, no EOL) | — |
| `scripts/c3_oracle_output.txt` (28-entry, at `538562dc`) | `50D848E83B94C7712A4F5B2C54B4FA3C77606E6D4F49351B74BBA33865EBE7D1` | `ACCB569C4198347CEA6321888EB6A016FDB200E648B1AF54B46E9EC2F7C92F01` |
| `scripts/c3_oracle_output_v2.txt` (34-entry, release revision) | `90B757A7AB233D7C28905330572B6BEF01B75B404074E05D5A833BF0EA194978` (LF bytes on disk) | — |
| `scripts/c3_lake_build_run9_GREEN_transcript.txt` | `33F54A06609D5C1F677E7D27BF7DCC57086B88F40A7149033ABA356E0254858C` (LF bytes on disk) | — |

EOL note (standing, from the C1 arc): git normalizes CRLF->LF at
blob formation; `core.autocrlf` checkouts materialize CRLF worktree
copies.  "Committed unmodified" means content not reconstructed, not
binary identity across EOL normalization.  Compare against
`git show <rev>:path`, never a worktree checkout.

## Oracle registry note (34 = 28 + 6)

The headline registry at `538562dc` prints 28 statements (the
eighteen inherited from the C2 layer plus the ten new headline
statements), all `[propext, Classical.choice, Quot.sound]`.  At the
release revision the registry was extended by the six supporting
lemmas named in the paper's artifact map
(`besselTerm_le_geometric`, `besselI_mul_le`,
`besselTerm_zero_lt_besselI`, `besselTerm_zero_succ`,
`besselPsi_hasDerivAt`, `riccati_zero_of_touch`), so that every
"exact" map row carries a DIRECT oracle witness rather than a
transitive one (audit round 1, hostile-editor finding 2): 34
entries, every one printing the same axiom list; green rebuild run 9
(again 8166 jobs — the only Lean change besides `Oracle.lean` was
the removal of one stale comment in `AmosBarrier.lean`).

## Audit expedient

The fabrication-side audit desks (mathematical referee, hostile
editor, checklist+formal-hygiene auditor — three independent
sessions) are recorded with findings and dispositions in
docs/C3-CHARTER.md Amendment 2.  The release-tree formal+repro
audit is recorded as an addendum to this manifest (post-tag by
sequencing; fixes, if any, go in post-tag commits — tags never
move), per the C2 pattern.
