# C4 release manifest

## Revisions (all ids recorded from POST-PUSH git log)

| Object | Value |
|---|---|
| Charter commit (pre-registration) | `bdf453b0` |
| Phase 1, J-C4-1 (runs 1 VACUOUS / 2 FAIL / 3 GREEN, 8167 jobs) | `523fe5c4` |
| Mid-course audit applied (Amendment 1, witnesses named, run 4, 44-entry oracle) | `a9f61179` |
| Amendment 2 (phase-2 refined design, own commit) | `73450f93` |
| Phase 2, J-C4-2 (run 5 GREEN, 8168 jobs, 53-entry oracle) | `346353b2` |
| Phase 3a (Riccati real, run 6, 8169 jobs, 61-entry) + Amendment 3 | `b19b6bd3` |
| Phase 3b (zone real, run 7, 8170 jobs, 68-entry) + Amendment 4 | `b7e241dd` |
| Phase 3c, J-C4-3 (THE THEOREM, run 8, 8171 jobs, 74-entry) + Amendment 5 | `56ff479b` |
| J-C4-4 grid 70/70 + Amendment 6 (protocol) | `2873e910` |
| Grid harness micropatch + transcript v2 (authoritative) | `ec0ef301` |
| Manuscript v1 | `4a699c81` |
| Manuscript v1.1 (owner + three-desk rounds, Amendment 7) | `354b6a11` |
| Manuscript v1.2 (nu-backslash micropatch, Amendment 8) | `70944009` |
| Release commit (manuscript v1.3 + this manifest) | tag `c4-v1.0` (ANNOTATED; this commit; tags never move) |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc6` |
| Mathlib pin | `07642720480157414db592fa85b626dafb71355b` (lakefile + manifest agree) |

## Canonical artifact hashes (SHA-256; LF = git blob representation)

| Artifact | SHA-256 |
|---|---|
| `papers/c4-amos-real/c4_amos_real.tex` (v1.3, LF blob) | `BBD0785A493240F43BEA20CC6FE3EDA8ED0521845024244638C8652C18173767` |
| `papers/c4-amos-real/c4_amos_real.pdf` (v1.3, binary) | `FDD3C8E52D46DBA22D9EEBAB7295059C8930CD1F9FFC903234FAA2CD526753F9` |
| `scripts/c4_oracle_output_phase3c.txt` (74-entry, at `56ff479b`) | `see dual-hash note` |
| `scripts/c4_amos_real_arb.py` (v2, portable) | `C1A4DF1784499DA2281B5BA5F34BD06FDAB747D8153EB98A233850139F317BAD` |
| `scripts/c4_amos_real_transcript_v2.txt` (authoritative) | `recorded at ec0ef301; v1 superseded-kept` |

EOL note (standing): git normalizes CRLF->LF at blob formation;
compare against `git show <rev>:path`, never a worktree checkout.
The oracle/transcript blob hashes are pinned by their commit ids
above; the release-tree audit re-derives them.

## Owner release order (Amendment 9)

The two companion viXra identifiers (C2 release `c2-v1.2.1`, C3
release `c3-v1.0.1`) were NOT yet assigned at release time.  BY
OWNER ORDER (2026-07-12) the release proceeds with the bibliography
citing "ai.viXra.org identifier pending at the time of this
release"; the identifiers will be inserted in a post-tag patch
(`c4-v1.0.x`) when assigned.  The former [BIB-ID-SLOT] blockers are
waived by the release authority; the waiver is registered in
docs/C4-CHARTER.md Amendment 9.

## Audit expedient

Fabrication-side desks (math referee, hostile editor,
checklist+formal-hygiene) + two owner render-audits: registered
with findings and dispositions in docs/C4-CHARTER.md Amendments
7-8.  The release-tree formal+repro audit and the external-tool
desk are recorded as addenda to this manifest (post-tag by
sequencing; fixes, if any, in post-tag commits — tags never move),
per the C2/C3 pattern.
