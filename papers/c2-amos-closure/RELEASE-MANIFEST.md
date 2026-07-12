# C2 release manifest

## Revisions

| Object | Value |
|---|---|
| Charter commit (pre-registration) | `426d299a` |
| Certified companion run 1 (superseded) | `719c5488` |
| Lean integration commit | `b0aa4f7017e5aeb5a7e923fb13d9b0e8839632d9` |
| Companion run 2 (corrected majorant) | `b65aced1` |
| Manuscript v2 commit | `ec873a6a` |
| Release tag | `c2-v1.0` (this commit; tags never move) |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc6` |
| Mathlib pin | `07642720480157414db592fa85b626dafb71355b` |

## Canonical artifact hashes (SHA-256; LF = git blob representation)

| Artifact | LF blob | CRLF worktree (where distinct and known) |
|---|---|---|
| `scripts/c2_amos_arb.py` (run 2) | `0528DADF563D9A51EB80A95E34FB813830A5968983B5820861A3A044E5AB1DEF` | `11370EE82194CBC7EC23DC0135BD6A128A04F8E9A90BDCE743AC63CED393E21C` |
| `scripts/c2_amos_transcript.txt` (run 2) | `3D703169ACFA287C131198B06C575B26766AA17563423FC707B2CBF97268EC3F` | `ACCC11D6EB7E108993804385EDC41E2A345228CFCD3927327BB36E29DB1FBC7F` |
| `scripts/c2_oracle_output.txt` | `A0080A064B18910A573063CAE620D07D4947DE13B12D95B2BAE9CEAC1CD5BF36` | — |
| `scripts/c2_lake_build_run1_GREEN_transcript.txt` | `F2809C4F1448CA1034BF7EFBACF89CCEE0028426A567DC84825567FD4B228669` | — |
| `papers/c2-amos-closure/c2_amos_closure.tex` (v2) | `3EAD9A336A344B0813E2D8A001812B50346FBE00739A044D5C29BECBE62F3A4E` | — |
| `papers/c2-amos-closure/c2_amos_closure.pdf` (v2) | `AB86F83D5C895B55C43215C70996A57C6E33E3460D204EF805D1CE3585D97867` (binary, no EOL) | — |

EOL note (standing, from the C1 arc): the script executed with LF
bytes — the `0528DADF...` value printed inside the transcript and
quoted in the paper is the LF/blob canonical hash; a later
`core.autocrlf` checkout materialized the worktree copy as CRLF
(`11370EE8...`).  Git normalizes CRLF->LF at blob formation;
"committed unmodified" means content not reconstructed, not binary
identity across EOL normalization.  Compare against
`git show <rev>:path`, never a worktree checkout.

## Supersession

`scripts/c2_amos_transcript_v1_SUPERSEDED.txt` (+ its HASHES file) is
run 1, kept committed with diagnosis: tail majorant covered only
k >= K+1 (t_K unbucketed; enclosures non-containing by <= 6.5e-34
relative; independently measured conservative at all visible grid
points, so its verdicts were true statements reached by an unsound
documented method).  Authoritative transcript: run 2
(`c2_amos_transcript.txt`), corrected majorant t_K/(1-q), identical
printed values.

## Audit expedient

Charter (docs/C2-CHARTER.md) Amendment 1 records the three-desk audit
(math referee, hostile editor, numeric auditor) with findings and
resolutions; the formal+repro audit on the release tree is recorded
as Amendment 2 (post-tag by sequencing; fixes if any go in post-tag
commits, tags never move).

## Addendum (c2-v1.0.1): run-2 commit id correction + final audit

The formal+repro audit (PASS 8/8) flagged that the run-2 commit id
above, `b65aced1`, is a pre-rebase orphan: a dashboard-bot commit
landed concurrently and the push was rebased, so the reachable
on-main twin is `1721f65e` (identical message, author, parent and
tree except one bot DASHBOARD.md line; the orphan is unreachable
from any ref and GC-vulnerable).  Authoritative run-2 commit:
`1721f65e`.  Nothing else in this manifest is affected; every one
of its 8 hash values was independently re-derived by the release
auditor with zero mismatches, and both the companion transcript and
the oracle log were re-executed byte-identically on the release
tree.

## Addendum 2 (c2-v1.0.2): tag-scoped manuscript hashes + review fixes

External review of c2-v1.0.1 (7.1/10) sustained a REAL manifest
defect: the table above lists the v2 manuscript hashes (3EAD9A33 /
AB86F83D - correct AT c2-v1.0) while c2-v1.0.1 ships v2.1.  Rule
adopted: manuscript hashes are TAG-SCOPED and each tag's addendum
stamps its own.  For the record, all independently confirmed by the
reviewer and re-derived here:

| Manuscript | LF blob (tex) | pdf |
|---|---|---|
| v2 (at c2-v1.0) | 3EAD9A336A344B0813E2D8A001812B50346FBE00739A044D5C29BECBE62F3A4E | AB86F83D5C895B55C43215C70996A57C6E33E3460D204EF805D1CE3585D97867 |
| v2.1 (at c2-v1.0.1) | C203FDDEFDFA4EA752981428EA047BE1A22D4CEF5AFD27BDF3596DA052FD398D | 022305592F433842061052AE633AB64EA1B2897A43E4495AE4C465167949FF87 |
| v2.2 (at c2-v1.0.2) | 305F0A7DD414CBBE7EF8C3278D2332041CC8CB320BE3BF9601A11A67C6D37710 | A790076678EF79CE6A290BF560F3B3168083006F51668F64BE1ECC72661C226B |

Also fixed in v2.2 (review-mandatory): release tense corrected to
past (the tags exist); bibliography completed with Hornik-Grun 2013
(JMAA 408, 91-101) and Hornik-Grun 2024 (MIA 27(4), 775-787, both
verified against the sources) plus the why-this-bound remark (exact
calibration + HG24 optimality within the generalized family);
abstract restructured mathematics-first.
