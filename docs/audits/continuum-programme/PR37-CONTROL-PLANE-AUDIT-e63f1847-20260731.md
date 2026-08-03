# Independent control-plane audit — PR 37 at `e63f1847`

Snapshot:

```text
producer:   e63f1847b2e8a91631ec7f8ff7318a338534e2b0
tree:       7aa53152efe94373cf507889d1873dd211058578
merge-base: 1f81ec43404ae2a8c72a8c934807d4b03b8680c9
PR:         https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/37
```

## Mandatory raw freshness seal

```text
UTC=2026-07-31T08:51:10Z
COMMAND=git ls-remote origin refs/heads/main refs/pull/34/head refs/pull/35/head refs/pull/36/head refs/pull/37/head
5683f5929b0d4e2f0114bb8bac73ad39131ad4b7	refs/heads/main
0a46e266fc4808332ed20d2ab4611bfc271b208b	refs/pull/34/head
ecbd5c6831f982526602433e3fface0ab964d501	refs/pull/35/head
7fe64bbced729337f6a1060d731e661384863c42	refs/pull/36/head
e63f1847b2e8a91631ec7f8ff7318a338534e2b0	refs/pull/37/head
COMMAND=git rev-list --left-right --count e63f1847b2e8a91631ec7f8ff7318a338534e2b0...refs/remotes/audit/pr37
0	0
```

## Executive verdict

**FAIL with witnesses; keep draft; no merge.**

The PR contains valuable, unusually honest source documents and its local
validators pass. It nevertheless fails the preregistered public-compression
gate, misattributes the exact 8463-job build checkpoint, and publishes an
incomplete “canonical” publication count which its validator cannot defend.
The remote control-plane check is also red.

This desk did not edit any producer or governance file.

## Credit before findings

### C0 closure record — PASS

`docs/CONTINUUM-C0-CLOSURE.md` deserves credit. It says “CLOSED as a
scale-limit substrate and obstruction package; not merged; no paper”, keeps
the lane outside `YangMillsCore`, calls `(2,0)` the conjunction of two
independent product-topology limits, denies dependence of the second
coordinate on the first, and lists the missing law, tightness,
renormalisation, nontriviality, geometric RP, reconstruction, and gap
obligations. That is accurate compression inside the long-form record.

### C1 closure record — PASS on negative scope

`docs/CONTINUUM-C1-CLOSURE.md` limits the result to the current
strong-coupling KP window, states the finite cap, and denies positive
tightness, continuum-state, reconstruction, and mass-gap claims.

### Local validation — PASS, but only for the checks implemented

At the exact head:

```text
validate_publications.py       exit 0
validate_project_state.py      exit 0
validate_documentation_state.py exit 0
validate_dashboard.py          exit 0
check_consistency.py           exit 0
```

These results are credited without treating a validator as stronger than its
code.

## Public compression test — FAIL

The preregistered rule was that every new public-front-door phrase mentioning
C0 or C1 must carry the independent trichotomy, not only “closed”, “proved”,
or “closure”. The frozen audit results being compressed are:

```text
C0: PASS 7 / FAIL 0 / BLOCKED 6
C1: PASS 9 / FAIL 2 / BLOCKED 0
```

Diff-only measurement gives:

| Front door | Added C0/C1 mention lines | Lines containing `BLOCKED` | Verdict |
|---|---:|---:|---|
| `README.md` | 9 | 0 | FAIL |
| `CURRENT-STATE.md` | 7 | 0 | FAIL |
| `HYPOTHESIS_FRONTIER.md` | 9 | 0 | FAIL |
| `docs/dashboard/data.json` | 10 | 0 | FAIL |
| `docs/dashboard/index.html` | 0 literal mentions | 0 | FAIL as renderer |

The prose often includes good scope limitations; this prevents a broad false
continuum theorem. It does not preserve the audited trichotomy. In particular,
the dashboard records both `C0S` and `C1N` as `"status": "proved"`, and the
generic renderer turns that into:

```text
Proved - oracle-clean
```

The C0 node is green even though the external report has six material
`BLOCKED` gates. The C1 node suppresses two witnessed `FAIL`s, including the
physical sign/convention problem. Links to long-form caveats do not make the
green status itself trichotomic.

## `CLAUDE.md` line-by-line governance audit

The PR author and all four commit authors are the repository owner
`lluiseriksson`; there are no reviews or comments recording a second
authorization. The owner-authored changes are therefore attributable but
unreviewed.

| Change | Evidence | Verdict |
|---|---|---|
| Mark Surface Theorem closed and public as `2607.0089` | terminal seal already in repository; live public record resolves with matching title | PASS |
| Rename Part I from active to closed | matches `CURRENT-STATE.md` and terminal audit | PASS |
| Replace “relay in progress” with the completed theorem and executable final seal | exact final-seal script is named | PASS |
| Rename the old task queue “HISTORICAL — DO NOT EXECUTE” | prevents stale autonomous work; no proof rule removed | PASS |
| Preserve trichotomy, split-role, no-`sorry`, no-axiom, non-vacuity, oracle, Clay-distance, and explicit-staging rules | literal diff retains them | PASS |
| Change hard-rule-7 anchor from `7460e035` to `f0720ba7` | exact build transcript is attached to `7460e035`; `f0720ba7` records the subsequent full oracle | FAIL |

No standing mathematical-honesty rule is weakened. The checkpoint edit is a
metadata attribution failure, not a relaxation of the rule.

## 8463-job checkpoint cross-check — FAIL

Git history gives:

```text
f0720ba7 parent = 7460e035
f0720ba7 changed only CLAUDE.md, README-FOR-NEXT-MODEL.md,
REPRODUCIBILITY.md, and docs/VERIFICATION-LEDGER.md
```

Ledger Addendum 564 says the combined core was rebuilt at `7460e035` and
prints `Build completed successfully (8463 jobs)`. Addendum 565 says the
complete oracle ran at published checkpoint `f0720ba7`. The PR instead says
in `CLAUDE.md`, `CURRENT-STATE.md`, `README.md`, `docs/PROJECT-STATE.md`, and
`project-state.json` that the 8463-job full-core build is at `f0720ba7`.

The Lean source graph is unchanged between parent and child, so the numerical
count remains applicable to that graph. The exact command provenance is still
misstated. The honest representation needs separate build and oracle
checkpoints, or an explicit source-identical inheritance statement.

`validate_project_state.py` cannot catch this: it checks only that the
checkpoint is an ancestor, the job count is a positive integer, and the
evidence path exists. It never binds the count to a transcript at that SHA.

## Publication register

### Direct records and listed arithmetic — PASS for the listed set

The official pages resolve:

- `ai.viXra:2607.0089` — *Global Ratio Monotonicity for a Killed von Mises
  Bridge*;
- `ai.viXra:2607.0005` — *A Machine-Checked Volume-Uniform Wilson-Loop Area
  Law via a Formalized Cluster Expansion*.

All 28 listed public IDs occur on the live author index. Their titles match
apart from typography-only Unicode normalization in `2607.0042`. All 26
listed artifact paths exist. The two listed `published-unmirrored` entries
have null artifacts, and the two `repository-only` titles were not found on
the live author index. The malformed `2607.0035` record is correctly treated
as a duplicate of the same 2D SU(2) work represented canonically by
`2607.0039`.

### Completeness and counts — FAIL with witness

The canonical register omits:

```text
ai.viXra:2607.0001
A Machine-Verified Bijective Proof of the Rooted Child-Factorial Catalan
Identity over Spanning Trees of the Complete Graph
```

This is not an unrelated author-index item. Its official abstract explicitly
places the identity in this four-dimensional Yang--Mills programme. The
repository ledger calls it the released “Catalan formal id”, the cross-repo
reconciliation maps `Catalan identity = 2607.0001`, and multiple in-tree
papers cite it. `papers/c1-rooted-tree-majorants/CHANGELOG.md` explains that
its PDF belongs to the companion repository.

Because the register already has a `published-unmirrored` category, the
companion-repository location is not a reason to omit the public work. With
the stated programme-wide scope, the cross-check is:

```text
29 distinct public programme works
26 canonical PDFs in this repository
3 public works not mirrored here
2 repository manuscripts without a public ID
```

If the intended scope excludes companion-repository programme papers, that
inclusion rule is absent and the advertised completeness remains
**BLOCKED**. Under the scope actually written, the 28/26/2/2 claim is
**FAIL**.

### Validator defense — FAIL with executable witness

`audit_pr37_publications.py` loads the producer validator from the exact clean
checkout and applies two isolated mutations:

```text
baseline_errors=0
delete_2607.0093_errors=0
wrong_2607.0089_title_errors=0
ADVERSARIAL_WITNESS=VALIDATOR_ACCEPTS_BOTH_MUTATIONS
```

The validator checks ID syntax, ordering, artifact existence, placeholders,
and one hard-coded area-law mapping. It neither queries nor consumes a frozen
author-index snapshot, compares titles, enforces the advertised counts, nor
rejects a public row present in `PUBLICATIONS.md` but absent from JSON.
Therefore CI can defend a self-consistent but incomplete or mistitled
manifest.

```text
producer validate_publications.py sha256 =
470BBBD6941FBC873094E2207EAC0D0F5C6151FB99DD35ED2A01375BE663697A
independent audit_pr37_publications.py sha256 =
B70EEE806E731F026161B3994CB07AD4C987E983914080BBDD341C61FD344B58
```

## Remote CI — FAIL for merge readiness, inherited cause disclosed

The `honesty` and dashboard checks pass. `Validate repository control plane`
fails in `validate_run_manifests.py`:

```text
623 file(s), 4134 error(s)
```

The failure is the pre-existing historical run-manifest migration and is
explicitly disclosed in the PR body. This PR does not touch those manifests
or weaken that validator. Nevertheless the branch is not a green checkpoint
under hard rule 5, so this desk cannot issue a merge-ready PASS.

## Independent-model disclosure

The permitted Fable request was already exhausted by a verified HTTP 429 and
was not retried. No acceptable exact-`claude-opus-5` JSON exists. Neither
model contributed to this verdict.

## Final disposition

| Claim | Verdict |
|---|---|
| Long-form C0/C1 closure records | PASS, scoped |
| Public-front-door trichotomy preservation | FAIL |
| `CLAUDE.md` rule preservation | PASS |
| Exact 8463-job checkpoint attribution | FAIL |
| Listed publication IDs/artifacts | PASS |
| Canonical publication completeness/count | FAIL |
| Publication validator as external-record defense | FAIL |
| Current remote merge readiness | FAIL |

No merge and no producer-file edit.
