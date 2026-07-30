# Initial public-ref inventory and partial Paper 13 audit

Timestamp: `2026-07-30T23:40:37.8185962+02:00`  
Audit base: `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`  
Tree: `f35f500fa7be86bb0a4783904ee5cb403ea52f3e`

## Producer lanes

Command:

```text
git ls-remote --heads origin \
  refs/heads/codex/su2-wilson-reflection-positivity \
  refs/heads/codex/continuum-c0 \
  refs/heads/codex/continuum-c1
```

Output: empty.

The open-PR query filtered to the same three head names also produced empty
output. Therefore:

| Lane | Verdict | Missing datum |
|---|---|---|
| SU2 | **BLOCKED** | No public ref, head SHA, or PR |
| CONT-C0 | **BLOCKED** | No public ref, head SHA, or PR |
| CONT-C1 | **BLOCKED** | No public ref, head SHA, or PR |

The witness is nonexistence of the named refs at the timestamp above. It is not
the false statement that existing refs point to the audit base.

## Baseline correction incident

The first protocol commit named
`81721890ad3e111d73cbe45074d42ec698ce07b2`. A later authoritative fetch showed
that public `main` had advanced by one commit to `7c6aaab2`, adding Paper 13's
TeX/PDF. The protocol now contains both SHAs and a supersession record.

No claim from the Paper 13 TeX/PDF is credited at `81721890`: those two files
are absent there. `YangMills/OS/SpatialOS.lean` and
`scripts/judge_spatial_os.py` are present at `81721890`, so the earlier clean
run of that script remains a run on a real old-base artefact. The audit was
then repeated below at the corrected base.

## Clean public checkout

Construction:

```text
git clone --filter=blob:none --no-checkout \
  https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git <new-empty-dir>
git -C <new-empty-dir> checkout --detach \
  7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a
git -C <new-empty-dir> status --porcelain=v1
```

The status output was empty. `HEAD` and tree resolved to the identifiers at the
top of this report.

Tool versions:

```text
git version 2.43.0.windows.1
Lake version 5.0.0-src+00659f8 (Lean version 4.29.0-rc6)
Lean 4.29.0-rc6, commit 00659f8e6071d7e46131ed643bf8003b99b044e9
Python 3.12.6
NumPy 2.3.5
```

Load-bearing hashes:

| File | SHA-256 |
|---|---|
| `YangMills/OS/SpatialOS.lean` | `6FC0EE2C0EA981BF685F6FC2031D8B09CCD6093B42BC13CA35C8616AB1A0C7FA` |
| `scripts/judge_spatial_os.py` | `E79CEC13AE0387121E4A26513DD02691842D0D7721347C1FABCF7643284F92D9` |
| `papers/spatial-os/spatial_os.tex` | `3F809DC934B391DD070522D9B7936231A95F8E35BE0FB763B67F590B415E2883` |
| `papers/spatial-os/spatial_os.pdf` | `AE7BD3BA237E7901120179A8481CDB08B4EC57BA20AB3660D0F45E127D87C814` |

## Independent re-execution of the numerical judge

Command:

```text
python scripts/judge_spatial_os.py
```

Exit: `0`.

Summary emitted by the script:

```text
GATE A1: PASS  (site factorisation)
GATE A2: PASS  (bond factorisation)
GATE B : PASS  (beta >= 0 axiom form)
GATE C : PASS  (sharpness witness)
Each gate licenses its own theorem only.
```

The largest displayed normalised-tolerance stress cell was the bond case
`L=2, m=1, beta=0.80`, with absolute error `9.095e-13` and scale `7241`; it
remained within the script's `1e-12 * scale` rule.

Verdict: **PASS for the four finite numerical gates at the tested cells.** This
is not a proof of the full-path gluing identity and is not transferable to
continuous `SU(2)`.

## Lean re-execution

Clean-checkout command:

```text
lake env lean YangMills/OS/SpatialOS.lean
```

Exit: `1`. The exact blocker was:

```text
error: unknown module prefix 'Mathlib'
No directory 'Mathlib' or file 'Mathlib.olean' in the search path
```

The clean clone had package directories but no built Mathlib oleans. A second
run in the cached audit worktree reached the 184-second command limit with no
output. No third attempt was made.

Verdict: **BLOCKED** for independent Lean recompilation in this audit run,
missing a ready dependency build/time budget. This is not converted to an
artefact failure. The numerical result above remains independently
reproducible.

## Paper 13 claim-level verdict

The abstract at `papers/spatial-os/spatial_os.tex:43-60` states that:

1. the reflected form is defined as a sum over pairs of halves;
2. its identification with the Gibbs sum over whole paths is checked to
   `10^-12` by brute force;
3. that identification is not proved; and
4. until it is proved, the paper does not establish the
   Osterwalder--Schrader axiom.

The script exists at the immutable hash above. No producer-side run transcript
matching it is committed at the audit base; the tree query returns the judge
script but no `spatial_os` transcript.

Verdicts:

- **PASS**: the paper's disclaimer matches the artefact and does not claim a
  full OS axiom, `SU(N)`, continuum limit, or mass gap.
- **BLOCKED**: the historical producer execution cannot be validated from a
  committed producer transcript.
- **PASS**: this desk independently re-executed the numerical judge at the
  corrected SHA.
- **FAIL with witness** for any statement that the current Paper 13 artefact
  establishes the OS axiom: the missing gluing theorem is admitted literally
  in the abstract and is not a declaration in `SpatialOS.lean`.

## House-instrument self-test

At the audit base:

```text
python scripts/check_module_prose.py YangMills/OS/SpatialReflection.lean
python scripts/check_consistency.py
python scripts/source_db.py verify
```

All three exited `0`. The prose checker reported one module and zero failures;
the consistency checker reported zero `sorry` and zero core axioms; the source
database reported nine catalog files and no structural errors.

This validates the reusable instruments only. It is not evidence about a
future producer SHA.

## Independent-model disclosure

### Fable High

- Profile check: logged in as `masterythief@gmail.com` under profile
  `masterythief`.
- Task: one bounded adversarial test of the SU(2) crossing/gluing,
  conjugation, Haar, character-dimension, and coefficient gates.
- Result: HTTP `429`, command exit `1`, `is_error=true`, empty `modelUsage`,
  and `verified_fable_5=false`.
- Action: output rejected; no retry.

### Opus 5 Max

- Requested exact identifier: `claude-opus-5`.
- Configuration: `CLAUDE_CONFIG_DIR` for `masterythief`; API/auth environment
  variables removed; effort `max`; JSON output; no session persistence.
- Two attempts produced no JSON before their time limits. The exact spawned
  process trees were stopped.
- Result: no `is_error=false` object and no exact `modelUsage` entry existed,
  so no output was accepted or used.

All mathematical and repository conclusions in this report were checked by
this desk from primary sources or executable artefacts. Neither external model
is a source.

## Supersession: independent Lean re-execution completed

Timestamp: `2026-07-31T00:11:16+02:00`.

The earlier `BLOCKED` result under “Lean re-execution” above is superseded.
The missing-olean diagnosis was an audit-environment defect, not an artefact
defect.

The local cache
`C:\Users\lluis\AppData\Local\Temp\eriksson-push2\.lake\packages`
contained 7,788 Mathlib oleans. Before using it, the desk compared the
checkout and cache-owner inputs:

| Input | SHA-256 | Result |
|---|---|---|
| `lean-toolchain` | `8C46C0308E92095E478BCFAE7C357327E88C5A624B54ABF5AD1660EE0E51DF5A` | MATCH |
| `lake-manifest.json` | `E2F2D45A5FEF5AE352E6F8BE858726D603D83FDE30D740A14A8A2A588579381D` | MATCH |
| `lakefile.lean` | `09D3FF29B030A20C396CDD5F729230EEB7BCDE3AE91CDA519C0643AC6B715BD5` | MATCH |

A new public clone was checked out detached at
`7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`. Only
`.lake/packages` was junctioned to the verified cache; `.lake/build` remained
local to the clean clone. `git status --porcelain=v2` was empty before the
run.

Commands and results:

```text
lake env lean YangMills/OS/PSDKernel.lean
exit 0; elapsed 334641 ms

lake build YangMills.OS.SpatialOS
exit 0; elapsed 959995 ms
Build completed successfully (8173 jobs).
```

The first direct `SpatialOS.lean` attempt failed only because its project
imports had not yet been built in the new clone. The target build above is the
correct clean-checkout re-execution and replaces that intermediate failure.
No producer worktree or shared project build directory was read or modified.

Revised verdict: **PASS** for independent Lean compilation of
`YangMills.OS.SpatialOS` at the corrected public base. This does not alter the
separate **FAIL** for any claim that Paper 13 proves the missing gluing
identity or the full OS axiom.
