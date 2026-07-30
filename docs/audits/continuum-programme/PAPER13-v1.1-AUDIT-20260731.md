# Independent supersession audit — Paper 13 v1.1

Audit time: `2026-07-31` (Europe/Stockholm)

Audited public ref: `origin/main`

Audited SHA: `1e6113a10c407ba2964af2713aef26c62bbd1157`

Supersedes, for the changed claims only, the partial Paper 13 audit at
`7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`. The older execution record
remains valid for that immutable SHA.

## Verdict

- **PASS**: v1.1 adds an actual finite-family Gram identity and a nonnegative
  Gram theorem for the candidate bond form.
- **PASS**: the prose no longer says that `beta >= 0` is proved necessary. It
  correctly calls it sufficient and records the `L=0` obstruction to a
  universal necessity claim.
- **PASS**: the module and paper now prominently call the half-pairing forms
  candidates and say the assembly bijection is not proved.
- **FAIL with source witness** for any claim that v1.1 proves the full
  reflected Gibbs/OS pairing. The audited module defines a sum over pairs of
  halves; it still has no assembly map, inverse, bijection, or theorem equating
  that candidate form with the Gibbs sum over whole paths.
- **BLOCKED** for a separately declared site-reflection Gram matrix. The new
  cross form and the two Gram theorems are bond-only. This does not invalidate
  the site diagonal theorem, but the source desk does not infer an absent
  declaration.

Thus v1.1 closes the earlier finite-family bond-Gram gap. It does not close the
load-bearing gluing gap and does not establish the OS axiom. The paper's own
disclaimer passes; an external full-OS headline would fail.

## Changed evidence

The public mainline advanced from `7c6aaab2` through:

```text
4623a971 dashboard [skip ci]
293a3bab ctx: PAPER 13 v1.1 code
56b3d5ef merge main into s-block-v13
1e6113a1 ctx: PAPER 13 v1.1 tex+pdf
```

Only the following changed relative to the old audit:

```text
DASHBOARD.md
YangMills/OS/SpatialOS.lean
oracle_check.lean
papers/spatial-os/spatial_os.pdf
papers/spatial-os/spatial_os.tex
```

The desk did not edit or credit the dashboard. Canonical producer blobs:

| File | Git blob |
|---|---|
| `YangMills/OS/SpatialOS.lean` | `d2fe4a311b121b9d52b21f802340af08dddddd10` |
| `oracle_check.lean` | `d79e04dbc892060a6f31b0523573a73692cd4359` |
| `papers/spatial-os/spatial_os.tex` | `784fa1c0d0a2ed1a63678035fb876fdec3a7ff5d` |
| `papers/spatial-os/spatial_os.pdf` | `3fff8e29156f2abafd50800f95ab74fff9af21f0` |

## Claim-level checks

### P13-GRAM-BOND — PASS

At producer lines 349-354, `osPairingBondCross` defines the sesquilinear
cross form. `osPairingBondCross_eq` at lines 375-417 factors it through the
collapse. `osPairingBond_gram` at lines 427-450 proves

```text
sum_i,j conjugate(c_i) c_j PairingCross(F_i,F_j)
  = Pairing(sum_i c_i F_i).
```

`osPairingBond_gram_nonneg` at lines 456-463 combines that equality with the
existing nonnegativity theorem for `beta >= 0`. The conjugation and coefficient
order are correct for arbitrary complex coefficients.

### P13-SUFFICIENCY — PASS

The old “exactly for `beta >= 0`” prose was too broad because the negative
witness is not a theorem in this module and the zero-site kernel is the scalar
one. V1.1 changes the theorem and paper headings to sufficiency, explicitly
records the `L=0` exception, and leaves the sharpness witness open. This is a
scope repair, not a proof of necessity.

### P13-GLUING — FAIL with witness

Exact declaration and prose searches at the audited SHA find no full-path
assembly map, inverse, equivalence, or candidate-to-Gibbs equality. In
contrast, `SpatialOS.lean:18-23` states that the identification with the
reflected Gibbs sum is not proved, and the TeX abstract repeats the same
limitation.

That explicit absence is a finite source witness against a claim of completed
OS reflection positivity. Passing numerical gates A1/A2 to `1e-12` licenses a
future theorem; it is not the theorem.

### P13-GRAM-SITE — BLOCKED

The changed declarations contain no site cross form and no site Gram theorem.
The diagonal `osPairingSite_nonneg` remains valid for arbitrary complex
observables. A finite-family site statement may be derivable, but this desk
does not write the producer proof or treat derivability as a declaration.

## Clean-checkout transcript

A new public clone was checked out detached at `1e6113a1`; tracked status was
clean. The Mathlib package cache and prior clean build cache came from the
already audited parent checkout at `7c6aaab2`. All three pin inputs matched:

| Input | SHA-256 |
|---|---|
| `lean-toolchain` | `8C46C0308E92095E478BCFAE7C357327E88C5A624B54ABF5AD1660EE0E51DF5A` |
| `lake-manifest.json` | `E2F2D45A5FEF5AE352E6F8BE858726D603D83FDE30D740A14A8A2A588579381D` |
| `lakefile.lean` | `09D3FF29B030A20C396CDD5F729230EEB7BCDE3AE91CDA519C0643AC6B715BD5` |

The build cache was copied, not shared. Lake invalidated and rebuilt the
changed target.

```text
python scripts/check_module_prose.py YangMills/OS/SpatialOS.lean
exit 0; modules checked: 1; failures: 0

python scripts/check_consistency.py
exit 0; zero sorry; zero verified-core axioms

python scripts/source_db.py verify
exit 0; 9 catalog files; no structural errors

python scripts/judge_spatial_os.py
exit 0; gates A1, A2, B, and C PASS

git diff --check 7c6aaab2..1e6113a1
exit 0

lake build YangMills.OS.SpatialOS
exit 0; cached replay 93223 ms
Build completed successfully (8173 jobs).

lake env lean \
  <auditor-checkout>/docs/audits/continuum-programme/oracles/PAPER13-v1.1-oracle.lean
exit 0; 33069 ms
```

The five new-declaration oracle queries each emitted exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Warnings replayed from dependencies. No project axiom was reported.

## Independent-model disclosure

The permitted Fable request had already returned HTTP 429 and was rejected
without retry. Exact-identifier Opus attempts supplied no acceptable JSON.
Neither model contributed evidence or conclusions to this supersession.

