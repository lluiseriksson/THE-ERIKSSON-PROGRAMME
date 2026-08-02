# D-3c — TERMINAL AUDIT RECORD

**This record does not modify `YangMills/OS/DobrushinComparison.lean`.**  The
module's banner defers to exactly this document; the source text does not
certify its own status.

Artifacts: `docs/audits/d3c-40ca8523/` — 15 artifacts, listed with size and
SHA-256 in `MANIFEST.sha256`, which is the sixteenth file and does not list itself.
Driver: `.d3c-audit/DobrushinComparisonAudit.lean`, preserved at the path it ran
from.

---

## 1. The object audited

**Source identity**

```
Source commit (A)   40ca85239cb14f18ebf16aa46769f3bc02bbaf6b
Source blob         3fe356cc97e57f2d241158b692e6b8a3acece83a
Canonical SHA-256   698080fa80ea44d2f1ae7b46cab333b5d0d6f4b97d205df2844db69d510017ea
Path                YangMills/OS/DobrushinComparison.lean
```

**Materialization identity** — the per-checkout working-tree SHA-256, compared
against the canonical one, and the only quantity here that a checkout filter can
change.

```
Checkout 1 (Windows, autocrlf=false, eol=lf)   698080fa…   == canonical
Checkout 2 (WSL2, autocrlf unset)              698080fa…   == canonical
```

**Discarded candidates** — all three stand immutable in the history, and **no
evidence in this record is attributed to any of them**:

```
72bb1c66   first elaborated candidate
2ec1ce33   second elaborated candidate
3d5752a2   third elaborated candidate
```

**Toolchain**: `leanprover/lean4:v4.29.0-rc6`, Mathlib pinned
`07642720480157414db592fa85b626dafb71355b`.

---

## 2. Checkout 1 — the only build and axiom audit of `A`

Clean clone, `core.autocrlf=false` and `core.eol=lf` set **before** materialising
any file.

### 2.1 Identity, closed before Lean ran

```
commit              = 40ca85239cb14f18ebf16aa46769f3bc02bbaf6b     OK
blob                = 3fe356cc97e57f2d241158b692e6b8a3acece83a     OK
working_blob        = 3fe356cc97e57f2d241158b692e6b8a3acece83a     OK  RAW EQUALITY
canonical_sha256    = 698080fa…                                    OK
materialized_sha256 = 698080fa…                                    OK
git status          = empty (0 bytes)
git diff (module)   = clean
git check-attr -a   = no attribute for this path (0 bytes)
```

### 2.2 Focused build

```
Command    lake build YangMills.OS.DobrushinComparison
Exit code  0
Jobs       8159
Duration   351 s   (the module's own build step)
Errors     0
stderr     empty (0 bytes, attested in MANIFEST.sha256)
```

**Job-count delta: +1 against the 8158 measured for D-3a**, which is what adding
one module to the cone should cost.

**Warning attribution, stated precisely.**  Two warnings appear in the build
log.  **Neither comes from `DobrushinComparison`**, which produced none.  Both
are *replayed* from the already-built dependency `DobrushinOscillation`, and they
are the same two `linter.unnecessarySimpa` suggestions that D-3a accepted
in-module, at the same lines:

```
⚠ [8158/8159] Replayed YangMills.OS.DobrushinOscillation
warning: YangMills/OS/DobrushinOscillation.lean:236:8: try 'simp' instead of 'simpa'
warning: YangMills/OS/DobrushinOscillation.lean:245:8: try 'simp' instead of 'simpa'
✔ [8159/8159] Built YangMills.OS.DobrushinComparison (351s)
Build completed successfully (8159 jobs).
```

**Warning policy for this module: zero warnings of its own, and the two
inherited ones are D-3a's, already accepted there.**

### 2.3 Focused audit

```
Command    lake env lean .d3c-audit/DobrushinComparisonAudit.lean
Exit code  0
Transcript 176 lines, 14257 bytes — SAVED IN FULL BEFORE ANY SUMMARY
stderr     empty (0 bytes, attested)
```

---

## 3. The manifest, and what 40/40 means

**40/40 is coverage of the manifest.  It is NOT "40 theorems".**

```
31 theorems      #check AND #print axioms   → candidates for `Formalized`
 9 definitions   #check only                → compiled, covered by the manifest,
                                              axiom cones deliberately NOT reported
```

Coverage checked against the driver, not asserted:

```
names asked by the driver   40
names reported by Lean      40
missing                      0
extra                        0
duplicates                   0
```

A first pass of this check reported only 22 of 40, because it matched signatures
opening with `@Name`.  Lean prints `@Name : …` when there are implicit or
instance arguments to expose and `Name : …` when `@` is a no-op — 22 + 18 = 40.
**The gate was wrong, not the audit**, and it is recorded because a coverage
check that silently under-counts would have looked like missing declarations.

### Classes

```
11  load-bearing / interface   deltaAt_siteExp_self, deltaAt_siteExp_le,
                               Bupd_mulVec, deltaVec_siteExp_le,
                               deltaAt_eq_deltaAtOff, abs_sub_update_le,
                               abs_sub_le_deltaAt, deltaAt_nonneg,
                               C_nonneg_of_majorant, Bupd_mulVec_mono,
                               Bupd_mulVec_mono_of_majorant
 4  headline witnesses         deltaVec_hypotheses_satisfiable,
                               Witness.hypotheses_hold, Witness.pw_tv_attained,
                               Witness.deltaAt_siteExp_attained
16  supporting witness lemmas  uniformKernel_{local,nonneg,sum,tv},
                               Witness.{fw_update_zero, fw_update_one, pw_local,
                               two_cases, pw_nonneg, pw_sum, Cw_diag, pw_tv,
                               siteExp_pw, deltaAt_zero_fw, deltaAt_one_fw,
                               deltaAt_one_siteExp}
 9  definitions                deltaAt, deltaAtOff, siteExp, LocalKernel, Bupd,
                               uniformKernel, Witness.{pw, Cw, fw}
```

All names in the driver are **fully qualified**, so nothing depends on an
implicit `open`.

---

## 4. Axiom cones — 31 of 31

```
sorryAx occurrences            0
errors in the transcript       0
warnings in the transcript     0
union of axioms over all 31    propext, Classical.choice, Quot.sound
axioms outside that trio       0
```

**One cone is a PROPER SUBSET, and that is not a defect.**

```
30 cones  [propext, Classical.choice, Quot.sound]
 1 cone   [propext]                                 Witness.two_cases
```

`Witness.two_cases` is proved by `decide` and needs neither `Classical.choice`
nor `Quot.sound`.  A smaller cone is strictly better than the permitted one.
Recorded because the first version of this gate tested for *equality* with the
trio and flagged it as a violation: **the correct criterion is containment, not
equality**, and D-3a's record said "every cone exactly [propext, Classical.choice,
Quot.sound]" — true there, and not the right general test.

## 5. `DobrushinGruss` is outside the cone

```
DobrushinComparison  imports  YangMills.OS.DobrushinOscillation
DobrushinOscillation imports  Mathlib
Gruss in the transitive source cone                0
Gruss olean required by the focused build          0
Gruss anywhere in the audit transcript             0
```

Popoviciu is not a dependency of D-3c, by construction and by measurement.

---

## 6. Checkout 2 — SHA reproduction, and nothing more

```
Environment      WSL2 Ubuntu 24.04, Linux 5.15.167.4-microsoft-standard-WSL2
                 git 2.43.0, core.autocrlf unset, core.eol unset
                 elan: absent      lake: absent

commit / blob / raw equality              PASS
canonical == materialized                 PASS
canonical SHA-256 reproduced (698080fa…)  PASS
working tree clean, no path attributes    PASS

Lean build       NOT RUN
Axiom audit      NOT RUN
Warning policy   NOT EXERCISED
```

The charter's literal condition is *another checkout*, and that is what this
closes.  That it is also another kernel, another git and another filesystem is
**reinforced evidence, filed separately** — a condition tightened after seeing
its result is not a condition.  Both checkouts share one physical host, and that
limit is written down rather than left to be found.

---

## 7. Closure

> At source commit `40ca85239cb14f18ebf16aa46769f3bc02bbaf6b` and source blob
> `3fe356cc97e57f2d241158b692e6b8a3acece83a`, the manifest's 40 named
> declarations were compiled in a clean checkout whose materialized bytes were
> proved identical to the committed blob before Lean was invoked.  The focused
> build exited 0 in 8159 jobs with no warning of its own.  The focused audit
> exited 0, reported 40 of 40 manifest names with none missing, none extra and
> no duplicates, found zero `sorryAx`, and reported axiom cones for all 31
> theorems whose union is exactly `propext`, `Classical.choice`, `Quot.sound`.
> The canonical SHA-256 was reproduced from a second independent checkout.
>
> **The manifest contains 40 named declarations: 31 theorems with targeted axiom
> reports, now `Formalized`, and 9 compiled definitions covered by the manifest
> but not claimed `Formalized`, because their axiom cones were deliberately not
> reported.**

### What this does NOT establish

* **D-3d is not done.**  This is the local transport input; iterating it is a
  separate rung, and `Bupd_mulVec_mono_of_majorant` is the interface it will
  consume, not the iteration itself.
* **D-3e is not done.**  Converting that iteration into the covariance
  comparison estimate is a further rung.
* **Charter prohibition 4 stands.**  Even a complete D-3 yields decay of
  correlations, **not** `sup_L specRatio(L) < 1`; the finite-time operator
  interface remains open.
* `YangMills/OS/DobrushinGruss.lean` (Popoviciu) remains **SOURCE, NOT RESULT**.
* The manuscript is unchanged and claims only the earlier chain.

`72bb1c66`, `2ec1ce33` and `3d5752a2` are discarded candidates.  `40ca8523` is
the audited target.  This commit modifies no Lean.
