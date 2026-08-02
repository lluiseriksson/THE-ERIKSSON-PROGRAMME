# D-3a — TERMINAL AUDIT RECORD

**This record does not modify `YangMills/OS/DobrushinOscillation.lean`.**
The `Formalized` status of the nine declarations below derives from THIS
document and its artifacts, not from any sentence in the source file.  A module
that certifies itself certifies nothing; that separation is the whole point of
the A/B split registered in `docs/DOBRUSHIN-D3-CHARTER.md`.

Artifacts: `docs/audits/d3a-916de45a/`, listed with sizes and SHA-256 in
`MANIFEST.sha256` of that directory.

---

## 1. The object audited

```
Source commit      916de45a6d09df417e2af4e10f080f0521498fb2
Source blob        0a14617b87360d29d7cd20bda4308a8ee0857236
Canonical SHA-256  87ac87f63f9fe442230d84a7208e1735bbb7180334af67572df29c36838019c3
Path               YangMills/OS/DobrushinOscillation.lean
```

Four identifiers are carried because three of them are answers to different
questions and the fourth is the trap:

| identifier | question it answers |
| --- | --- |
| commit | which revision of the repository |
| blob OID | which bytes git stores for this path |
| canonical SHA-256 | the SHA-256 of exactly those stored bytes |
| *materialized* SHA-256 | the SHA-256 of the bytes actually on disk — the one that can differ |

### Discarded candidates

```
ff840b4d   first candidate,  discarded
693e0287   second candidate, discarded
```

Both commits stand, immutable, in the history.  **No evidence in this record is
attributed to either.**  Every measurement below was taken against
`916de45a…`, which is the only audited target.

### Toolchain identity

```
lean-toolchain   leanprover/lean4:v4.29.0-rc6
mathlib pinned   07642720480157414db592fa85b626dafb71355b
```

---

## 2. Checkout 1 — the only build and axiom audit of `A″`

Clean clone at `C:/Users/lluis/AppData/Local/Temp/d3a-audit-1`, created with
`--no-checkout` and configured **before** materialising any file:

```
core.autocrlf   false     (file:.git/config)
core.eol        lf        (file:.git/config)
```

### 2.1 Identity of the bytes that were compiled

```
commit          = 916de45a6d09df417e2af4e10f080f0521498fb2
blob            = 0a14617b87360d29d7cd20bda4308a8ee0857236
working_blob    = 0a14617b87360d29d7cd20bda4308a8ee0857236     (git hash-object --no-filters)
canonical_sha256= 87ac87f63f9fe442230d84a7208e1735bbb7180334af67572df29c36838019c3
working_sha256  = 87ac87f63f9fe442230d84a7208e1735bbb7180334af67572df29c36838019c3
```

```
Raw blob equality                       PASS
Canonical / materialized SHA-256        PASS
git status --porcelain                  empty
git check-attr -a                       no attribute for this path
```

Artifacts: `checkout-1-identities.txt`, `checkout-1-git-config.txt`,
`checkout-1-status.txt`, `checkout-1-attributes.txt`.

### 2.2 Build

```
Command    lake build YangMills.OS.DobrushinOscillation
Started    2026-08-02T14:51:32Z
Finished   2026-08-02T15:12:57Z
Exit code  0
Jobs       8158
Duration   379 s   (the module's own build step)
Errors     0
stderr     empty (0 bytes, attested in MANIFEST.sha256)
Warnings   exactly 2, both accepted in the source, both reproduced verbatim below
Additional warnings   0
```

The two warnings, copied literally from `checkout-1-build.stdout.log`:

```
⚠ [8158/8158] Built YangMills.OS.DobrushinOscillation (379s)
warning: YangMills/OS/DobrushinOscillation.lean:236:8: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: YangMills/OS/DobrushinOscillation.lean:245:8: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Build completed successfully (8158 jobs).
```

Both warnings occur on the two `simpa using h0` / `simpa using h1` lines inside
the `sup'`/`inf'` calculation of `signed_bound_attained` — line 236 is
`simpa using h0`, line 245 is `simpa using h1`.  The two adjacent
`by_cases h : x = 0 <;> simp [h]` closures, at lines 229 and 246, already use
`simp` and are **not** the object of the suggestion.

They are `linter.unnecessarySimpa` **suggestions**, not defects.  The linter's
own proposal is `simp`.  A separate repair, `norm_num at h0`, was also tried and
failed for a different reason — it closes the hypothesis to `True`, after which
`exact h0` no longer discharges the goal — and the two must not be conflated:
what the linter asked for and what was attempted are different edits.  The
module declares both warnings ACCEPTED in-module rather than silencing the
linter, so that the warning count is a constant an audit can check against and
a third warning would be a change.  **Warning policy: exactly these two, at
lines 236 and 245, and no others.**

### 2.3 Focused axiom audit

```
Command    lake env lean _audit.lean       (driver preserved as checkout-1-audit-driver.lean)
Exit code  0
Reports    9 #check + 9 #print axioms, 9/9 completed
stderr     empty (0 bytes, attested)
sorryAx    0 occurrences
Axiom union over all nine declarations:
           propext
           Classical.choice
           Quot.sound
```

Artifacts: `checkout-1-build.stdout.log`, `checkout-1-build.stderr.log`,
`checkout-1-build.exit.txt`, `checkout-1-audit-command.txt`,
`checkout-1-audit-driver.lean`, `checkout-1-signatures-and-axioms.log`,
`checkout-1-audit.stderr.log`, `checkout-1-audit.exit.txt`,
`checkout-1-timing.txt`.

---

## 3. The audited inventory

Nine declarations in three classes.  The classes are not decoration: an
endpoint is a result the chain consumes, a witness is what stops the constant
from being a number above the truth, and an auxiliary is exported convenience
that carries no claim.  Counting them together would let the module report a
larger inventory than it earns.

### 3.1 Five analytic endpoints

```
@sum_zero_sub_const : ∀ {S : Type u_1} [inst : Fintype S] {a : S → ℝ},
  ∑ x, a x = 0 → ∀ (g : S → ℝ) (c : ℝ), ∑ x, a x * (g x - c) = ∑ x, a x * g x
@abs_sub_mid_le : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : Nonempty S] (g : S → ℝ) (x : S),
  |g x - mid g| ≤ osc g / 2
@abs_sum_signed_le : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : Nonempty S] {a : S → ℝ},
  ∑ x, a x = 0 → ∀ (g : S → ℝ), |∑ x, a x * g x| ≤ (∑ x, |a x|) / 2 * osc g
@TV_nonneg : ∀ {S : Type u_1} [inst : Fintype S] (p q : S → ℝ), 0 ≤ TV p q
@abs_sum_sub_le_tv_mul_osc : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : Nonempty S] {p q : S → ℝ},
  ∑ x, p x = ∑ x, q x → ∀ (g : S → ℝ), |∑ x, (p x - q x) * g x| ≤ TV p q * osc g
```

**Hypothesis discrimination, read off the signatures and not asserted:**

* `sum_zero_sub_const` and `TV_nonneg` require **only** `Fintype S`.  Neither
  needs a nonempty carrier, and the printed signatures show it.
* `abs_sub_mid_le`, `abs_sum_signed_le` and `abs_sum_sub_le_tv_mul_osc`
  require `Fintype S` **and** `Nonempty S`, because `osc` is defined through
  `sup'`/`inf'`, which do not exist on an empty type.
* `DecidableEq S` was removed from the section variables and appears in **no**
  signature.  It was carried at one point and was not needed.

### 3.2 One sharpness witness, counted separately

```
signed_bound_attained : |∑ x, ((if x = 0 then 1 else 0) - if x = 1 then 1 else 0) * if x = 0 then 1 else 0| =
  (TV (fun x => if x = 0 then 1 else 0) fun x => if x = 1 then 1 else 0) * osc fun x => if x = 0 then 1 else 0
```

A closed theorem — no variables, no hypotheses.  It exhibits an **equality**
where `abs_sum_sub_le_tv_mul_osc` gives `≤`.  Two point masses on `Fin 2`,
tested against the indicator of the first, attain the bound.  This is what
licenses calling the constant *the* constant: `TV · osc` with `TV` carrying
the `1/2`, and not `2 · TV · osc`, which the charter registered in advance as
the cheap fallback that would have halved the window.

### 3.3 Three exported auxiliaries

```
@inf_le_apply : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : Nonempty S] (g : S → ℝ) (x : S),
  Finset.univ.inf' ⋯ g ≤ g x
@apply_le_sup : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : Nonempty S] (g : S → ℝ) (x : S),
  g x ≤ Finset.univ.sup' ⋯ g
@osc_nonneg : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : Nonempty S] (g : S → ℝ), 0 ≤ osc g
```

### 3.4 Axiom cones, all nine

```
'YangMills.OS.Dobrushin.sum_zero_sub_const'        depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.OS.Dobrushin.abs_sub_mid_le'            depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.OS.Dobrushin.abs_sum_signed_le'         depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.OS.Dobrushin.TV_nonneg'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.OS.Dobrushin.abs_sum_sub_le_tv_mul_osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.OS.Dobrushin.signed_bound_attained'     depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.OS.Dobrushin.inf_le_apply'              depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.OS.Dobrushin.apply_le_sup'              depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.OS.Dobrushin.osc_nonneg'                depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. Checkout 2 — reproduction of the hash, and nothing more

A second, independent clone from the remote, on a different kernel and a
different git:

```
Environment      WSL2 Ubuntu 24.04
                 Linux 5.15.167.4-microsoft-standard-WSL2  x86_64
                 git version 2.43.0
core.autocrlf    <unset>
core.eol         <unset>

Raw blob equality                    PASS   (0a14617b… = git hash-object --no-filters)
Canonical / materialized SHA-256     PASS   (87ac87f6… = 87ac87f6…)
Working tree                         clean
Path attributes                      none

Lean build                           NOT RUN
Axiom audit                          NOT RUN
Warning policy                       NOT EXERCISED
```

**`elan` is not installed in that environment.**  Amendment 2 of the charter
makes a second build *preferable*, not obligatory for reproduction of the
hash, so its absence is not a failure — but it is recorded here in the
negative so that the absence of a toolchain can never later be read as a
second compilation.

Artifacts: `checkout-2-environment-and-identities.log`, `checkout-2-script.sh`.

**What this checkout is, and what it is not.**  The charter's literal
condition is *another checkout*, and that is what closes condition 10.  That
this checkout also happens to be another kernel, another git and another
filesystem is **reinforced evidence**, recorded separately.  It is not
retroactively promoted to a requirement — a condition tightened after seeing
the result is not a condition, and the same discipline that forbade weakening
a gate after evaluating it forbids strengthening one.  Both checkouts share
one physical host; that limit is stated rather than left to be discovered.

---

## 5. ERRATUM to the commit message of `A″` (`916de45a`)

The source file is not touched.  What is corrected here is the **prose of the
commit message**, which claimed more than had been established at the moment
it was written.

1. **The elaboration that preceded the terminal checkout ran on a CRLF
   materialization.**  It was performed in the fabrication clone, whose
   `core.autocrlf` came from the system gitconfig; the bytes on disk there
   were 10746, against 10498 canonical.  That elaboration therefore did **not**
   certify the canonical blob.

2. **"Focused elaboration on these bytes exits zero with only the two accepted
   linter suggestions" was too strong.**  At the time it was written, "these
   bytes" were not the bytes elaborated.  The statement is true *now* — but it
   is made true by §2 of this record, not by the commit that asserted it.

3. **The platform inference was also too strong.**  The message reasoned that
   because `core.autocrlf = true` sits in the system gitconfig, "every clone on
   this machine is affected and a Linux clone is not."  Both halves are wrong
   as stated: checkout 1 is on this machine and was **not** affected, because
   the configuration was set before materialisation; and checkout 2 produced
   canonical bytes not *because* it is Linux but because no conversion was
   configured there.  **The platform does not determine byte identity.**

4. **The authority is the test, not the environment.**  Source identity is
   established by, and only by,
   ```
   git rev-parse HEAD:<path>  ==  git hash-object --no-filters <path>
   ```
   together with equality of the canonical and materialized SHA-256.  This is
   why the check is repeated in **every** checkout instead of being inferred
   once from the operating system.

5. **Only checkout 1 counts as the terminal build and axiom audit of `A″`.**
   No build evidence exists for `ff840b4d`, for `693e0287`, or for checkout 2.

---

## 6. Closure

> At source commit `916de45a6d09df417e2af4e10f080f0521498fb2` and source blob
> `0a14617b87360d29d7cd20bda4308a8ee0857236`, the five analytic endpoints, the
> separately counted sharpness witness, and the three exported auxiliaries were
> compiled in a clean checkout whose materialized bytes were proved identical to
> the committed blob.  The targeted audit completed 9/9 reports, found zero
> `sorryAx`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.
> The canonical SHA-256 `87ac87f63f9fe442230d84a7208e1735bbb7180334af67572df29c36838019c3`
> was reproduced from a second independent checkout.  These nine declarations
> therefore satisfy the repository's definition of `Formalized`.

### Condition tally — the ELEVEN of Amendment 2, quoted, not paraphrased

The charter's list is conjunctive and is reproduced here in its own words.  An
earlier version of this table replaced conditions 1–9 with a summary of
checkout-1 evidence, which is a different list; the substitution is corrected in
§8.

| # | condition, verbatim from Amendment 2 | where its evidence is |
| --- | --- | --- |
| 1 | focused elaboration succeeds | §2.2 — exit 0, 8158 jobs, zero errors |
| 2 | five endpoints compiled | §3.1 — five `#check` signatures |
| 3 | the exact equality witness compiled | §3.2 — `signed_bound_attained`, closed theorem |
| 4 | non-emptiness explicit in the signature | §3.1 — `[Nonempty S]` printed where required, and ABSENT from the two that do not need it |
| 5 | a single convention for `TV` and for `osc` | source lines 114 (`osc`), 119 (`mid`), 179 (`TV`) — one definition each, none repeated |
| 6 | the factor `1/2` traceable to one lemma | §8.2 — the analytic `1/2` is created once, at line 142 |
| 7 | the TV/oscillation corollary obtained by REWRITING, not by a second proof under another convention | §8.3 — the proof is `unfold TV; exact this` |
| 8 | stdout, stderr and exit code preserved OUTSIDE the VM | `docs/audits/d3a-916de45a/`, attested in `MANIFEST.sha256` |
| 9 | focused oracle clean | §2.3 — 9/9 reports, zero `sorryAx`, three-axiom cone, exit 0 |
| 10 | SHA-256 reproduced from another checkout | §4 — checkout 2 |
| 11 | no subsequent modification of the module | commit `75fb3734` and its erratum change no Lean |

Separately, and NOT part of the eleven: two gates were **added during** the
audit, at the auditor's request, after the charter was written.  They are listed
apart precisely so that a condition invented mid-audit is never counted as one
that was pre-registered.

| gate | checkout 1 | checkout 2 |
| --- | --- | --- |
| raw equality `blob = working_blob` | PASS | PASS |
| canonical SHA-256 = materialized SHA-256 | PASS | PASS |
| warning policy | PASS | **not exercised** |

### What this record does NOT establish

* `docs/../YangMills/OS/DobrushinGruss.lean` (Popoviciu) remains **SOURCE, NOT
  RESULT**.  It is unelaborated and is deliberately not a dependency of D-3c.
* **D-3c is open.**  The key lemma is not written.
* **The global comparison estimate is open.**
* **The finite-time operator interface is open**, and charter prohibition 4
  stands: even a complete D-3 would give decay of correlations, not
  `sup_L specRatio(L) < 1`.
* The current manuscript claims only the earlier chain and is unchanged by this
  record.  D-3a enters the paper, if at all, in a later version.

`A` and `A′` are discarded candidates.  `A″` is the audited target.  This
commit modifies no Lean.

---

## 7. One defect found while assembling this record

Staging was printed **in full** before committing, per Addendum 577, and the
listing did not match the directory: five files were missing, and they were the
three load-bearing ones — the build log carrying the two warnings, the
signature/axiom-cone log, and the checkout-2 log — plus the two empty `stderr`
captures.

Cause, from `git check-ignore -v`:

```
.gitignore:9:*.log    docs/audits/d3a-916de45a/checkout-1-build.stdout.log
```

The repository-wide `*.log` rule is correct for build scratch and silently
wrong for an evidence directory.  Had the commit gone out unexamined, this
record would have cited a `MANIFEST.sha256` listing sixteen artifacts while the
repository contained eleven, and every quoted log would have been unverifiable
from the repository — the same defect that cost PR #43 four documentary rounds.

**Fixed durably**, not with a one-off `git add -f`: `docs/audits/.gitignore`
carries `!*.log`, so the next evidence record does not step on the same rule.
That file is the one item in this commit not named in the audit specification,
and it is here for this reason.

**Gate added, and passed**, stated with its universe named exactly:

> the 16 entries of `MANIFEST.sha256` must equal the set of artifacts the commit
> contains **in `docs/audits/d3a-916de45a/`, excluding the manifest itself**, and
> all 16 hashes must verify.

16 files, 16 `OK`.  The manifest does **not** cover the whole commit and never
claimed to: the commit contains 19 paths — those 16 artifacts, plus
`MANIFEST.sha256`, plus this record, plus `docs/audits/.gitignore`.  An earlier
wording of this gate said "the set of files the commit actually contains", which
is false as written; corrected in §8.  A manifest that is not diffed against the
commit is decoration, but a gate whose universe is left vague is worse — it
reads as covering more than it checks.

---

## 8. ERRATUM to this record (commit `75fb3734`)

Three documentary defects found by external audit of `B` itself.  None touches
the build, the axiom cones, the hashes or the `Formalized` status; all three are
this record describing its own evidence inaccurately, which is the class of
defect this lane has now paid for five times.  The module is not touched: the
blob at HEAD is still `0a14617b87360d29d7cd20bda4308a8ee0857236`.

### 8.1 The warnings were mislocated

This record said the two warnings sit "at the two `by_cases h : x = 0 <;> simp [h]`
closures".  **False.**  Read from the audited source:

```
229|       · by_cases h : x = 0 <;> simp [h]
...
236|         simpa using h0
...
245|         simpa using h1
246|       · by_cases h : x = 0 <;> simp [h]
```

The warnings are at 236 and 245 — the `simpa using h0/h1` lines.  The `by_cases`
lines are 229 and 246, they already use `simp`, and the linter says nothing
about them.  The two were adjacent in the proof and got conflated in prose.

Also corrected: the record implied `norm_num` was the linter's suggestion.  It
was not — the linter proposes `simp`; `norm_num at h0` was a separate repair
attempt that failed for a separate reason.

### 8.2 The tally substituted a different list for conditions 1–9

The charter's Amendment 2 fixes eleven conjunctive conditions.  This record's
table replaced the first nine with a summary of checkout-1 evidence — identity,
clean tree, exit code, warning policy, and so on.  Those are real and they are
recorded, but **they are not conditions 1–9**, and two of them (raw equality,
warning policy) are gates added *during* the audit, which the record itself
separated one paragraph later and then re-mixed in the table above it.

Corrected: §6 now quotes the eleven verbatim and points each at its evidence,
and the added gates are listed apart under their own heading.

Evidence for the two conditions that had no explicit anchor before:

* **Condition 6, the `1/2` traceable to one lemma.**  Three occurrences of the
  factor exist and they have distinct roles, so the honest statement names all
  three rather than claiming there is one:
  * line 121, inside `def mid` — the midpoint's own definition;
  * line 142, `abs_sub_mid_le : |g x - mid g| ≤ osc g / 2` — **the analytic
    factor, created here and nowhere else**; every later `/2` in
    `abs_sum_signed_le` (lines 164, 170, 173) is this one propagated;
  * line 179, inside `def TV` — the definitional normalisation.

  The analytic and definitional halves are identified by rewriting, not added.
  That is exactly what condition 7 checks.

* **Condition 7, corollary by rewriting.**  The whole proof, from the audited
  source:
  ```lean
  191| theorem abs_sum_sub_le_tv_mul_osc {p q : S → ℝ}
  192|     (h : ∑ x, p x = ∑ x, q x) (g : S → ℝ) :
  193|     |∑ x, (p x - q x) * g x| ≤ TV p q * osc g := by
  194|   have hzero : ∑ x, (p x - q x) = 0 := by
  195|     rw [Finset.sum_sub_distrib, h, sub_self]
  196|   have := abs_sum_signed_le hzero g
  197|   unfold TV
  198|   exact this
  ```
  `unfold TV; exact this`.  No second proof, no second convention.

### 8.3 The manifest gate was stated over too wide a universe

"the set of files listed in `MANIFEST.sha256` must equal the set of files the
commit actually contains" is false as written: the manifest lists 16 artifacts,
the commit contains 19 paths.  The gate that was actually run — and the correct
one — is scoped to `docs/audits/d3a-916de45a/` excluding the manifest itself.
Corrected in §7.

### What did NOT change

`916de45a` remains the audited source; `0a14617b…` remains its blob;
`87ac87f6…` remains the canonical SHA-256; the build, the nine signatures, the
nine axiom cones and both checkouts are untouched.  Condition 11 stays closed:
this erratum modifies no Lean.
