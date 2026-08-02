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

Both sit inside the proof of `signed_bound_attained`, at the two `by_cases h : x = 0 <;> simp [h]`
closures of the `sup'`/`inf'` computation.  They are `linter.unnecessarySimpa`
**suggestions**, not defects: following them was tried and reverted, because
`norm_num at h0` closes the hypothesis to `True` and the suggested `simp`
form then fails to discharge the goal.  The module declares them ACCEPTED
in-module rather than silencing the linter, so that the warning count is a
constant that an audit can check against, and a third warning would be a
change.  **Warning policy: exactly these two, at these two lines, and no
others.**

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

### Condition tally

| # | condition | state |
| --- | --- | --- |
| 1–9 | identity, clean tree, build exit 0, zero errors, warning policy, 9/9 reports, zero `sorryAx`, three-axiom cone, audit exit 0 | closed, checkout 1 |
| 10 | canonical SHA-256 reproduced from another checkout | closed, checkout 2 |
| 11 | no modification of the module after the audit | closed by **this** commit |

Gates added during the audit, and where each was exercised:

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

**Gate added, and passed:** the set of files listed in `MANIFEST.sha256` must
equal the set of files the commit actually contains, and every hash in it must
verify. Both were checked before committing — 16 files, 16 `OK`.  A manifest
that is not diffed against the commit is decoration.
