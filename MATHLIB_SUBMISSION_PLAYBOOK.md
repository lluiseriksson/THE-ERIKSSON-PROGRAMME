# MATHLIB_SUBMISSION_PLAYBOOK.md

**Audience**: Lluis, or any agent / human picking up the work in a Mathlib build environment
**Author**: Cowork agent (Claude), produced 2026-04-25 (Phase 424)
**Subject**: end-to-end playbook for submitting the 17 PR-ready files in `mathlib_pr_drafts/` to Mathlib upstream
**Companion documents**: `mathlib_pr_drafts/INDEX.md`, `MATHLIB_PRS_OVERVIEW.md`

---

## 0. TL;DR

This document goes deeper than `INDEX.md` §4: it is the **operational playbook** for actually submitting PRs. Read it when:

- You have a Mathlib master clone with `lake` working.
- You have ≥30 min per file budgeted.
- You want to land 9-10 merged PRs out of the 17-file collection.

Estimated total time end-to-end (assuming no major roadblocks): **6-12 hours**.

---

## 1. Setup checklist (do once)

```bash
# 1. Clone Mathlib master (if not already).
cd ~/work
git clone https://github.com/leanprover-community/mathlib4.git
cd mathlib4

# 2. Verify lake builds.
lake build  # expect ~30-60 min on first build, much faster afterwards

# 3. Check Mathlib version.
git log -1 --pretty=format:"%h %s"

# 4. Ensure your fork is set up for PR.
git remote add fork https://github.com/<yourusername>/mathlib4.git
```

---

## 2. Per-file submission pipeline

For **each** of the 17 PR-ready files, follow this exact sequence:

### 2.1 Pick a file from the priority queue

Per `INDEX.md` §3, the priority order is:

1. `MatrixExp_DetTrace_DimOne_PR.lean` — closes literal Mathlib TODO at `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean:57`. **Highest priority**.
2. `LogTwoLowerBound_PR.lean` — smallest, simplest sanity-check submission.
3. `SpectralGapMassFormula_PR.lean` — natural addition to `Real.log` library.
4. `OneSubInvLeLog_PR.lean` — dual to existing `Real.log_le_sub_one_of_pos`.
5. `ExpTangentLineBound_PR.lean` — generalises existing `add_one_le_exp`.
6. `MulExpNegLeInvE_PR.lean` — explicit form of standard concentration bound.
7. `ExpNegLeOneDivAddOne_PR.lean` + `ExpLeOneDivOneSub_PR.lean` — coordinated sandwich PR pair.
8. `BrydgesKennedyBound_PR.lean` — Mayer cluster expansion ingredient.
9. `OneAddDivPowLeExp_PR.lean` + `OneAddPowLeExpMul_PR.lean` — coordinated equivalent-pair PR.
10. `KlarnerBFSBound_PR.lean` — combinatorial.
11. `CoshLeExpAbs_PR.lean` — hyperbolic.
12. `ExpMVTBounds_PR.lean` + `LogMVTBounds_PR.lean` — coordinated MVT pair.
13. `NumericalBoundsBundle_PR.lean` — small bundle of `e`, `log 2`, `log 3` bounds.
14. `LogLeSelfDivE_PR.lean` — sharp asymptotic bound.

### 2.2 Drop file in Mathlib checkout

Each file targets a specific Mathlib path. Suggested locations:

| Source file | Mathlib target path |
|---|---|
| `MatrixExp_DetTrace_DimOne_PR.lean` | inline into `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` |
| `LogTwoLowerBound_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `SpectralGapMassFormula_PR.lean` | new file `Mathlib/Analysis/SpecialFunctions/Log/SpectralGap.lean` |
| `OneSubInvLeLog_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `ExpTangentLineBound_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `MulExpNegLeInvE_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `ExpNegLeOneDivAddOne_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `ExpLeOneDivOneSub_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `BrydgesKennedyBound_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `OneAddDivPowLeExp_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `OneAddPowLeExpMul_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `KlarnerBFSBound_PR.lean` | new file `Mathlib/Combinatorics/Animals/BFSBound.lean` (path may need bikeshedding) |
| `CoshLeExpAbs_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean` |
| `ExpMVTBounds_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `LogMVTBounds_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `NumericalBoundsBundle_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `LogLeSelfDivE_PR.lean` | inline into `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |

For "inline" files, copy the relevant theorems into the existing Mathlib file, removing duplicate imports. For "new file" entries, create a fresh file and add it to the relevant `import` chain.

### 2.3 Run `lake build` and address errors

```bash
lake build Mathlib.Analysis.SpecialFunctions.Log.Basic
```

The most likely error categories:

#### 2.3.1 Tactic-name drift

| Drafted name | Likely current Mathlib name (as of 2026-04-25) | Fix |
|---|---|---|
| `pow_le_pow_left h_nn h_le n` | `pow_le_pow_left₀ h_nn h_le n` (in some recent versions) | Add the `₀` suffix |
| `lt_div_iff₀ h_pos` | sometimes `lt_div_iff h_pos` (no zero suffix) | Drop the `₀` |
| `one_div_le_one_div_of_le h_pos h_le` | possibly renamed | Check `Mathlib/Order/Field/Basic.lean` |
| `Real.log_div h_x_ne h_y_ne` | argument order may be `(h_x : x ≠ 0) (h_y : y ≠ 0)` or different | Check signature |
| `Real.exp_nat_mul x n` | possibly `Real.exp_nat_mul n x` (argument swap) | Adjust |
| `Real.add_one_lt_exp h_ne` | sometimes `Real.add_one_lt_exp_of_ne` | Check |
| `mul_le_mul_of_nonneg_left` | stable, but check argument ordering | `mul_le_mul_of_nonneg_left h_le h_nn` not `(h_nn h_le)` |
| `abs_of_nonneg` | stable | — |

When in doubt, `#check <name>` in Lean to inspect signature.

#### 2.3.2 Namespace collision

```bash
grep -rn "exp_le_one_div_one_sub\|exp_neg_le_one_div_one_add\|log_le_self_div_e" Mathlib/
```

If a name already exists in Mathlib, rename the new one (e.g., add `_pr` suffix until merged) or check whether the existing one supersedes ours.

#### 2.3.3 Missing import

If `Real.cosh_eq` is used and unresolved, add:
```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
```

### 2.4 Run `#lint` and address warnings

```lean
#lint only unusedHavesSuffices in MyTheorem
```

Common Mathlib lint rules:
- **`unusedHavesSuffices`**: remove `have h_xxx : ...` if unused.
- **`docBlame`**: add `/-- ... -/` docstring above any `theorem` lacking one.
- **`namedDocBlame`**: top-level `def`s need docstrings starting with `**Name** : ...`.
- **`hasNonemptyInstance`**: if a structure has no instance, mark with `Nonempty`.

Each PR must clear `lake exe lint` before review.

### 2.5 Verify `#print axioms` is clean

```lean
#print axioms exp_le_one_div_one_sub
-- expected: [propext, Classical.choice, Quot.sound]
```

If unexpected axioms appear, hunt them down — Mathlib does not accept new theorems with non-standard axioms.

### 2.6 Update Mathlib's public API exports

Some Mathlib files re-export their content via root imports. After adding a theorem:
- Check `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` exports.
- Check `Mathlib.lean` (top-level) for explicit re-export, if relevant.

### 2.7 Open the PR

Per Mathlib's CONTRIBUTING.md:

```bash
git checkout -b feature/pr-name
git add Mathlib/Analysis/SpecialFunctions/...
git commit -m "feat(Analysis/SpecialFunctions/Exp): add exp_le_one_div_one_sub"
git push fork feature/pr-name
gh pr create --title "feat(Analysis/SpecialFunctions/Exp): add exp_le_one_div_one_sub" \
             --body-file pr-body.md
```

---

## 3. PR description templates

Use one of these per file. Templates assume the PR adds a single theorem (or pair) without renaming existing API.

### 3.1 Template for `_le_` / `_lt_` style addition

```markdown
This PR adds the elementary bound

  `<theorem statement>`

which is missing from Mathlib in packaged form.

## Motivation

<2-3 sentences on why the bound is useful and where it appears>

## Proof strategy

Direct corollary of `<existing Mathlib lemma>` via <one-line strategy>.

## API design

- `Real.<theorem_name>`: the main statement.
- `Real.<theorem_name>_strict`: strict variant (if applicable).
- Numerical instance(s): demonstrating sharpness or sanity check.

## Verification

- `#print axioms <theorem_name>` returns `[propext, Classical.choice, Quot.sound]`.
- `lake build` passes.
- `lake exe lint` clean.
```

### 3.2 Template for "closes TODO" PR (`MatrixExp_DetTrace_DimOne_PR.lean`)

```markdown
This PR closes the **`n = 1` case** of the literal Mathlib TODO at
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean:57`:

  `Matrix.det (NormedSpace.exp ℂ A) = Complex.exp (Matrix.trace A)`.

The general-`n` case is **still open** (it requires Jacobi's formula
or Schur decomposition). This PR is the smallest non-trivial stepping
stone and does not block the general TODO.

## Strategy

Any 1×1 matrix is diagonal; both sides reduce to `exp (A 0 0)`.

## Verification

- `#print axioms` clean.
- `lake build` passes.
- The general-`n` TODO remains in place after this merge.
```

### 3.3 Template for "coordinated pair" PR (sandwich, MVT)

```markdown
This PR adds two complementary bounds that together form a sandwich
on [appropriate range]:

  `<bound 1>`
  `<bound 2>`

The two are intentionally submitted together because each motivates
the other — submitting only one would leave the API asymmetric.

## API

- `Real.<bound_1_name>` and `Real.<bound_2_name>`.
- A packaged `Real.<sandwich_name>` returning both as `And`.
- Numerical instances showing the bounds are sharp at the endpoints.

## Verification

- `#print axioms` clean for all three.
- `lake build` passes.
- `lake exe lint` clean.
```

---

## 4. Common roadblocks and resolutions

### 4.1 "Argument has type X but expected Y"

Most likely cause: implicit-vs-explicit argument drift between the drafted `theorem` signature and current Mathlib API.

**Fix**: read the error carefully. If `h_pos` is now `{h_pos : 0 < x}` instead of `(h_pos : 0 < x)`, swap the brackets. If a new argument has been added (e.g., `[Decidable]`), supply it.

### 4.2 "Failed to synthesize instance"

Most likely cause: a typeclass instance Mathlib has but our import doesn't pull in.

**Fix**: try `import Mathlib` (catch-all) to confirm. Once it builds, replace with the most-specific imports.

### 4.3 "Unknown identifier `Real.log_div`"

Most likely cause: the lemma was renamed.

**Fix**: search `grep -r "log.*div\b" Mathlib/Analysis/SpecialFunctions/Log/Basic.lean | head` for the current name.

### 4.4 "PR is too large / split it"

If a Mathlib reviewer asks to split a PR, do it. Typical decompositions:
- Sandwich pair → two separate PRs (lower-bound, upper-bound).
- Equivalent reformulations → one PR; mention the other in docstring.
- Numerical bundle → one PR; mention all pieces in description.

### 4.5 "We already have `Real.log_le_self`" (or similar collision)

If the reviewer points out that an existing lemma supersedes ours:
- Check whether the existing one can be re-stated in the form drafted (sometimes our packaging is the missing convenience form).
- If genuinely superseded, close the PR and remove the file from this collection.
- Update `INDEX.md` and `MATHLIB_PRS_OVERVIEW.md` to reflect.

---

## 5. Success criteria

A PR is **merged successfully** when:

- [ ] Lean build passes in CI.
- [ ] All `#lint` warnings addressed.
- [ ] `#print axioms` clean.
- [ ] At least one Mathlib reviewer has approved.
- [ ] Documentation generated correctly via `lake exe mathlib_doc`.

A PR is **stuck and should be closed** when:

- [ ] Reviewer indicates the lemma is not wanted upstream (e.g., too specialised).
- [ ] An existing Mathlib lemma is found to supersede.
- [ ] You no longer have time to maintain it.

---

## 6. Estimated time per file

| File | Estimated polish time | Notes |
|---|---|---|
| `MatrixExp_DetTrace_DimOne_PR.lean` | 2-3 h | Literal TODO closure; reviewers will look closely |
| `LogTwoLowerBound_PR.lean` | 30 min | Smallest, simplest |
| `KlarnerBFSBound_PR.lean` | 1-2 h | New combinatorial file; needs path bikeshedding |
| `BrydgesKennedyBound_PR.lean` | 30-60 min | Standard `nlinarith` proof |
| `LogLeSelfDivE_PR.lean` | 30 min | Direct corollary |
| `OneSubInvLeLog_PR.lean` | 30 min | Direct dual |
| `SpectralGapMassFormula_PR.lean` | 30 min | Domain naming may need adjustment |
| `ExpTangentLineBound_PR.lean` | 45 min | Generalisation; check no name collision |
| `ExpNegLeOneDivAddOne_PR.lean` | 30 min | Direct corollary |
| `ExpLeOneDivOneSub_PR.lean` | 30 min | Direct dual |
| `OneAddDivPowLeExp_PR.lean` | 30 min | Standard induction |
| `OneAddPowLeExpMul_PR.lean` | 0 min | Mention as corollary in #11's PR |
| `MulExpNegLeInvE_PR.lean` | 30 min | Direct corollary |
| `CoshLeExpAbs_PR.lean` | 30 min | Case analysis |
| `ExpMVTBounds_PR.lean` | 45 min | Two-sided bound |
| `LogMVTBounds_PR.lean` | 45 min | Dual of #15 |
| `NumericalBoundsBundle_PR.lean` | 30 min | Bundle multiple bounds |

**Total estimate**: ~10-13 hours of focused work to land all 9-10 PRs.

---

## 7. Final word

This playbook assumes you start from a working Mathlib build environment. If you don't, set that up first (§1).

The 17 files were drafted in a Cowork session **without `lake`**, so expect tactic-name drift and minor signature mismatches even for proofs as short as 2-5 lines. The proofs themselves are mathematically correct; the polishing is administrative.

Each merged PR is a small win — and 9-10 merged Mathlib PRs from this session is a substantial outward contribution.

**Treat the 17 files as solid math sketches with Lean drafts attached, not as finished contributions.** That's the honest framing.

---

*Cross-references*: `mathlib_pr_drafts/INDEX.md`, `MATHLIB_PRS_OVERVIEW.md`, `MATHLIB_GAPS.md`, `COWORK_FINDINGS.md` Finding 020.
