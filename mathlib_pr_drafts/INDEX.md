# `mathlib_pr_drafts/` — Master Index

**Last updated:** 2026-04-26 (Phase 480 — 20 PR-ready files, round number)
**Author:** Lluis Eriksson + Cowork agent (Claude)
**Status:** All files produced in workspace. `MatrixExp_DetTrace_DimOne_PR.lean` has been built against current Mathlib master; the remaining drafts still require a real Mathlib build pass.

---

## Purpose of this folder

This folder collects Lean 4 files that are **PR-ready candidates for upstream submission to Mathlib**. They are factored out of THE-ERIKSSON-PROGRAMME (Yang-Mills mass gap formalization) and stripped of project-specific dependencies, so each file imports **only mainline Mathlib**.

Each file is:

- self-contained (no `sorry`, no `axiom`)
- accompanied by a docstring explaining the result, its proof strategy, and PR submission notes
- closed with `#print axioms` to verify no spurious axioms slipped in
- elementary in proof technique (`linarith` / `nlinarith` / one or two existing Mathlib lemmas composed)

Except for `MatrixExp_DetTrace_DimOne_PR.lean`, these files are **not yet built** against Mathlib master. Each file flags its `Status (date)` line. The first concrete submission step for each unbuilt draft is `lake build` in a Mathlib checkout.

`MatrixExp_DetTrace_DimOne_PR.lean` was polished on 2026-04-26 in
`C:\Users\lluis\Downloads\mathlib4` on branch
`eriksson/det-exp-trace-fin-one`; local commit `cd3b69baae` builds on
Mathlib master `80a6231dcf`. The patch artifact is
`0001-feat-prove-det-exp-trace-for-1x1-matrices.patch`. PR opening is
blocked on GitHub publishing setup: no `gh` executable, no upstream push
permission, and no reachable `lluiseriksson/mathlib4` fork.

---

## §1. Inequality / special-functions PRs (20 files, Phases 401-479)

Each PR proposes a single elementary inequality missing from Mathlib in packaged form. All depend only on `Mathlib.Analysis.SpecialFunctions.Exp` or `Mathlib.Analysis.SpecialFunctions.Log.Basic`.

### Submission tier A — independent, can go in any order

| # | File | Theorem | Mathlib import |
|---|---|---|---|
| 1 | `KlarnerBFSBound_PR.lean` | `a_n ≤ a_1 · α^(n-1)` (BFS-tree bound) | `Nat.Basic`, `Algebra.Order.Group.Nat` |
| 2 | `BrydgesKennedyBound_PR.lean` | `|exp(t) - 1| ≤ \|t\| · exp(\|t\|)` | `SpecialFunctions.Exp` |
| 3 | `LogTwoLowerBound_PR.lean` | `1/2 < log 2` | `SpecialFunctions.Log.Basic`, `Exp` |
| 4 | `SpectralGapMassFormula_PR.lean` | `0 < λ < opNorm ⇒ 0 < log(opNorm/λ)` | `SpecialFunctions.Log.Basic` |
| 5 | `ExpNegLeOneDivAddOne_PR.lean` | `0 ≤ t ⇒ exp(-t) ≤ 1/(1+t)` | `SpecialFunctions.Exp` |
| 6 | `MulExpNegLeInvE_PR.lean` | `x · exp(-x) ≤ exp(-1)` | `SpecialFunctions.Exp` |
| 7 | `OneSubInvLeLog_PR.lean` | `0 < x ⇒ 1 - 1/x ≤ log x` | `SpecialFunctions.Log.Basic` |
| 8 | `ExpTangentLineBound_PR.lean` | `exp(a) + exp(a)·(x-a) ≤ exp x` | `SpecialFunctions.Exp` |
| 9 | `ExpLeOneDivOneSub_PR.lean` | `0 ≤ x < 1 ⇒ exp(x) ≤ 1/(1-x)` | `SpecialFunctions.Exp` |
| 10 | `CoshLeExpAbs_PR.lean` | `cosh(x) ≤ exp(\|x\|)` | `SpecialFunctions.Trigonometric.Basic` |
| 11 | `ExpMVTBounds_PR.lean` | `(b-a)·exp(a) ≤ exp(b)-exp(a) ≤ (b-a)·exp(b)` | `SpecialFunctions.Exp` |
| 12 | `NumericalBoundsBundle_PR.lean` | `2 < e < 3`, `log 2 < 1`, `0 < log 3 < 3/2` | `SpecialFunctions.Log.Basic`, `Exp` |
| 13 | `LogMVTBounds_PR.lean` | `(y-x)/y ≤ log(y) - log(x) ≤ (y-x)/x` | `SpecialFunctions.Log.Basic` |
| 14 | `LogLeSelfDivE_PR.lean` | `0 < x ⇒ log(x) ≤ x/e` (sharp at x = e) | `SpecialFunctions.Log.Basic` |
| 15 | `ExpSubOneLeSelfDivOneSub_PR.lean` | `0 ≤ x < 1 ⇒ exp(x) - 1 ≤ x/(1-x)` | `SpecialFunctions.Exp` |
| 16 | `LogOneAddLeSelf_PR.lean` | `-1 < x ⇒ log(1+x) ≤ x` (packaged dual of `add_one_le_exp`) | `SpecialFunctions.Log.Basic` |
| 17 | `LogLtSelf_PR.lean` | `0 < x ⇒ log x < x` (asymptotic comparison) | `SpecialFunctions.Log.Basic` |

### Submission tier B — companion / derivative results

| # | File | Theorem | Depends conceptually on |
|---|---|---|---|
| 18 | `OneAddDivPowLeExp_PR.lean` | `(1+x/n)^n ≤ exp x` for `x ≥ 0` | Tier A #5 (`add_one_le_exp`) |
| 19 | `OneAddPowLeExpMul_PR.lean` | `(1+x)^n ≤ exp(n·x)` for `x ≥ -1` | Same as #18, equivalent reformulation |

These two are **mathematically equivalent** (substitute `y := n·x` to swap forms). Submit one, mention the other in the docstring as an "equivalent reformulation" already proved.

**Sandwich pair**: tier A #5 (`ExpNegLeOneDivAddOne_PR.lean`) and
tier A #9 (`ExpLeOneDivOneSub_PR.lean`) together produce the
two-sided sandwich `1-x ≤ exp(-x) ≤ 1/(1+x)` (lower) and
`1+x ≤ exp(x) ≤ 1/(1-x)` (upper) on `[0, 1)`. Recommend submitting
as a single coordinated PR.

### Submission tier C — matrix/structural

| # | File | Theorem | Mathlib import |
|---|---|---|---|
| 20 | `MatrixExp_DetTrace_DimOne_PR.lean` | `det(exp A) = exp(trace A)` for `A : Matrix (Fin 1) (Fin 1) ℂ` | `MatrixExponential`, `Matrix.Trace`, `Determinant` |

This file closes the **`n = 1` case** of a **literal Mathlib TODO** at `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` line 57. Highest-priority submission target — there's an active Mathlib TODO it directly addresses.

---

## §2. Inactive / Cancelled

These files are preserved for git history and future reference, but they are
removed from the active Mathlib PR queue. They are either superseded by cleaner
Tier A PRs or are `sorry`-incomplete. Do not submit them upstream without a new
audit.

| # | File | Reason | Replacement / status |
|---|---|---|---|
| F1 | `AnimalCount.lean` | Superseded by Tier A PRs / `sorry`-incomplete | `KlarnerBFSBound_PR.lean` is the active replacement |
| F2 | `PiDisjointFactorisation.lean` | Superseded by Tier A PRs / `sorry`-incomplete | Keep as historical F3 sketch only |
| F3 | `PartitionLatticeMobius.lean` | Superseded by Tier A PRs / `sorry`-incomplete | Keep as historical Mayer/Ursell sketch only |
| F4 | `F3_Count_Witness_Sketch.lean` | Reference scaffold, not a PR draft | Keep as project-local reference only |

`KlarnerBFSBound_PR.lean` (tier A #1 above) **supersedes** `AnimalCount.lean` with a cleaner, more general statement.

---

## §3. Suggested submission order

**Priority 1** (literal Mathlib TODO, biggest impact):

1. `MatrixExp_DetTrace_DimOne_PR.lean` — closes `n=1` of the open TODO. Local patch built; PR URL pending fork/auth setup.

**Priority 2** (foundational `Real.exp` / `Real.log` bounds, individually small but collectively tighten the API):

2. `LogTwoLowerBound_PR.lean` — tiny, self-contained, sanity-check submission.
3. `SpectralGapMassFormula_PR.lean` — natural addition to `Real.log` library.
4. `OneSubInvLeLog_PR.lean` — dual to existing `Real.log_le_sub_one_of_pos`; submit alongside as a `_le_iff_le_` bidirectional sandwich.
5. `ExpTangentLineBound_PR.lean` — generalizes existing `add_one_le_exp` to arbitrary base point.
6. `MulExpNegLeInvE_PR.lean` — explicit form of standard concentration-inequality bound.
7. `ExpNegLeOneDivAddOne_PR.lean` — ubiquitous probability/numerical-analysis bound.
8. `BrydgesKennedyBound_PR.lean` — standard Mayer-cluster-expansion ingredient.
9. `OneAddDivPowLeExp_PR.lean` — elementwise form of classical limit; compound-interest bound.

**Priority 3** (combinatorial):

10. `KlarnerBFSBound_PR.lean` — clean general lattice-animal upper bound.

**Mention / don't submit separately**:

11. `OneAddPowLeExpMul_PR.lean` — equivalent to #9, mention as a corollary in the same PR.

Older F-series drafts: inactive/cancelled; do not spend upstream PR effort on
them unless Cowork opens a new audit task.

---

## §4. Pre-PR checklist (per file)

Before opening any PR upstream:

- [ ] Run `lake build` against current Mathlib master and confirm zero errors.
- [ ] Run `#lint` and address all warnings.
- [ ] Verify all axioms via `#print axioms <theorem_name>` show only `propext`, `Classical.choice`, `Quot.sound` (Mathlib-acceptable).
- [ ] Check Mathlib master for collisions: search `grep -r "exp_neg_le_one_div_one_add\|<theorem_name>" Mathlib/` to ensure not already added.
- [ ] Update import to most-specific Mathlib module (avoid `Mathlib` blanket import).
- [ ] Match Mathlib naming convention: snake_case, `Real.` namespace for real-valued, `Nat.` for nat-valued.
- [ ] Match Mathlib docstring style: `/-- **Theorem name** ... -/` then theorem body.
- [ ] Run `linter` and address every flag.

---

## §5. Verification status (2026-04-26)

| File | Workspace produced | `lake build` verified | Mathlib namespace collision checked |
|---|---|---|---|
| `MatrixExp_DetTrace_DimOne_PR.lean` | Yes | **Yes** — Mathlib master `80a6231dcf`; module and full build passed; local commit `cd3b69baae` | **Yes** — TODO present and theorem name absent before patch |
| `KlarnerBFSBound_PR.lean` | Yes | **No** | No |
| `BrydgesKennedyBound_PR.lean` | Yes | **No** | No |
| `LogTwoLowerBound_PR.lean` | Yes | **No** | No |
| `SpectralGapMassFormula_PR.lean` | Yes | **No** | No |
| `ExpNegLeOneDivAddOne_PR.lean` | Yes | **No** | No |
| `MulExpNegLeInvE_PR.lean` | Yes | **No** | No |
| `OneAddDivPowLeExp_PR.lean` | Yes | **No** | No |
| `OneSubInvLeLog_PR.lean` | Yes | **No** | No |
| `OneAddPowLeExpMul_PR.lean` | Yes | **No** | No |
| `ExpTangentLineBound_PR.lean` | Yes | **No** | No |
| `ExpLeOneDivOneSub_PR.lean` | Yes | **No** | No |
| `CoshLeExpAbs_PR.lean` | Yes | **No** | No |
| `ExpMVTBounds_PR.lean` | Yes | **No** | No |
| `NumericalBoundsBundle_PR.lean` | Yes | **No** | No |
| `LogMVTBounds_PR.lean` | Yes | **No** | No |
| `LogLeSelfDivE_PR.lean` | Yes | **No** | No |
| `ExpSubOneLeSelfDivOneSub_PR.lean` | Yes | **No** | No |
| `LogOneAddLeSelf_PR.lean` | Yes | **No** | No |
| `LogLtSelf_PR.lean` | Yes | **No** | No |

`MatrixExp_DetTrace_DimOne_PR.lean` is ready as a built local patch, but
the PR URL is still blocked on GitHub publishing setup. No PR has been
opened yet.

**No other file is ready for PR submission until the corresponding row above shows three "Yes".**

---

## §6. Honest caveat

Except for `MatrixExp_DetTrace_DimOne_PR.lean`, these are **drafts produced inside an LLM-assisted session without access to a Mathlib build environment**. The proofs are short and elementary, but standard pitfalls remain:

- A lemma name might exist in Mathlib already under a different signature.
- A tactic (`pow_le_pow_left`, `lt_div_iff₀`) may have been renamed in the version drift.
- The exact axiom-status of `Real.exp_nat_mul`, `Real.log_inv`, etc. should be confirmed.

**Treat each file as a math sketch + Lean draft, not as a verified contribution.** The path from this folder to a merged Mathlib PR is: clone Mathlib master → drop file in → `lake build` → fix tactic-name drift → run `#lint` → open PR.

---

*This index is the final consolidation of Phases 401-410 of the Yang-Mills formalization session. The PR-ready file production was an **opportunistic byproduct** of the project's working through `Real.exp` and `Real.log` bounds: every theorem here is something the project itself uses and would prefer not to re-prove from scratch.*
