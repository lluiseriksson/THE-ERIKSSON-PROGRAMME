# MATHLIB_PRS_OVERVIEW.md

**Author**: Cowork agent (Claude), produced 2026-04-25 (Phase 415, refreshed Phase 480 = 20 files round number)
**Subject**: outward-facing catalog of contributions THE-ERIKSSON-PROGRAMME has prepared for upstream submission to Mathlib
**Companion documents**: `MATHLIB_GAPS.md` (the *inward* direction — what we need from Mathlib), `mathlib_pr_drafts/INDEX.md` (organisational doc inside the drafts folder)

---

## 0. TL;DR

`mathlib_pr_drafts/` contains **20 PR-ready Lean files** factored out of THE-ERIKSSON-PROGRAMME, each:

- **Self-contained**: imports only mainline Mathlib, no project-specific dependencies.
- **Elementary**: proof in 1-5 line tactic block.
- **Documented**: copyright Apache-2.0, docstring with proof strategy + PR submission notes, closing `#print axioms` to verify no spurious axiom.
- **Missing in packaged form**: each closes an elementary inequality / identity not currently in Mathlib in the form drafted.

**Critical caveat**: **None has been built with `lake build`** against current Mathlib master. The workspace producing them lacks `lake`. Tactic-name drift (`pow_le_pow_left`, `lt_div_iff₀`, `Real.log_inv`, `Real.exp_nat_mul`, `mul_le_mul_of_nonneg_left`) is real and will require non-trivial polishing per file before any PR opens.

---

## 1. The 20 PR-ready files

### 1.1 By Mathlib subject area

#### `Real.exp` lemmas (10 files)

| File | Theorem | Comments |
|---|---|---|
| `BrydgesKennedyBound_PR.lean` | `\|exp(t)-1\| ≤ \|t\|·exp(\|t\|)` | Mayer cluster expansion ingredient |
| `ExpNegLeOneDivAddOne_PR.lean` | `0 ≤ t ⇒ exp(-t) ≤ 1/(1+t)` | Markov / numerical analysis |
| `MulExpNegLeInvE_PR.lean` | `x · exp(-x) ≤ 1/e` | Concentration inequality bound |
| `OneAddDivPowLeExp_PR.lean` | `(1+x/n)^n ≤ exp(x)` | Compound interest / Poisson approx |
| `OneAddPowLeExpMul_PR.lean` | `(1+x)^n ≤ exp(n·x)` | Bernoulli generalisation |
| `ExpTangentLineBound_PR.lean` | `exp(a) + exp(a)·(x-a) ≤ exp(x)` | Tangent line bound at any base |
| `ExpLeOneDivOneSub_PR.lean` | `0 ≤ x < 1 ⇒ exp(x) ≤ 1/(1-x)` | Dual of `ExpNegLeOneDivAddOne` |
| `ExpMVTBounds_PR.lean` | `(b-a)·exp(a) ≤ exp(b)-exp(a) ≤ (b-a)·exp(b)` | Two-sided MVT bound |
| `ExpSubOneLeSelfDivOneSub_PR.lean` | `0 ≤ x < 1 ⇒ exp(x) - 1 ≤ x/(1-x)` | Geometric-series form of deviation |
| (sandwich) | `1+x ≤ exp(x) ≤ 1/(1-x)` and `1-x ≤ exp(-x) ≤ 1/(1+x)` for `x ∈ [0, 1)` | Coordinated PR pair |

#### `Real.log` lemmas (7 files)

| File | Theorem | Comments |
|---|---|---|
| `LogTwoLowerBound_PR.lean` | `1/2 < log 2` | Concrete numerical bound |
| `SpectralGapMassFormula_PR.lean` | `0 < lam < opNorm ⇒ 0 < log(opNorm/lam)` | Spectral gap → mass gap |
| `OneSubInvLeLog_PR.lean` | `0 < x ⇒ 1 - 1/x ≤ log(x)` | Dual to `log_le_sub_one_of_pos` |
| `LogMVTBounds_PR.lean` | `(y-x)/y ≤ log(y) - log(x) ≤ (y-x)/x` | Two-sided MVT bound for log |
| `LogLeSelfDivE_PR.lean` | `0 < x ⇒ log(x) ≤ x/e` | Sharp asymptotic bound (= at x=e) |
| `LogOneAddLeSelf_PR.lean` | `-1 < x ⇒ log(1+x) ≤ x` | Packaged dual of `add_one_le_exp` |
| `LogLtSelf_PR.lean` | `0 < x ⇒ log x < x` | Asymptotic comparison (strict) |

#### Hyperbolic (1 file)

| File | Theorem | Comments |
|---|---|---|
| `CoshLeExpAbs_PR.lean` | `cosh(x) ≤ exp(\|x\|)` | Sub-Gaussian / Hoeffding ingredient |

#### Numerical bounds bundle (1 file)

| File | Theorem | Comments |
|---|---|---|
| `NumericalBoundsBundle_PR.lean` | `2 < e < 3`, `log 2 < 1`, `0 < log 3 < 3/2` | Closed-form sanity checks |

#### Combinatorial (1 file)

| File | Theorem | Comments |
|---|---|---|
| `KlarnerBFSBound_PR.lean` | `a_n ≤ a_1 · α^(n-1)` | Lattice animal upper bound |

#### Matrix / structural (1 file)

| File | Theorem | Comments |
|---|---|---|
| `MatrixExp_DetTrace_DimOne_PR.lean` | `det(exp A) = exp(trace A)` for `n=1` | **Closes literal Mathlib TODO** |

### 1.2 The headline PR

**`MatrixExp_DetTrace_DimOne_PR.lean`** is the highest-priority submission because it closes a **literal Mathlib TODO** at `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean:57`. The general-`n` case requires Jacobi's formula or Schur decomposition (open Mathlib problem); the `n=1` case is closed here as a stepping stone.

### 1.3 The headline coordinated pair

**`ExpNegLeOneDivAddOne_PR.lean` + `ExpLeOneDivOneSub_PR.lean`** together produce the two-sided sandwich

```
1 - x ≤ exp(-x) ≤ 1/(1+x)   (lower)
1 + x ≤ exp(x)  ≤ 1/(1-x)   (upper)
```

on the interval `[0, 1)`. This is a foundational identity in numerical analysis / probability theory that has no compact packaged statement in Mathlib. Recommended as a coordinated single PR with both lemmas + a third sandwich theorem that bundles them.

### 1.4 The headline equivalent reformulation pair

**`OneAddDivPowLeExp_PR.lean` + `OneAddPowLeExpMul_PR.lean`** are mathematically equivalent (substitute `y := n·x` to swap forms). Submit one, mention the other in the docstring as an "equivalent reformulation already proved" — single PR.

---

## 2. Recommended submission order

Per `mathlib_pr_drafts/INDEX.md` §3:

1. **`MatrixExp_DetTrace_DimOne_PR.lean`** — closes literal Mathlib TODO. **Highest priority**.
2. **`LogTwoLowerBound_PR.lean`** — smallest, simplest sanity-check submission.
3. **`SpectralGapMassFormula_PR.lean`** — natural addition to `Real.log` library.
4. **`OneSubInvLeLog_PR.lean`** — dual to existing `Real.log_le_sub_one_of_pos`.
5. **`ExpTangentLineBound_PR.lean`** — generalises existing `add_one_le_exp`.
6. **`MulExpNegLeInvE_PR.lean`** — explicit form of standard concentration bound.
7. **Coordinated sandwich PR**: `ExpNegLeOneDivAddOne_PR.lean` + `ExpLeOneDivOneSub_PR.lean`.
8. **`BrydgesKennedyBound_PR.lean`** — Mayer cluster expansion.
9. **Coordinated equivalent-pair PR**: `OneAddDivPowLeExp_PR.lean` + `OneAddPowLeExpMul_PR.lean` (mention #2 in docstring of #1's PR).
10. **`KlarnerBFSBound_PR.lean`** — combinatorial.

Total: **9-10 PRs** (depending on how the coordinated pairs are packaged).

---

## 3. Pre-PR checklist (apply per file)

- [ ] `lake build` against current Mathlib master with no errors.
- [ ] `#lint` clean.
- [ ] `#print axioms <theorem_name>` shows only `propext`, `Classical.choice`, `Quot.sound` (Mathlib-acceptable axioms).
- [ ] Search Mathlib for namespace collision: `grep -r "<theorem_name>" Mathlib/` to ensure not already added.
- [ ] Update import to most-specific Mathlib module (avoid `Mathlib` blanket import).
- [ ] Match Mathlib naming convention: snake_case, `Real.` namespace for real-valued, `Nat.` for nat-valued.
- [ ] Match Mathlib docstring style: `/-- **Theorem name** ... -/`.
- [ ] Run `linter` and address every flag.

---

## 4. Status (2026-04-25)

| File | Workspace produced | `lake build` verified | Mathlib namespace collision checked |
|---|---|---|---|
| `MatrixExp_DetTrace_DimOne_PR.lean` | Yes | **No** | No |
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

**No file is ready for PR submission until the corresponding row above shows three "Yes".**

---

## 5. Honest meta-caveat

These 12 files were drafted inside an **LLM-assisted Cowork session without access to a Mathlib build environment**. The proofs are short, elementary, and conceptually verified by the author and the agent, but standard pitfalls are not yet ruled out:

- A lemma name might exist in Mathlib master under a different signature.
- A tactic (e.g. `pow_le_pow_left`, `lt_div_iff₀`) may have been renamed in version drift.
- The exact axiom-status of `Real.exp_nat_mul`, `Real.log_inv`, and similar combination lemmas should be confirmed.

**Treat each file as a math sketch + Lean draft, not as a verified contribution.** The path from this folder to merged Mathlib PRs is:

> clone Mathlib master → drop file in → `lake build` → fix tactic-name drift → run `#lint` → open PR.

Each individual proof is 2-5 lines; expect ~30 min per file of polishing in a real build environment.

---

## 6. Relationship to `MATHLIB_GAPS.md`

| Direction | Document | Subject |
|---|---|---|
| **Down** (Mathlib → us) | `MATHLIB_GAPS.md` | What this project needs from Mathlib but Mathlib doesn't yet have. 5 concrete F3-closure gaps. |
| **Up** (us → Mathlib) | This document | What this project has factored out and would contribute to Mathlib. 17 files queued. |

### 6.1 Explicit cross-reference (Phase 422 audit)

Of the 5 gaps in `MATHLIB_GAPS.md`, **2 now have PR-ready drafts** in this collection:

| `MATHLIB_GAPS.md` # | Gap name | PR-ready file | Status |
|---|---|---|---|
| #1 | BFS-tree lattice animal count bound | `KlarnerBFSBound_PR.lean` | Draft, not built |
| #2 | Haar product factorisation | (older `PiDisjointFactorisation.lean` exists, not in 17-file set) | Older draft only |
| #3 | Möbius / partition lattice inversion | (older `PartitionLatticeMobius.lean` exists, not in 17-file set) | Older draft only |
| #4 | Brydges–Kennedy forest estimate | `BrydgesKennedyBound_PR.lean` (foundational per-edge ingredient only) | Partial draft |
| #5 | Spanning-tree count via Cayley | (none — `MATHLIB_GAPS.md` recommends skip) | Skipped |

After **#1** and the per-edge ingredient of **#4** land upstream, the corresponding `MATHLIB_GAPS.md` rows will close. The remaining 12 PR-ready files in this collection are **NOT** listed in `MATHLIB_GAPS.md` because they are downstream-consumer lemmas (`Real.exp` / `Real.log` / hyperbolic / numerical / matrix bounds) factored out of the project's analysis chain, not from F3 specifically.

### 6.2 Flow

After all eligible files in this collection land upstream:

- `MATHLIB_GAPS.md` shrinks from 5 → 3 (or 5 → 2 if Brydges-Kennedy full estimate also lands).
- `MATHLIB_PRS_OVERVIEW.md` shrinks from 17 → 0 (this document becomes archive).
- The project's bidirectional Mathlib relationship simplifies to "consumer" only.

---

*This document is the project's outward-facing contribution catalog. Cross-references: `mathlib_pr_drafts/INDEX.md`, `COWORK_FINDINGS.md` Finding 020, `FINAL_HANDOFF.md` post-Phase 410 addendum, `STATE_OF_THE_PROJECT.md` post-Phase 410 addendum.*
