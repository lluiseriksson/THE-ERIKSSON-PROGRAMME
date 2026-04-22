# THE ERIKSSON PROGRAMME

> **A Lean 4 / Mathlib formalization of the Yang–Mills mass gap.**
> Oracle-clean core · transparent frontier · explicit path to 100 % unconditional.

![Lean](https://img.shields.io/badge/Lean-4.29.0--rc6-0052CC)
![Mathlib](https://img.shields.io/badge/Mathlib-master-5e81ac)
![ClayCore oracles](https://img.shields.io/badge/ClayCore%20oracles-propext%20%7C%20Classical.choice%20%7C%20Quot.sound-2e7d32)
![Unconditionality](https://img.shields.io/badge/unconditional-40%25-orange)
![Front](https://img.shields.io/badge/front-L2.6%20step%202-informational)

---

## TL;DR

- **What works today, oracle-clean.** The L1 layer — Haar measure on `SU(N)` + Schur orthogonality on matrix entries, **through L2.6 step 1c** — type-checks against only `[propext, Classical.choice, Quot.sound]`. Every diagonal entry of a Haar-distributed `U ∈ SU(N)` now has `∫ |U_ij|² dμ = 1/N` as a Lean theorem.
- **What's next.** L2.6 step 2 packages full matrix-entry Schur orthogonality by combining step 1b (off-diagonals vanish) with step 1c (diagonals `= 1/N`). After that, step 3 goes to irreducible-character orthogonality via Peter–Weyl.
- **What's not yet unconditional.** The L3 mass-gap conclusion still depends on declared physics hypotheses — Balaban RG, Dirichlet / Bakry–Émery, Lie-derivative regularity, Stroock–Zegarliński LSI. Every one of them is named in `AXIOM_FRONTIER.md`. The unconditionality roadmap retires them one at a time.

This repository is **not** a finished proof of the Clay Yang–Mills mass gap. It is a structured, transparent push toward one, where every remaining assumption is *named* and the core machinery is held to a strict three-oracle budget. The `#print axioms` trace is the ground truth.

---

## At a glance

| | |
|---|---|
| **Target** | Clay Millennium Prize — existence of quantum Yang–Mills on ℝ⁴ with a positive mass gap |
| **Language** | Lean 4 (`leanprover/lean4:v4.29.0-rc6`) + Mathlib (`master`) |
| **Core discipline** | `YangMills/ClayCore/` prints only `[propext, Classical.choice, Quot.sound]` |
| **Current front** | **L2.6 step 2** — full matrix-entry Schur orthogonality `∫ U_ij · conj U_kl dμ = δ_ik δ_jl / N` |
| **Last closed** | **L2.6 step 1c** — diagonal Schur integral `∫ \|U_ij\|² dμ = 1/N` (commit `d22a6b8`) |
| **Last updated** | 2026-04-22 |

---

## Table of contents

1. [What this repository is](#1-what-this-repository-is)
2. [Progress toward 100 % unconditional](#2-progress-toward-100--unconditional)
3. [Recently closed](#3-recently-closed)
4. [Oracle discipline](#4-oracle-discipline--scope-of-the-no-sorry-claim)
5. [Current front — L2.6 step 2](#5-current-front--l26-step-2)
6. [Milestone ladder](#6-milestone-ladder)
7. [Repository layout](#7-repository-layout)
8. [Building & verifying](#8-building--verifying)
9. [How to contribute](#9-how-to-contribute)
10. [Honesty note](#10-honesty-note)

---

## 1. What this repository is

The repository formalizes, in Lean 4 + Mathlib, the chain of analytic and representation-theoretic facts used in a Yang–Mills mass-gap argument. The long-term target is the Clay Millennium Prize problem: proving the existence of a quantum Yang–Mills theory on ℝ⁴ with a positive mass gap.

The formal content is split into three layers:

- **L1 — Haar + Schur on `SU(N)`.** The base layer. Haar probability measure, left/right invariance, and Schur orthogonality for matrix coefficients of unitary irreducible representations. This is the layer where the current front (L2.6 step 2) lives.
- **L2 — Character expansion and cluster decay.** Wilson-loop expansions, polymer / Mayer expansions, exponential cluster bounds. Builds on L1 but is structurally separable.
- **L3 — Mass-gap conclusion.** The final logical step: from L1 + L2 (plus conditional physical hypotheses collected as `CharacterExpansionData` and `h_correlator`) to a two-point-function bound giving a mass gap.

The conditional structure is intentional. Every physics hypothesis that is *not* fully Lean-checked yet is surfaced as a named `structure` field or a named `axiom`, and lives in `AXIOM_FRONTIER.md`. L3's final statement takes those as hypotheses; the goal of the unconditionality roadmap is to discharge them one by one inside L1–L2.

---

## 2. Progress toward 100 % unconditional

The following bars measure *closed, oracle-clean Lean artifacts* against the layer's planned total. Percentages move **only** when a named frontier entry is retired from `AXIOM_FRONTIER.md` or `SORRY_FRONTIER.md` — never by decree.

```
L1    Haar + Schur scaffolding on SU(N)         ▰▰▰▰▰▰▰▰▰▰   98 %
L2.4  Structural Schur / Haar scaffolding       ▰▰▰▰▰▰▰▰▰▰  100 %
L2.5  Frobenius trace bound  (∑ ∫ |U_ii|² ≤ N)  ▰▰▰▰▰▰▰▰▰▰  100 %
L2.6  Schur orthogonality on SU(N)              ▰▰▰▰▰▰▰▰▰▱   85 %
L2    Character expansion + cluster decay       ▰▰▰▰▱▱▱▱▱▱   42 %
L3    Mass-gap conclusion (with hypotheses)     ▰▰▱▱▱▱▱▱▱▱   22 %
──────────────────────────────────────────────────────────────
      OVERALL unconditionality                  ▰▰▰▰▱▱▱▱▱▱   40 %
```

**Change since previous snapshot (2026-04-22 morning).** L2.6 step 1c closed at commit `d22a6b8`, moving L1 92 → 98, L2.6 68 → 85, L2 38 → 42, and overall **34 → 40**. All bumps are backed by an oracle-clean `#print axioms` trace (see §3).

**How the overall number is computed.** Each layer's percentage is the ratio of oracle-clean, sorry-free Lean artifacts to that layer's planned artifact count in `UNCONDITIONALITY_ROADMAP.md`. The overall number weights the layers by their total frontier-entry count in `AXIOM_FRONTIER.md` + `SORRY_FRONTIER.md`. The metric is **monotone by design**: it cannot go up except by retiring a named frontier entry, and it cannot go down unless a previously closed lemma regresses in CI.

**What this number is not.** It is not a confidence score in the mass-gap result, and it is not the ratio of filled theorems in the whole repo. It is specifically *"how much of the declared hypothesis set has been discharged in Lean."*

**Next expected movement.** When L2.6 step 2 closes, the L2.6 row moves 85 → ~92 and the overall number moves 40 → ~42. When L2.6 step 3 closes (Peter–Weyl character orthogonality), L1 completes at 100 %, L2.6 completes at 100 %, and the overall number crosses 50 %.

---

## 3. Recently closed

### L2.6 step 1c — diagonal Schur integral (commit `d22a6b8`, 2026-04-22)

**Theorem.** `YangMills.ClayCore.sunHaarProb_entry_normSq_eq_inv_N` in `YangMills/ClayCore/SchurEntryDiagonal.lean`:

    ∀ i j : Fin N,
      ∫ U, U.val i j · star (U.val i j) ∂(sunHaarProb N) = 1 / (N : ℂ)

**Oracle trace (verified in CI).**

    #print axioms YangMills.ClayCore.sunHaarProb_entry_normSq_eq_inv_N
    ⟶ [propext, Classical.choice, Quot.sound]

**Proof architecture (3 rounds, 298 lines, 0 sorry, 0 new axioms).**

1. **`rotPairMat i j`** — the quarter-rotation matrix with the 2×2 block `[[0, −1], [1, 0]]` on rows/columns `(i, j)` and identity elsewhere. Unitarity is proven entry-by-entry.
2. **`rotPairSU hij`** — `rotPairMat` packaged as an element of `Matrix.specialUnitaryGroup (Fin N) ℂ` after proving `det = 1` via `rotPairMat_eq_diag_mul_perm` + `Matrix.det_permutation` + `Equiv.Perm.sign_swap`.
3. **`sunHaarProb_entry_normSq_eq_inv_N`** — combines
   - the row-squared-sum identity `∑_k U_ik · star U_ik = 1` (from `U * star U = I`, diagonal entry);
   - column symmetry `∫ |U_ij|² dμ = ∫ |U_ii|² dμ` via right-invariance of Haar under `rotPairSU`;
   - `N · ∫ |U_11|² dμ = ∫ ∑_k |U_1k|² dμ = 1`, divide by `N`.

**Impact on the unconditionality ladder.** Together with L2.6 step 1b (off-diagonals vanish, commit `0143c37`), this is the analytic content of matrix-entry Schur orthogonality on `SU(N)`. L2.6 step 2 is now a packaging step.

---

## 4. Oracle discipline — scope of the "no sorry" claim

The `YangMills/ClayCore/` subtree — the L1 + central L2 chain through Schur orthogonality and the trace/Frobenius bound — is held to a strict oracle budget:

    #print axioms <theorem>  ⟹  [propext, Classical.choice, Quot.sound]

No project-specific `axiom`, no `sorry`, nothing beyond Lean's three foundational oracles. Any commit that enlarges the axiom print of a ClayCore theorem is rejected.

**This discipline is scoped to `YangMills/ClayCore/` only.** Peripheral modules that model Balaban RG, Dirichlet / Bakry–Émery, Lie-derivative regularity, and Stroock–Zegarliński-type LSI inputs still carry conditional `axiom` declarations and a small number of `sorry`s. These are the declared physics hypotheses of L3, each tracked individually in `AXIOM_FRONTIER.md` and `SORRY_FRONTIER.md`. The unconditionality roadmap is precisely the plan to eliminate those peripheral entries one at a time, starting from the L1 end.

So: the *core* is oracle-clean today. The *whole project* is not — and we say so out in the open, file by file.

---

## 5. Current front — L2.6 step 2

**Target statement.** For `N ≥ 1` and any indices `(i, j, k, l)` of a Haar-distributed `U ∈ SU(N)`,

    ∫_{SU(N)} U_ij · star(U_kl) dμ_Haar = (1 / N) · δ_{ik} · δ_{jl}

i.e. the full matrix-entry Schur orthogonality identity on `SU(N)`.

### 5.1 Why this is the right next brick

- **Downstream.** This is the statement every L2 cluster-expansion bound expects to cite. Until step 2 lands, any expansion downstream carries an unknown normalization constant on the two-point function.
- **Upstream.** Step 1b (commit `0143c37`) and step 1c (commit `d22a6b8`) between them already establish the four cases — diagonal `(i, j) = (k, l)` gives `1/N`; the three off-diagonal cases all vanish. Step 2 is the packaging: a single theorem that case-analyzes and invokes the right sub-lemma.

### 5.2 Proof strategy in Lean

The target file is `YangMills/ClayCore/SchurEntryOrthogonality.lean`. One theorem, essentially one `match` on the four cases:

1. `i = k ∧ j = l` → apply `sunHaarProb_entry_normSq_eq_inv_N` (step 1c) and simplify `δ_{ii} · δ_{jj} = 1`.
2. `i = k ∧ j ≠ l` → apply the column-orthogonality sub-lemma of step 1b.
3. `i ≠ k ∧ j = l` → apply the row-orthogonality sub-lemma of step 1b.
4. `i ≠ k ∧ j ≠ l` → apply the general off-diagonal sub-lemma of step 1b (entry version).

### 5.3 Oracle budget for step 2

Step 2 calls only theorems already committed and oracle-clean. It therefore lands inside the `YangMills/ClayCore/` oracle budget by construction, provided no Mathlib extension beyond what step 1b and step 1c already import is needed. Expected: hours, not days.

### 5.4 What step 2 does *not* do

Step 2 does not prove irreducible-character orthogonality `∫ χ_λ · conj χ_μ dμ = δ_{λμ}`. That is L2.6 step 3, and it goes through the Peter–Weyl decomposition. It also does not touch any L3 physics hypothesis.

---

## 6. Milestone ladder

Every row is a Lean-checkable statement, not a paper-level claim. Acceptance criterion for every "DONE" row: `#print axioms` prints only `[propext, Classical.choice, Quot.sound]` and no `sorry` appears in the file.

| # | Milestone | Lean location | Status | Acceptance |
| --- | --- | --- | --- | --- |
| 1 | L2.4 — Structural Schur / Haar scaffolding on SU(N) | `YangMills/ClayCore/Schur*.lean` | DONE | oracle-clean |
| 2 | L2.5 — `∑_i ∫ \|U_ii\|² dμ ≤ N` on SU(N) | `SchurL25.lean` | DONE | oracle-clean |
| 3 | L2.6 step 0 — Diagonal phase element of SU(N) | `SchurDiagPhase.lean` | DONE | oracle-clean |
| 4 | L2.6 step 1a — Antisymmetric two-site angle | `SchurTwoSitePhase.lean` | DONE | oracle-clean |
| 5 | L2.6 step 1b-i — `exp(I·π) = −1` for the two-site phase | `SchurTwoSitePhase.lean` | DONE | oracle-clean |
| 6 | L2.6 step 1b-ii — Off-diagonal entry integral vanishes | `SchurEntryOffDiag.lean` | DONE | oracle-clean |
| 7 | L2.6 step 1b (column + general) — Off-diagonal Schur orthogonality | `SchurEntryOffDiag.lean` | DONE | oracle-clean (commit `0143c37`) |
| 8 | L2.6 step 1c — Diagonal Schur integral `∫ \|U_ij\|² dμ = 1/N` | `SchurEntryDiagonal.lean` | **DONE** | **oracle-clean (commit `d22a6b8`, 2026-04-22)** |
| 9 | **L2.6 step 2 — Full matrix-entry Schur orthogonality** | **`SchurEntryOrthogonality.lean`** | **IN PROGRESS** | oracle-clean; combines 1b + 1c by case analysis |
| 10 | L2.6 step 3 — Irreducible-character orthogonality on SU(N) | TBD (Peter–Weyl path) | QUEUED | oracle-clean; Peter–Weyl decomposition |
| 11 | L2 — Cluster expansion bounds | `CharacterExpansion.lean` + cluster | PARTIAL | retires cluster-axiom entries |
| 12 | L3 — Mass-gap conclusion theorem | L3 top file | CONDITIONAL | retires L3 axioms one-by-one |

The canonical, always-up-to-date version of this table is maintained in `UNCONDITIONALITY_ROADMAP.md`.

---

## 7. Repository layout

    YangMills/
      ClayCore/                    ← oracle-clean core (L1 + central L2)
        SchurDiagPhase.lean        ← L2.6 step 0
        SchurTwoSitePhase.lean     ← L2.6 step 1a / 1b-i
        SchurOffDiagonal.lean
        SchurEntryOffDiag.lean     ← L2.6 step 1b (column + general)
        SchurEntryDiagonal.lean    ← L2.6 step 1c  CLOSED (commit d22a6b8)
        SchurEntryOrthogonality.lean ← L2.6 step 2  (current front)
        SchurL25.lean              ← L2.5 closed
        SchurNormSquared.lean
        SchurZeroMean.lean
        SchurPhysicalBridge.lean
        CharacterExpansion.lean
        …                          ← Wilson / Cluster / Balaban / Mayer machinery
      (peripheral L3 modules: Balaban, Dirichlet, LieDeriv, Hille–Yosida,
       Bakry–Émery, Stroock–Zegarliński — carry declared axioms + a small
       number of sorries tracked in AXIOM_FRONTIER.md and SORRY_FRONTIER.md)
    docs/
    papers/
    registry/
    scripts/
    dashboard/
    README.md                      ← this file
    AXIOM_FRONTIER.md
    SORRY_FRONTIER.md
    UNCONDITIONALITY_ROADMAP.md
    PETER_WEYL_ROADMAP.md
    STATE_OF_THE_PROJECT.md
    ROADMAP.md / ROADMAP_MASTER.md
    HYPOTHESIS_FRONTIER.md
    DECISIONS.md
    CONTRIBUTING.md
    AI_ONBOARDING.md

---

## 8. Building & verifying

    lake update
    lake build YangMills.ClayCore

To verify the oracle budget of a specific theorem, add at the end of any ClayCore file:

    #print axioms your_theorem_name
    -- expected: [propext, Classical.choice, Quot.sound]

CI refuses a `YangMills/ClayCore/` commit que imprima otro axioma.

Example trace for the most recently closed core theorem:

    #print axioms YangMills.ClayCore.sunHaarProb_entry_normSq_eq_inv_N
    ⟶ [propext, Classical.choice, Quot.sound]

---

## 9. How to contribute

1. Read `AI_ONBOARDING.md` and `CONTRIBUTING.md`.
2. Pick an entry from `AXIOM_FRONTIER.md` or the current front (`SchurEntryOrthogonality.lean`).
3. Keep `YangMills/ClayCore/` oracle-clean. Land physics hypotheses in peripheral modules with a *named* `axiom` declaration and a matching row in `AXIOM_FRONTIER.md`.
4. Open a PR with a `#print axioms` trace for every theorem added to ClayCore.
5. If your PR retires a frontier entry, delete the entry from `AXIOM_FRONTIER.md` (or `SORRY_FRONTIER.md`) in the same commit, and bump the relevant bar in §2 of this README.

---

## 10. Honesty note

This project will not be considered a full proof of the Clay Yang–Mills mass gap until `AXIOM_FRONTIER.md` is empty and `SORRY_FRONTIER.md` is empty at the same commit, and L3's top theorem `#print axioms`-prints only `[propext, Classical.choice, Quot.sound]`. We are not there yet.

L2.6 step 1c (commit `d22a6b8`) is one rung on that ladder — a concrete, oracle-clean one. L2.6 step 2 is the next. Every milestone in this README is stated with its exact status and a pointer to the file where it lives, so that any reader can check the gap between claim and proof themselves.

If you spot a gap between a claim and a proof here, open an issue. **Transparency over polish.**
