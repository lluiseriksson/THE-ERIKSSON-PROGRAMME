# THE ERIKSSON PROGRAMME

> **A Lean 4 / Mathlib formalization of the Yang–Mills mass gap.**
> Oracle-clean core · transparent frontier · explicit path to 100 % unconditional.

![Lean](https://img.shields.io/badge/Lean-4.29.0--rc6-0052CC)
![Mathlib](https://img.shields.io/badge/Mathlib-master-5e81ac)
![ClayCore oracles](https://img.shields.io/badge/ClayCore%20oracles-propext%20%7C%20Classical.choice%20%7C%20Quot.sound-2e7d32)
![Unconditionality](https://img.shields.io/badge/unconditional-50%25-yellow)
![Front](https://img.shields.io/badge/front-L2.6%20step%203%20(Peter%E2%80%93Weyl)-informational)

---

## TL;DR

- **What works today, oracle-clean.** The L1 layer — Haar measure on `SU(N)` + Schur orthogonality on matrix entries — is closed, and **L2.6's main target has just landed**: the character inner product `⟨χ_fund, χ_fund⟩ = ∫_{SU(N)} |tr U|² dμ_Haar = 1` is a Lean theorem with `#print axioms` ⟹ `[propext, Classical.choice, Quot.sound]`. This is the statement every downstream cluster-expansion bound actually cites.
- **What's next.** L2.6 step 3 — extend the character inner-product identity from the fundamental representation to arbitrary irreducible representations, via the Peter–Weyl decomposition. That retires the final internal dependency of the L1 ↦ L2 bridge on a specific irrep.
- **What's not yet unconditional.** The L3 mass-gap conclusion still depends on declared physics hypotheses — Balaban RG, Dirichlet / Bakry–Émery, Lie-derivative regularity, Stroock–Zegarliński LSI. Every one of them is named in `AXIOM_FRONTIER.md`. The unconditionality roadmap retires them one at a time.

This repository is **not** a finished proof of the Clay Yang–Mills mass gap. It is a structured, transparent push toward one, where every remaining assumption is *named* and the core machinery is held to a strict three-oracle budget. The `#print axioms` trace is the ground truth.

---

## At a glance

| | |
|---|---|
| **Target** | Clay Millennium Prize — existence of quantum Yang–Mills on ℝ⁴ with a positive mass gap |
| **Language** | Lean 4 (`leanprover/lean4:v4.29.0-rc6`) + Mathlib (`master`) |
| **Core discipline** | `YangMills/ClayCore/` prints only `[propext, Classical.choice, Quot.sound]` |
| **Current front** | **L2.6 step 3** — Peter–Weyl: extend character inner product from fundamental to arbitrary irreps |
| **Last closed** | **L2.6 step 3b** — bilinear trace-power vanishing `∫ (tr U)^j · star((tr U))^k dμ_Haar = 0` on SU(N_c) when `k ≤ j` and `N_c ∤ (j - k)` (commit `70403d1`) |
| **Last updated** | 2026-04-22 |

---

## Table of contents

1. [What this repository is](#1-what-this-repository-is)
2. [Progress toward 100 % unconditional](#2-progress-toward-100--unconditional)
3. [Recently closed](#3-recently-closed--l26-main-target-character-inner-product--1)
4. [Oracle discipline](#4-oracle-discipline--scope-of-the-no-sorry-claim)
5. [Current front — L2.6 step 3 (Peter–Weyl)](#5-current-front--l26-step-3-peterweyl)
6. [Milestone ladder](#6-milestone-ladder)
7. [Repository layout](#7-repository-layout)
8. [Building & verifying](#8-building--verifying)
9. [How to contribute](#9-how-to-contribute)
10. [Honesty note](#10-honesty-note)

---

## 1. What this repository is

The repository formalizes, in Lean 4 + Mathlib, the chain of analytic and representation-theoretic facts used in a Yang–Mills mass-gap argument. The long-term target is the Clay Millennium Prize problem: proving the existence of a quantum Yang–Mills theory on ℝ⁴ with a positive mass gap.

The formal content is split into three layers:

- **L1 — Haar + Schur on `SU(N)`.** The base layer. Haar probability measure, left/right invariance, Schur orthogonality for matrix coefficients, and the character inner product for the fundamental representation. This is now closed for the fundamental representation as of L2.6's main target.
- **L2 — Character expansion and cluster decay.** Wilson-loop expansions, polymer / Mayer expansions, exponential cluster bounds. Builds on L1 but is structurally separable. The current front (L2.6 step 3 / Peter–Weyl) is the last remaining internal L1→L2 bridge.
- **L3 — Mass-gap conclusion.** The final logical step: from L1 + L2 (plus conditional physical hypotheses collected as `CharacterExpansionData` and `h_correlator`) to a two-point-function bound giving a mass gap.

The conditional structure is intentional. Every physics hypothesis that is *not* fully Lean-checked yet is surfaced as a named `structure` field or a named `axiom`, and lives in `AXIOM_FRONTIER.md`. L3's final statement takes those as hypotheses; the goal of the unconditionality roadmap is to discharge them one by one inside L1–L2.

---

## 2. Progress toward 100 % unconditional

The following bars measure *closed, oracle-clean Lean artifacts* against the layer's planned total. Percentages move **only** when a named frontier entry is retired from `AXIOM_FRONTIER.md` or `SORRY_FRONTIER.md` — never by decree.

```
L1    Haar + Schur scaffolding on SU(N)         ▰▰▰▰▰▰▰▰▰▰   98 %
L2.4  Structural Schur / Haar scaffolding       ▰▰▰▰▰▰▰▰▰▰  100 %
L2.5  Frobenius trace bound  (∑ ∫ |U_ii|² ≤ N)  ▰▰▰▰▰▰▰▰▰▰  100 %
L2.6  Character inner product on SU(N)          ▰▰▰▰▰▰▰▰▰▱   97 %
L2    Character expansion + cluster decay       ▰▰▰▰▰▱▱▱▱▱   50 %
L3    Mass-gap conclusion (with hypotheses)     ▰▰▱▱▱▱▱▱▱▱   22 %
──────────────────────────────────────────────────────────────
      OVERALL unconditionality                  ▰▰▰▰▰▱▱▱▱▱   50 %
```

**Change since previous snapshot (2026-04-22 morning).** L2.6's main target — the character inner product `∫ |tr U|² dμ = 1` — closed at commit `f9ec5e9`, moving L2.6 85 → 95, L2 42 → 50, and overall **40 → 48**. This is the biggest single jump since we began tracking. The bump is backed by an oracle-clean `#print axioms` trace (see §3).

**Follow-up closure (2026-04-22 afternoon).** L2.6 step 2 — the full matrix-entry Schur orthogonality `∫_{SU(N)} U_{ij} · star(U_{kl}) dμ_Haar = δ_{ik} δ_{jl} / N` — closed at commit `95175f3`, moving L2.6 95 → 97 and overall **48 → 50**. This packages the four-case analysis previously deferred as "non-blocking" into a single clean theorem `sunHaarProb_entry_orthogonality` in `SchurEntryFull.lean`, combining step 1b (off-diagonal = 0) and step 1c (diagonal = 1/N) via one `by_cases` on `(i = k ∧ j = l)`. Oracle-clean `[propext, Classical.choice, Quot.sound]`.

**Follow-up closure (2026-04-22 evening).** L2.6 step 3b — the bilinear trace-power vanishing `∫_{SU(N_c)} (tr U)^j · (star (tr U))^k dμ_Haar = 0` when `k ≤ j` and `N_c ∤ (j - k)` — closed at commit `70403d1` in `SchurTracePowBilinear.lean`. This completes the {3a, 3b, 3c} sidecar triplet: 3a handles the pure power `(tr U)^k`, 3c handles the power sum `tr(U^k)`, and 3b now handles the mixed bilinear `(tr U)^j · star(tr U)^k` — the form that actually appears inside character inner products `⟨χ_{V^{⊗j}}, χ_{V^{⊗k}}⟩`. Same central-element argument extended to `ω^{j-k} ≠ 1` (with `j ≥ k` and `N_c ∤ (j-k)`). Seven new theorems total: the helper `rootOfUnity_pow_mul_star_pow`, the transport lemma `trace_scalarCenter_mul_pow_bilinear`, the MAIN `sunHaarProb_trace_pow_bilinear_integral_zero` plus a prime variant with `star` applied to the whole power, two low-degree corollaries (`j=2,k=1` requiring `N_c ≥ 2`; `j=3,k=1` requiring `N_c ≥ 3`), and a non-triviality witness at `U = 1` evaluating to `(N_c)^{j+k}`. Oracle-clean `[propext, Classical.choice, Quot.sound]` for all seven. L2.6 bar unchanged at 97 %; step 3 proper (arbitrary irreps, not just scalar traces and their bilinear products) remains open.

**Strategic note on the step 1c → main-target transition.** The plan previously anticipated a separate "step 2" that packages matrix-entry Schur orthogonality `∫ U_ij · star(U_kl) dμ = (1/N) δ_ik δ_jl`. When the parallel instance inspected the downstream L2 call sites, the statement actually consumed is the **character-level** one: `∫ |tr U|² dμ = 1`. That follows from L2.5's trace decomposition `∫ tr U · star(tr U) = ∑ᵢ ∫ |Uᵢᵢ|²` plus step 1c's diagonal identity `∫ |Uᵢᵢ|² = 1/N`. We therefore went directly to the character-level consumer. Full matrix-entry packaging has now been landed anyway (step 2, commit `95175f3`, theorem `sunHaarProb_entry_orthogonality` in `SchurEntryFull.lean`) — it was not on the critical path, but closing it removes a standing TODO and keeps the `δ_{ik} δ_{jl} / N` form available as public API for any irrep-generalization downstream consumer that prefers it over the character-level reduction.

**How the overall number is computed.** Each layer's percentage is the ratio of oracle-clean, sorry-free Lean artifacts to that layer's planned artifact count in `UNCONDITIONALITY_ROADMAP.md`. The overall number weights the layers by their total frontier-entry count in `AXIOM_FRONTIER.md` + `SORRY_FRONTIER.md`. The metric is **monotone by design**: it cannot go up except by retiring a named frontier entry, and it cannot go down unless a previously closed lemma regresses in CI.

**What this number is not.** It is not a confidence score in the mass-gap result, and it is not the ratio of filled theorems in the whole repo. It is specifically *"how much of the declared hypothesis set has been discharged in Lean."*

**Next expected movement.** When L2.6 step 3 closes (Peter–Weyl character orthogonality), L1 completes at 100 %, L2.6 completes at 100 %, L2 bumps to ~59 %, and the overall number crosses 54 %.

---

## 3. Recently closed — L2.6 main target (character inner product = 1)

### L2.6 main target — character inner product for the fundamental representation (commit `f9ec5e9`, 2026-04-22)

**Theorem.** `YangMills.ClayCore.sunHaarProb_trace_normSq_integral_eq_one` in `YangMills/ClayCore/SchurL26.lean`:

    ∫_{SU(N)} Complex.normSq (U.val.trace) ∂(sunHaarProb N) = 1

Equivalently, `⟨χ_fund, χ_fund⟩_{L²(SU(N), μ_Haar)} = 1`, i.e. the fundamental character has unit `L²` norm against Haar measure.

**Oracle trace (verified in CI).**

    #print axioms YangMills.ClayCore.sunHaarProb_trace_normSq_integral_eq_one
    ⟶ [propext, Classical.choice, Quot.sound]

    #print axioms YangMills.ClayCore.diag_normSq_integral_eq_inv_N
    ⟶ [propext, Classical.choice, Quot.sound]

**Proof architecture (1 new file, 2 theorems, 0 sorry, 0 new axioms).**

1. **Trace decomposition (L2.5).** `integral_trace_mul_conj_trace_eq_sum` expands `∫ tr U · star(tr U) dμ = ∑ᵢⱼ ∫ Uᵢᵢ · star Uⱼⱼ dμ`. The off-diagonal sum collapses to the diagonal via `SchurOffDiagonal.sunHaarProb_offdiag_integral_zero` (two-site phase argument).
2. **Diagonal identity (step 1c).** `sunHaarProb_entry_normSq_eq_inv_N` gives `∫ |Uᵢᵢ|² dμ = 1/N` for every diagonal entry.
3. **New bridge lemma `diag_normSq_integral_eq_inv_N`.** Rewrites the diagonal integrand `Uᵢᵢ · star Uᵢᵢ` as `(normSq Uᵢᵢ : ℂ)` and reduces to step 1c.
4. **`sunHaarProb_trace_normSq_integral_eq_one`.** Sums the diagonal, gets `N · (1/N) = 1`, and pulls the `ofReal` out of the integral by the `integral_congr_ae` + `integral_ofReal` pattern (same template as `SchurL25.diag_integral_ofReal`).

**Impact on the unconditionality ladder.** This is the first L1 → L2 interface statement that L2's cluster expansion actually consumes. It closes L2.6 at the fundamental-representation level. The only remaining L2.6 work is generalization to arbitrary irreps via Peter–Weyl (step 3).

---

## 4. Oracle discipline — scope of the "no sorry" claim

The `YangMills/ClayCore/` subtree — the L1 + central L2 chain through Schur orthogonality, the trace/Frobenius bound, and now the character inner product — is held to a strict oracle budget:

    #print axioms <theorem>  ⟹  [propext, Classical.choice, Quot.sound]

No project-specific `axiom`, no `sorry`, nothing beyond Lean's three foundational oracles. Any commit that enlarges the axiom print of a ClayCore theorem is rejected.

**This discipline is scoped to `YangMills/ClayCore/` only.** Peripheral modules that model Balaban RG, Dirichlet / Bakry–Émery, Lie-derivative regularity, and Stroock–Zegarliński-type LSI inputs still carry conditional `axiom` declarations and a small number of `sorry`s. These are the declared physics hypotheses of L3, each tracked individually in `AXIOM_FRONTIER.md` and `SORRY_FRONTIER.md`. The unconditionality roadmap is precisely the plan to eliminate those peripheral entries one at a time, starting from the L1 end.

So: the *core* is oracle-clean today. The *whole project* is not — and we say so out in the open, file by file.

---

## 5. Current front — L2.6 step 3 (Peter–Weyl)

**Target statement.** Extend the character inner-product identity from the fundamental representation to an arbitrary irreducible representation `ρ: SU(N) → GL(V_ρ)` of `SU(N)`:

    ⟨χ_ρ, χ_ρ⟩_{L²(SU(N), μ_Haar)}  =  ∫_{SU(N)} |tr ρ(U)|² dμ_Haar  =  1

More generally, for `ρ` and `σ` non-isomorphic irreps,

    ⟨χ_ρ, χ_σ⟩  =  0.

**Sidecars already landed: L2.6 steps 3a + 3b + 3c.** `YangMills/ClayCore/SchurTracePow.lean` (commit `3c7a957`) proves `∫_{SU(N_c)} (tr U)^k dμ_Haar = 0` whenever `N_c ∤ k`. Representation-theoretically this is the trivial-character component of Peter–Weyl restricted to scalar traces of tensor powers of the fundamental: `(tr U)^k` is the character of `(ℂ^{N_c})^{⊗ k}`, and when `N_c ∤ k` the decomposition contains no `det^{k/N_c}` factor, so no trivial summand appears. The companion file `YangMills/ClayCore/SchurTraceUPow.lean` (commit `bf321e4`) proves the parallel identity `∫_{SU(N_c)} tr(U^k) dμ_Haar = 0` for `N_c ∤ k` — the `k`-th power sum of the eigenvalues, as opposed to the `k`-th power of the first power sum. A third file `YangMills/ClayCore/SchurTracePowBilinear.lean` (commit `70403d1`) closes the *bilinear* case `∫_{SU(N_c)} (tr U)^j · (star (tr U))^k dμ_Haar = 0` whenever `k ≤ j` and `N_c ∤ (j - k)`, extending 3a's single-integrand statement to mixed products with complex conjugates — the exact form that appears inside character inner products `⟨χ_{V^{⊗j}}, χ_{V^{⊗k}}⟩` on tensor powers of the fundamental. By Newton’s identities 3a and 3c span the same subalgebra of class functions over ℚ, but as integrands each is independent; 3b adds the bilinear closure of that subalgebra. All three follow from the same central-element argument (`Ω = ω·I`), with `ω^k ≠ 1` for 3a/3c and `ω^{j-k} ≠ 1` for 3b. Step 3 proper (arbitrary irreps, not just scalar traces and their bilinear products) remains open.

### 5.1 Why this is the right next brick

- **Downstream.** L2's character-expansion bound sums over *all* irreps of `SU(N)`, not just the fundamental. Until step 3 lands, the expansion is formally constrained to the defining representation.
- **Upstream.** The main target just closed gives this identity for `ρ = fundamental`. Peter–Weyl reduces the general case to the fundamental case plus a basis-change argument over a chosen complete set of irreps.

### 5.2 Proof strategy in Lean

The intended target file is `YangMills/ClayCore/PeterWeyl.lean` (or an extension of `SchurL26.lean`). Two subgoals, in order of increasing difficulty:

1. **Finite index, structural.** Express an arbitrary irrep `ρ` of `SU(N)` as a sub-representation of a tensor power of the fundamental. Reduce character integrals over `ρ` to polynomial combinations of fundamental-trace integrals.
2. **Peter–Weyl orthogonality.** Prove `⟨χ_ρ, χ_σ⟩ = δ_{[ρ]=[σ]}` by the standard argument: matrix-element orthogonality for non-isomorphic irreps, plus a dimension count for isomorphic irreps.

Mathlib already carries large parts of the compact-group representation theory used here. The bottleneck is likely the bridge between `Matrix.specialUnitaryGroup` and Mathlib's abstract `Representation` / `Rep` types.

### 5.3 Oracle budget for step 3

Step 3 must remain inside `[propext, Classical.choice, Quot.sound]` for any theorem that lands in `YangMills/ClayCore/`. If a Mathlib Peter–Weyl dependency drags in an extra axiom, that axiom is surfaced in `AXIOM_FRONTIER.md` with a named entry and a retirement plan, rather than silently absorbed.

### 5.4 What step 3 does *not* do

Step 3 does not touch L3's physics hypotheses. It also does not prove anything about the *spectrum* of the L² character space — only the orthogonality of the characters that are already named.

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
| 8 | L2.6 step 1c — Diagonal Schur integral `∫ \|U_ij\|² dμ = 1/N` | `SchurEntryDiagonal.lean` | DONE | oracle-clean (commit `d22a6b8`, 2026-04-22) |
| 9 | **L2.6 main target — character inner product `∫ \|tr U\|² dμ = 1`** | **`SchurL26.lean`** | **DONE** | **oracle-clean (commit `f9ec5e9`, 2026-04-22)** |
| 10 | **L2.6 step 2 — full matrix-entry Schur orthogonality `∫ U_{ij}·star(U_{kl}) dμ = δ_{ik}δ_{jl}/N`** | **`SchurEntryFull.lean`** | **DONE** | **oracle-clean (commit `95175f3`, 2026-04-22)** |
| 11 | **L2.6 step 3a (sidecar) — trace-power vanishing `∫ (tr U)^k dμ = 0` for `N_c ∤ k`** | **`SchurTracePow.lean`** | **DONE** | **oracle-clean (commit `3c7a957`, 2026-04-22)** |
| 12 | **L2.6 step 3b (sidecar) — bilinear trace-power vanishing `∫ (tr U)^j · star((tr U))^k dμ = 0` for `k ≤ j`, `N_c ∤ (j-k)`** | **`SchurTracePowBilinear.lean`** | **DONE** | **oracle-clean (commit `70403d1`, 2026-04-22)** |
| 13 | **L2.6 step 3c (sidecar) — power-sum trace vanishing `∫ tr(U^k) dμ = 0` for `N_c ∤ k`** | **`SchurTraceUPow.lean`** | **DONE** | **oracle-clean (commit `bf321e4`, 2026-04-22)** |
| 14 | **L2.6 step 3 — Peter–Weyl: character orthogonality for arbitrary irreps** | **`PeterWeyl.lean`** (TBD) | **IN PROGRESS** | oracle-clean; fundamental → irrep generalization |
| 15 | L2 — Cluster expansion bounds | `CharacterExpansion.lean` + cluster | PARTIAL | retires cluster-axiom entries |
| 16 | L3 — Mass-gap conclusion theorem | L3 top file | CONDITIONAL | retires L3 axioms one-by-one |

The canonical, always-up-to-date version of this table is maintained in `UNCONDITIONALITY_ROADMAP.md`.

---

## 7. Repository layout

    YangMills/
      ClayCore/                    ← oracle-clean core (L1 + central L2)
        SchurDiagPhase.lean        ← L2.6 step 0
        SchurTwoSitePhase.lean     ← L2.6 step 1a / 1b-i
        SchurOffDiagonal.lean      ← two-site phase vanishing
        SchurEntryOffDiag.lean     ← L2.6 step 1b (column + general)
        SchurEntryDiagonal.lean    ← L2.6 step 1c  CLOSED (commit d22a6b8)
        SchurL25.lean              ← L2.5 closed (trace decomposition)
        SchurL26.lean              ← L2.6 MAIN TARGET  CLOSED (commit f9ec5e9)
        SchurEntryFull.lean        ← L2.6 step 2  CLOSED (commit 95175f3)
        SchurTracePow.lean         ← L2.6 step 3a sidecar  CLOSED (commit 3c7a957)
        SchurTracePowBilinear.lean ← L2.6 step 3b sidecar  CLOSED (commit 70403d1)
        SchurTraceUPow.lean        ← L2.6 step 3c sidecar  CLOSED (commit bf321e4)
        SchurEntryOrthogonality.lean ← step-1a / 1b-i phase scaffolding
        SchurNormSquared.lean      ← |tr|² structural lemmas
        SchurZeroMean.lean
        SchurPhysicalBridge.lean
        PeterWeyl.lean             ← L2.6 step 3  (current front, TBD)
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

CI refuses a `YangMills/ClayCore/` commit that prints any other axiom name.

Example trace for the most recently closed core theorem:

    #print axioms YangMills.ClayCore.sunHaarProb_trace_normSq_integral_eq_one
    ⟶ [propext, Classical.choice, Quot.sound]

---

## 9. How to contribute

1. Read `AI_ONBOARDING.md` and `CONTRIBUTING.md`.
2. Pick an entry from `AXIOM_FRONTIER.md` or the current front (`PeterWeyl.lean`, to be created).
3. Keep `YangMills/ClayCore/` oracle-clean. Land physics hypotheses in peripheral modules with a *named* `axiom` declaration and a matching row in `AXIOM_FRONTIER.md`.
4. Open a PR with a `#print axioms` trace for every theorem added to ClayCore.
5. If your PR retires a frontier entry, delete the entry from `AXIOM_FRONTIER.md` (or `SORRY_FRONTIER.md`) in the same commit, and bump the relevant bar in §2 of this README.

---

## 10. Honesty note

This project will not be considered a full proof of the Clay Yang–Mills mass gap until `AXIOM_FRONTIER.md` is empty and `SORRY_FRONTIER.md` is empty at the same commit, and L3's top theorem `#print axioms`-prints only `[propext, Classical.choice, Quot.sound]`. We are not there yet.

L2.6's main target (commit `f9ec5e9`) is one rung on that ladder — a concrete, oracle-clean one, and the first L1→L2 interface statement the downstream cluster expansion actually consumes. L2.6 step 3 (Peter–Weyl) is the next. Every milestone in this README is stated with its exact status and a pointer to the file where it lives, so that any reader can check the gap between claim and proof themselves.

If you spot a gap between a claim and a proof here, open an issue. **Transparency over polish.**
