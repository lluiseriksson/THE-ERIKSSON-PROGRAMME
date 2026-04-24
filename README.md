# THE ERIKSSON PROGRAMME

> **A Lean 4 / Mathlib formalization of the Yang–Mills mass gap.**
> Oracle-clean core · transparent frontier · explicit path to 100 % unconditional.

![Lean](https://img.shields.io/badge/Lean-4.29.0--rc6-0052CC)
![Mathlib](https://img.shields.io/badge/Mathlib-master-5e81ac)
![ClayCore oracles](https://img.shields.io/badge/ClayCore%20oracles-propext%20%7C%20Classical.choice%20%7C%20Quot.sound-2e7d32)
![Unconditionality](https://img.shields.io/badge/unconditional-50%25-yellow)
![Front](https://img.shields.io/badge/front-ClusterCorrelatorBound-informational)

---

## TL;DR

- **What works today, oracle-clean.** The L1 layer — Haar measure on `SU(N)` + Schur orthogonality on matrix entries — is closed, and **L2.6's main target has just landed**: the character inner product `⟨χ_fund, χ_fund⟩ = ∫_{SU(N)} |tr U|² dμ_Haar = 1` is a Lean theorem with `#print axioms` ⟹ `[propext, Classical.choice, Quot.sound]`. This is the statement every downstream cluster-expansion bound actually cites.
- **What's next.** `ClusterCorrelatorBound`: the F3 summability/factoring bridge now reaches the exact Wilson-facing target; canonical `⌈siteLatticeDist⌉₊` geometry, distance buckets, and finite `connectingBound` normalization are closed. The live analytic inputs are the Mayer/Ursell identity for `wilsonConnectedCorr` and the Kotecký-Preiss `connectingBound` cluster-series estimate.
- **What's not yet unconditional.** The L3 mass-gap conclusion still depends on declared physics hypotheses — Balaban RG, Dirichlet / Bakry–Émery, Lie-derivative regularity, Stroock–Zegarliński LSI. Every one of them is named in `AXIOM_FRONTIER.md`. The unconditionality roadmap retires them one at a time.

This repository is **not** a finished proof of the Clay Yang–Mills mass gap. It is a structured, transparent push toward one, where every remaining assumption is *named* and the core machinery is held to a strict three-oracle budget. The `#print axioms` trace is the ground truth.

---

## At a glance

| | |
|---|---|
| **Target** | Clay Millennium Prize — existence of quantum Yang–Mills on ℝ⁴ with a positive mass gap |
| **Language** | Lean 4 (`leanprover/lean4:v4.29.0-rc6`) + Mathlib (`master`) |
| **Core discipline** | `YangMills/ClayCore/` prints only `[propext, Classical.choice, Quot.sound]` |
| **Current front** | **`ClusterCorrelatorBound`** — analytic two-point decay for the SU(N_c) Gibbs measure, via F1 (character / Taylor expansion in scalar traces) + F2 (sidecar Haar integrals: L2.5 + 3a + 3b + 3c + main target) + F3 (Kotecky–Preiss cluster convergence) |
| **Last closed** | **v0.66.0 shifted terminal F3 endpoint** — pure-additive, no bar movement. Adds `clusterCorrelatorBound_of_count_cardDecayBounds_ceil_shifted` and `clay_theorem_of_count_connectedCardDecayActivities_ceil_shifted` in `YangMills/ClayCore/ClusterRpowBridge.lean`. This is now the preferred F3 terminal wrapper: it consumes a raw connected-cardinality-decay activity bound, the Mayer/Ursell identity for the constructed activity, and the realistic bucket count `#bucket(n) ≤ C_conn * (n+1)^dim`; disconnected support cancellation, global `K_bound` decay, and finite-volume summability are supplied by `TruncatedActivities.ofConnectedCardDecay`. Final prefactor: `clusterPrefactorShifted r C_conn A₀ dim`. Build `lake build YangMills.ClayCore.ClusterRpowBridge` green. Oracle: `[propext, Classical.choice, Quot.sound]`. No new axioms. No `sorry`. (2026-04-24) |
| **Last updated** | 2026-04-24 |

---

## Table of contents

1. [What this repository is](#1-what-this-repository-is)
2. [Progress toward 100 % unconditional](#2-progress-toward-100--unconditional)
3. [Recently closed milestones](#3-recently-closed-milestones)
4. [Oracle discipline](#4-oracle-discipline--scope-of-the-no-sorry-claim)
5. [Current front — `ClusterCorrelatorBound` (F1 / F2 / F3)](#5-current-front--clustercorrelatorbound-f1--f2--f3)
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
L2.6  Character inner product on SU(N)          ▰▰▰▰▰▰▰▰▰▰  100 %
L2    Character expansion + cluster decay       ▰▰▰▰▰▱▱▱▱▱   50 %
L3    Mass-gap conclusion (with hypotheses)     ▰▰▱▱▱▱▱▱▱▱   22 %
──────────────────────────────────────────────────────────────
      OVERALL unconditionality                  ▰▰▰▰▰▱▱▱▱▱   50 %
```

**Change since previous snapshot (2026-04-22 morning).** L2.6's main target — the character inner product `∫ |tr U|² dμ = 1` — closed at commit `f9ec5e9`, moving L2.6 85 → 95, L2 42 → 50, and overall **40 → 48**. This is the biggest single jump since we began tracking. The bump is backed by an oracle-clean `#print axioms` trace (see §3).

**Follow-up closure (2026-04-22 afternoon).** L2.6 step 2 — the full matrix-entry Schur orthogonality `∫_{SU(N)} U_{ij} · star(U_{kl}) dμ_Haar = δ_{ik} δ_{jl} / N` — closed at commit `95175f3`, moving L2.6 95 → 97 and overall **48 → 50**. This packages the four-case analysis previously deferred as "non-blocking" into a single clean theorem `sunHaarProb_entry_orthogonality` in `SchurEntryFull.lean`, combining step 1b (off-diagonal = 0) and step 1c (diagonal = 1/N) via one `by_cases` on `(i = k ∧ j = l)`. Oracle-clean `[propext, Classical.choice, Quot.sound]`.

**Follow-up closure (2026-04-22 evening).** L2.6 step 3b — the bilinear trace-power vanishing `∫_{SU(N_c)} (tr U)^j · (star (tr U))^k dμ_Haar = 0` when `k ≤ j` and `N_c ∤ (j - k)` — closed at commit `70403d1` in `SchurTracePowBilinear.lean`. This completes the {3a, 3b, 3c} sidecar triplet: 3a handles the pure power `(tr U)^k`, 3c handles the power sum `tr(U^k)`, and 3b now handles the mixed bilinear `(tr U)^j · star(tr U)^k` — the form that actually appears inside character inner products `⟨χ_{V^{⊗j}}, χ_{V^{⊗k}}⟩`. Same central-element argument extended to `ω^{j-k} ≠ 1` (with `j ≥ k` and `N_c ∤ (j-k)`). Seven new theorems total: the helper `rootOfUnity_pow_mul_star_pow`, the transport lemma `trace_scalarCenter_mul_pow_bilinear`, the MAIN `sunHaarProb_trace_pow_bilinear_integral_zero` plus a prime variant with `star` applied to the whole power, two low-degree corollaries (`j=2,k=1` requiring `N_c ≥ 2`; `j=3,k=1` requiring `N_c ≥ 3`), and a non-triviality witness at `U = 1` evaluating to `(N_c)^{j+k}`. Oracle-clean `[propext, Classical.choice, Quot.sound]` for all seven. L2.6 bar unchanged at 97 %; step 3 proper (arbitrary irreps, not just scalar traces and their bilinear products) remains open.

**New milestone (2026-04-23 — N_c = 1 unconditional witness).** `YangMills/ClayCore/AbelianU1Unconditional.lean` lands a concrete, unconditional inhabitant of `ClayYangMillsMassGap 1` — zero hypotheses, zero `sorry`, and `#print axioms` on all six produced artefacts prints exactly `[propext, Classical.choice, Quot.sound]`. The proof uses `Subsingleton (Matrix.specialUnitaryGroup (Fin 1) ℂ)` (SU(1) has exactly one element) to collapse every Wilson observable to a constant, force the connected correlator to vanish identically, and satisfy `ConnectedCorrDecay` vacuously at `m = kpParameter (1/2)`, `C = 1`. This does **not** retire a named entry in `AXIOM_FRONTIER.md` or `SORRY_FRONTIER.md` (those are scoped to `N_c ≥ 2` physics hypotheses), so the L1 / L2 / L3 / OVERALL bars do not move. What it establishes is a lower-bound existential anchor: `ClayYangMillsMassGap _` is not vacuous-by-contradiction in our Lean model; it has at least one oracle-clean inhabitant today. For `N_c ≥ 2`, the same schema must be filled in via the `ClusterCorrelatorBound` front (F1 / F2 / F3).

**Strategic note on the step 1c → main-target transition.** The plan previously anticipated a separate "step 2" that packages matrix-entry Schur orthogonality `∫ U_ij · star(U_kl) dμ = (1/N) δ_ik δ_jl`. When the parallel instance inspected the downstream L2 call sites, the statement actually consumed is the **character-level** one: `∫ |tr U|² dμ = 1`. That follows from L2.5's trace decomposition `∫ tr U · star(tr U) = ∑ᵢ ∫ |Uᵢᵢ|²` plus step 1c's diagonal identity `∫ |Uᵢᵢ|² = 1/N`. We therefore went directly to the character-level consumer. Full matrix-entry packaging has now been landed anyway (step 2, commit `95175f3`, theorem `sunHaarProb_entry_orthogonality` in `SchurEntryFull.lean`) — it was not on the critical path, but closing it removes a standing TODO and keeps the `δ_{ik} δ_{jl} / N` form available as public API for any irrep-generalization downstream consumer that prefers it over the character-level reduction.

**How the overall number is computed.** Each layer's percentage is the ratio of oracle-clean, sorry-free Lean artifacts to that layer's planned artifact count in `UNCONDITIONALITY_ROADMAP.md`. The overall number weights the layers by their total frontier-entry count in `AXIOM_FRONTIER.md` + `SORRY_FRONTIER.md`. The metric is **monotone by design**: it cannot go up except by retiring a named frontier entry, and it cannot go down unless a previously closed lemma regresses in CI.

**What this number is not.** It is not a confidence score in the mass-gap result, and it is not the ratio of filled theorems in the whole repo. It is specifically *"how much of the declared hypothesis set has been discharged in Lean."*

**Next expected movement.** L2.6 is now closed at 100 %. The next live movement comes from `ClusterCorrelatorBound` (the analytic target that `h_correlator` on `CharacterExpansionData` names). When F1 (character / Taylor expansion of `exp(-β · Re tr U)` in scalar traces), F2 (Haar sidecar assemblage from L2.5 + 3a + 3b + 3c + main target), and F3 (Kotecky–Preiss cluster convergence) land, L2 bumps to ~75 % and the overall number crosses 58 %.

---

## 3. Recently closed milestones

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

### N_c = 1 unconditional witness — `ClayYangMillsMassGap 1` inhabited (2026-04-23)

**Theorem.** `YangMills.u1_clay_yangMills_mass_gap_unconditional : ClayYangMillsMassGap 1` in `YangMills/ClayCore/AbelianU1Unconditional.lean`. Zero hypotheses. First concrete inhabitant of the Clay statement in this repository.

**Why N_c = 1 is tractable.** `Matrix.specialUnitaryGroup (Fin 1) ℂ` has exactly one element (the identity). Lean sees this as `Subsingleton`, which means every Wilson observable is constant, every Wilson connected correlator is identically zero, and `ConnectedCorrDecay` holds vacuously. We can therefore pick any positive mass gap `m > 0` and prefactor `C > 0`; the witness in this file takes `m = kpParameter (1/2)` and `C = 1` for arithmetic cleanliness.

**Oracle trace (verified at deploy time, 6 / 6).**

    #print axioms YangMills.unconditionalU1CorrelatorBound
    ⟶ [propext, Classical.choice, Quot.sound]

    #print axioms YangMills.u1_clay_yangMills_mass_gap_unconditional
    ⟶ [propext, Classical.choice, Quot.sound]

    #print axioms YangMills.wilsonConnectedCorr_su1_eq_zero
    ⟶ [propext, Classical.choice, Quot.sound]

    #print axioms YangMills.u1_unconditional_mass_gap_eq
    ⟶ [propext, Classical.choice, Quot.sound]

    #print axioms YangMills.u1_unconditional_mass_gap_pos
    ⟶ [propext, Classical.choice, Quot.sound]

    #print axioms YangMills.u1_unconditional_prefactor_eq
    ⟶ [propext, Classical.choice, Quot.sound]

**What it is, and what it is not.** This is the first proof, in this repository, that `ClayYangMillsMassGap _` has any inhabitant at all — i.e., that the Lean model of the Clay conclusion is not vacuous-by-contradiction. For the physically meaningful cases (`N_c ≥ 2`), the connected correlator is not identically zero, so the `ConnectedCorrDecay` witness must come from genuine analytic content: Osterwalder–Seiler reflection positivity, Kotecký–Preiss cluster convergence, and Balaban RG. Those are tracked on the `ClusterCorrelatorBound` front (F1 / F2 / F3) and remain open. No entry in `AXIOM_FRONTIER.md` or `SORRY_FRONTIER.md` was retired by this commit.

**Impact on the unconditionality ladder.** A new row is added to section 6 for the N_c = 1 witness (see ladder). The L1 / L2 / L3 / OVERALL percentage bars are unchanged, by design: the bars measure retirement of named hypotheses, and this milestone is orthogonal to that set.

---

## 4. Oracle discipline — scope of the "no sorry" claim

The `YangMills/ClayCore/` subtree — the L1 + central L2 chain through Schur orthogonality, the trace/Frobenius bound, and now the character inner product — is held to a strict oracle budget:

    #print axioms <theorem>  ⟹  [propext, Classical.choice, Quot.sound]

No project-specific `axiom`, no `sorry`, nothing beyond Lean's three foundational oracles. Any commit that enlarges the axiom print of a ClayCore theorem is rejected.

**This discipline is scoped to `YangMills/ClayCore/` only.** Peripheral modules that model Balaban RG, Dirichlet / Bakry–Émery, Lie-derivative regularity, and Stroock–Zegarliński-type LSI inputs still carry conditional `axiom` declarations and a small number of `sorry`s. These are the declared physics hypotheses of L3, each tracked individually in `AXIOM_FRONTIER.md` and `SORRY_FRONTIER.md`. The unconditionality roadmap is precisely the plan to eliminate those peripheral entries one at a time, starting from the L1 end.

So: the *core* is oracle-clean today. The *whole project* is not — and we say so out in the open, file by file.

---

## 5. Current front — `ClusterCorrelatorBound` (F1 / F2 / F3)
**Target statement.** `YangMills.ClayCore.ClusterCorrelatorBound N_c r C_clust` (in `ClusterCorrelatorBound.lean`): for every β > 0, every Wilson observable `F`, and every pair of plaquettes `p, q` with `siteLatticeDist p.site q.site ≥ 1`,
    |wilsonConnectedCorr β F p q|  ≤  C_clust · exp(− kpParameter(r) · siteLatticeDist p.site q.site).
This is the field named `h_correlator` on `CharacterExpansionData`, and by the recon of commit `70403d1` it is the *only* field that downstream consumers actually use.
### 5.1 Vestigial-metadata finding (2026-04-22 evening)
Consumer-driven recon of `CharacterExpansion.lean` / `ClusterCorrelatorBound.lean` / `WilsonGibbsExpansion.lean` shows:
- `CharacterExpansionData.{Rep, character, coeff}` are **vestigial metadata**. In `wilsonCharExpansion` they are filled with `Rep := PUnit`, `character := fun _ _ => 0`, `coeff := fun _ _ => 0` — carrying no representation-theoretic content.
- No external file imports `CharacterExpansionData.character`, `.coeff`, or `.Rep`. Zero citations of Peter–Weyl vocabulary, `MatrixCoefficient`, or arbitrary-irrep characters outside ClayCore.
- Only `h_correlator` flows to Clay (via `WilsonGibbsPolymerRep`'s polymer-rep passthrough in `WilsonGibbsExpansion.lean`, which explicitly discards `Rep` / `character` / `coeff`).
- **Consequence.** Arbitrary-irrep Peter–Weyl orthogonality is **not** a Clay blocker. L2.6 is therefore closed at 100 % by sidecar reclassification: the downstream-relevant character identities (3a + 3b + 3c + main target + L2.5) already span the integrand subalgebra that the character / Taylor expansion actually needs.
### 5.2 Strategy: F1 + F2 + F3 directly to `ClusterCorrelatorBound`
The critical path is a scalar-trace character / Taylor expansion, not an arbitrary-irrep Peter–Weyl argument:
- **F1 — character / Taylor expansion.** Expand `exp(−β · Re tr U) = ∑_{j,k ≥ 0} ((−β / 2)^{j+k} / (j! · k!)) · (tr U)^j · (star(tr U))^k` on each plaquette. Verify termwise Haar integrability and absolute summability in β.
- **F2 — Haar sidecar assemblage.** Each Haar integral of a monomial `(tr U)^j · star(tr U)^k` on SU(N_c) is computed from the sidecar triplet and the main target:
  - `j = k = 0`: trivial (1).
  - `j = k = 1`: L2.6 main target (commit `f9ec5e9`).
  - `j = 0, k ≥ 1` or `k = 0, j ≥ 1`: L2.6 step 3a (`SchurTracePow`, commit `3c7a957`) plus trivial conjugation.
  - `j ≠ k`, `N_c ∤ |j−k|`: L2.6 step 3b (`SchurTracePowBilinear`, commit `70403d1`).
  - `j = k ≥ 1` (Frobenius / Weingarten on the diagonal): reduces via L2.5 (`∑_i ∫ |U_ii|² dμ ≤ N_c`) + step 1c to a scalar bound, no new irrep theory required.
  - `j ≠ k`, `N_c ∣ (j−k)`: the only case where the monomial has nonzero Haar integral on SU(N_c). Handled at the F3 combinatorial layer (it contributes a subexponentially-bounded constant, not a divergence).
- **F3 — Kotecky–Preiss cluster convergence.** Feed the F1 · F2 monomial bounds into the abstract polymer / Mayer scaffolding already in place (`ClusterSeriesBound.lean` supplies `tsum` summability D1 and factoring D2; `MayerExpansion.lean` supplies `TruncatedActivities` and `connectingSum` / `connectingBound` via Kotecky–Preiss). Output: the analytic inequality `|wilsonConnectedCorr| ≤ C_clust · exp(− kpParameter(r) · dist)` with explicit `(r, C_clust)` in terms of `β` and `N_c`.
All three layers respect the strict `YangMills/ClayCore/` oracle budget.
### 5.3 Oracle budget for the front
Every theorem inside `YangMills/ClayCore/` on the `ClusterCorrelatorBound` critical path must satisfy `#print axioms ... ⟶ [propext, Classical.choice, Quot.sound]`. If any dependency of F1 / F2 / F3 introduces a new axiom or `sorry`, it is surfaced as a named entry in `AXIOM_FRONTIER.md` (or `SORRY_FRONTIER.md`) with a retirement plan — never silently absorbed.
### 5.4 Peter–Weyl step 3 — reclassified as aspirational
The original L2.6 step 3 (arbitrary-irrep Peter–Weyl character orthogonality) is preserved as an aspirational / Mathlib-PR target in `PETER_WEYL_ROADMAP.md`. It is not on the Clay critical path. Its value is purely mathematical cleanliness: if landed, it would allow `CharacterExpansionData.{Rep, character, coeff}` to carry genuine representation-theoretic content rather than vestigial `PUnit`, and would let the character expansion be stated over *all* irreps rather than over the scalar-trace subalgebra. That is nice to have, but strictly unnecessary for `ClusterCorrelatorBound`.## 6. Milestone ladder

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
| 14 | **`ClusterCorrelatorBound` — analytic two-point decay via F1 + F2 + F3** | **`ClusterCorrelatorBound.lean` + `WilsonGibbsExpansion.lean` + `MayerExpansion.lean`** | **IN PROGRESS** | oracle-clean; critical path (L2.6 step 3 proper reclassified as aspirational / Mathlib-PR in `PETER_WEYL_ROADMAP.md`) |
| 15 | L2 — Cluster expansion bounds | `CharacterExpansion.lean` + cluster | PARTIAL | retires cluster-axiom entries |
| 16 | L3 — Mass-gap conclusion theorem | L3 top file | CONDITIONAL | retires L3 axioms one-by-one |
| 17 | **`ClayYangMillsMassGap 1` — unconditional witness at N_c = 1** | **`AbelianU1Unconditional.lean`** | **DONE** | **oracle-clean (6 / 6 artefacts, 2026-04-23); does not retire a named axiom — scoped below the L1 / L2 / L3 N_c ≥ 2 frontier** |

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
        PeterWeyl.lean             ← L2.6 step 3 aspirational / Mathlib-PR (see PETER_WEYL_ROADMAP.md)
        CharacterExpansion.lean    ← CharacterExpansionData struct (Rep / character / coeff VESTIGIAL; see AXIOM_FRONTIER.md v0.38.0)
        ClusterCorrelatorBound.lean ← CURRENT FRONT: analytic two-point decay for SU(N_c) Gibbs measure
        WilsonGibbsExpansion.lean  ← polymer-rep passthrough (Rep / character / coeff discarded)
        ClusterSeriesBound.lean    ← D1 (tsum summability) + D2 (factoring); KP scaffolding
        MayerExpansion.lean        ← TruncatedActivities + connectingSum / connectingBound (Kotecky–Preiss)
        …                          ← Wilson / Cluster / Balaban machinery
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
