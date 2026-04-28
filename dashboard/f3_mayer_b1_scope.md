# F3-MAYER §(b)/B.1 — Truncated-Activity Single-Vertex Vanishing Scope

**Cowork-authored Codex-ready signature scaffold for F3-MAYER §(b)/B.1.**

**Author**: Cowork
**Created**: 2026-04-26T23:50:00Z (under `COWORK-F3-MAYER-NEXT-STEP-SCOPE-001`)
**Status**: **forward-looking blueprint only**. F3-MAYER is `BLOCKED` (gated on F3-COUNT closure first per LEDGER:98). §(b)/B.1 is **OPEN**. Nothing in this document moves any LEDGER row or percentage.

---

## Mandatory disclaimer

> **F3-MAYER row in `UNCONDITIONALITY_LEDGER.md` is `BLOCKED`** (gated on
> F3-COUNT row closure first). §(b)/B.1 (the easiest of the six missing
> Mayer theorems) is OPEN. This document scopes B.1 only as a Codex-ready
> implementation blueprint to be picked up *after* F3-COUNT closes (i.e.
> after Codex's B.2 anchored word decoder lands and `COWORK-AUDIT-FRESH-PERCENTAGE-MOVE-001`
> validates the F3-COUNT row promotion). **Nothing here moves the F3-MAYER
> row from `BLOCKED` or moves any percentage. All 4 percentages preserved
> at 5% / 28% / 23-25% / 50%.**

---

## Context

`F3_MAYER_DEPENDENCY_MAP.md` §(b) (lines 145+) enumerates **six missing Mayer
theorems** B.1–B.6 needed to inhabit `ConnectedCardDecayMayerData N_c (4 N_c β) 1
hr_nonneg hA_nonneg` for `β < log(2)/N_c`:

| # | Theorem | Difficulty | Est. LOC |
|---|---|---|---:|
| **B.1** | **Truncated-activity vanishing on single-vertex polymers** | **EASY** | **~30** |
| B.2 | Truncated-activity vanishing on disconnected polymers | MEDIUM | ~150 |
| B.3 | BK polymer-bound `|K(Y)| ≤ ‖w̃‖_∞^|Y|` (analytic boss) | HIGH | ~250 |
| B.4 | Sup bound `‖w̃‖_∞ ≤ 4 N_c · β` | EASY-MEDIUM | ~80 |
| B.5 | Mayer/Ursell identity in project notation | MEDIUM-HIGH | ~200 |
| B.6 | The bundled witness | MEDIUM | ~50 |

**This document scopes B.1 only** — the easiest theorem and the natural first
post-F3-COUNT step. Once B.1 lands, the project's MEDIUM/HIGH difficulty work
(B.2/B.3/B.5) opens up but is more substantial. Treat B.1 as the warm-up that
unblocks the F3-MAYER pipeline.

---

## (a) Precise Lean signature

The target theorem (verbatim from `F3_MAYER_DEPENDENCY_MAP.md:154-158`):

```lean
theorem truncatedK_zero_of_card_one
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (F : G → ℝ)
    (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L)) (hY : Y.card = 1) :
    truncatedK β F p q Y = 0
```

In English: when the polymer `Y` is a single plaquette, the truncated activity
`K(Y) = ⟨w̃⟩` integrates the zero-mean fluctuation over Haar measure and
vanishes identically.

**File location** (proposed): adjacent to existing `ZeroMeanCancellation.lean`
(398 lines, oracle-clean per `F3_MAYER_DEPENDENCY_MAP.md:74-84`) — likely a
new helper section in `MayerExpansion.lean` (which already hosts the
`TruncatedActivities` scaffold at line 50) OR a fresh file
`YangMills/ClayCore/MayerB1Single.lean`.

---

## (b) Statement of the Brydges-Kennedy / Ursell expansion form (B.1 fragment)

The Mayer / Ursell formalism on lattice polymers `Y ⊆ {plaquettes}` decomposes
the partition function `Z(β)` into truncated cluster activities:

```
log Z(β) = ∑_{Y polymer connected} K_β(Y)
```

Each `K_β(Y)` is the *truncated* activity on polymer `Y`:

```
K_β(Y) := (Möbius truncation of) ∫ ∏_{p ∈ Y} w̃_p dHaar
```

where `w̃_p := plaquetteWeight_p / Z_p − 1` is the **normalised plaquette
fluctuation** at site `p` (`MayerIdentity.lean:126`,
`plaquetteFluctuationNorm`).

**The keystone (already proved at `ZeroMeanCancellation.lean:142`)**:

```lean
theorem plaquetteFluctuationNorm_mean_zero :
    ∫ w̃_p dHaar = 0
```

**B.1 is the immediate corollary of the keystone applied to single-vertex
polymers**:

When `|Y| = 1`, the truncation is trivial (no Möbius subtraction; only one
sub-polymer = `∅`), so `K_β({p}) = ⟨w̃_p⟩` directly. The keystone gives
`⟨w̃_p⟩ = 0`. Therefore `K_β(Y) = 0` whenever `Y.card = 1`. □

This is the **single-line mathematical content of B.1**. The Lean proof is
the formalization of this single substitution step (~30 LOC, mostly
unfolding definitions and composing with the existing keystone).

---

## (c) Connection to `dashboard/mayer_mathlib_precheck.md` has-vs-lacks table

The mayer Mathlib precheck (filed 20:20Z, audited at `COWORK-MAYER-MATHLIB-PRECHECK-001`)
classified Mathlib's BK / Möbius / forest-formula readiness into 13 rows. The
relevant rows for **B.1** are:

| Mathlib facility | Status | Relevance to B.1 |
|---|:---:|---|
| `MeasureTheory.integral_zero` (zero integrand → zero integral) | **HAS** | Direct primitive needed by B.1 (when keystone is unfolded). |
| `MeasureTheory.integral_const` (constant integrand) | **HAS** | Used in any rephrasing of the proof. |
| Project's `plaquetteFluctuationNorm_mean_zero` (`ZeroMeanCancellation.lean:142`) | **HAS** | The keystone Cowork-audit is built on. NOT a Mathlib primitive — project-internal but oracle-clean. |
| `Finset.sum` over polymer subsets / Möbius truncation | **HAS** in basic form | B.1 only needs the trivial `|Y|=1` truncation = identity, so no real Möbius machinery is exercised at this step. The harder uses appear in B.5. |
| `BrydgesKennedyForest`, `MayerUrsell`, polymer-graph cluster-expansion | **LACKS** | NOT needed for B.1 (only B.3 / B.5 hit this gap). |

**Conclusion**: B.1 has **zero Mathlib gaps**. It's pure project-side
algebraic unfolding using the already-proved keystone. The Mathlib gaps
identified by `mayer_mathlib_precheck.md` are all on the BK forest formula
(B.3) and Mayer/Ursell identity (B.5) sides; B.1 is on the easy side of
that gap.

This makes B.1 the **ideal warm-up theorem** post-F3-COUNT closure: low
risk, no Mathlib roundtrip required, proves the F3-MAYER pipeline is
buildable from existing infrastructure before Codex tackles the harder B.3 / B.5.

---

## (d) Decomposition into project-side ~30 LOC + Mathlib-side gaps

**Project-side LOC budget for B.1**: **~30 LOC** (per `F3_MAYER_DEPENDENCY_MAP.md:163`):

| Sub-step | LOC | Content |
|---|---:|---|
| Unfold `truncatedK` definition for `Y.card = 1` | ~5 | `Finset.singleton` cases on `Y` to reach `Y = {p}` for some `p` |
| Reduce truncation to `⟨w̃_p⟩` | ~10 | Möbius truncation on single-element polymer = identity (no sub-polymers to subtract); cite `Finset.sum_singleton` or similar |
| Apply keystone `plaquetteFluctuationNorm_mean_zero` | ~5 | Single rewrite step: `⟨w̃_p⟩ = 0` |
| Conclude `K({p}) = 0` | ~5 | Linarith / norm cleanup |
| `#print axioms` directive | ~1 | Pin oracle trace to `[propext, Classical.choice, Quot.sound]` |
| Doc comments | ~5 | Mandatory disclaimer + cross-reference to keystone |

**Mathlib-side gaps**: **NONE** for B.1. All primitives in place:
- `MeasureTheory.integral_zero` ✓
- `Finset.sum_singleton` ✓
- `Finset.card_eq_one` (for `Y.card = 1` extraction) ✓
- Project keystone `plaquetteFluctuationNorm_mean_zero` ✓ (`ZeroMeanCancellation.lean:142`)

**Risk profile**: VERY LOW. No new mathematical content; pure formalization
of a one-line composition.

---

## (e) Klarner-Ursell pairing argument

After B.1 (and the rest of B.2-B.6) lands, the F3-MAYER side produces an
inhabitant of `ConnectedCardDecayMayerData N_c (4 N_c β) 1 hr_nonneg hA_nonneg`
(`ClusterRpowBridge.lean:2229`). The F3-COUNT side (post-B.2 word decoder)
produces a `ShiftedConnectingClusterCountBoundExp` (`LatticeAnimalCount.lean:1096`
consumer chain).

The **Klarner-Ursell pairing** is the geometric series convergence at
`ShiftedF3MayerCountPackageExp.ofSubpackages` (`ClusterRpowBridge.lean:4371`):

```
∑_{Y polymer connecting p,q} |K_β(Y)|
  ≤ ∑_{Y connecting} A₀ · r^|Y|       (B.3 + cardinality bound from F3-COUNT)
  = A₀ · ∑_n count(n; p, q) · r^n
  ≤ A₀ · ∑_n K^n · r^n                (Klarner: count ≤ K^n)
  = A₀ · 1/(1 − K · r)                (Klarner-Ursell pairing!)
  = finite                              (when K · r < 1)
```

For the specific physical assembly, `K = 7` (Klarner constant for d=4 lattice
animals; this is exactly what F3-COUNT delivers via the line-1096 consumer)
and `r = 4 N_c · β` (B.4 bound). Smallness `K · r < 1` reduces to
`7 · 4 N_c · β < 1`, i.e. `β < 1/(28 N_c)` — this is the small-β regime
formalized throughout the project.

**B.1 alone does not produce this pairing** — it only retires the easiest of
the six theorems needed to reach `ConnectedCardDecayMayerData`. But B.1 is
the *first* nontrivial Mayer theorem, and once it lands the pipeline shape
is committed: each subsequent Bi closes one term of the sum-bound chain
above.

**Strategic note**: the order B.1 → B.2 → B.4 → B.6 → B.3 → B.5 is
recommended (easy/medium first to validate API; HIGH-difficulty B.3 +
MEDIUM-HIGH B.5 last when the rest of the structure is proved). B.5
(Mayer/Ursell identity) is naturally the last step since it bundles all
the prior steps into the `h_mayer` field of `ConnectedCardDecayMayerData`.

---

## Summary table — pre-supplied API surface for §(b)/B.1

| Section | Identifier | File:line | Role in §(b)/B.1 |
|---|---|---|---|
| (a) signature | `truncatedK_zero_of_card_one` | (proposed) `MayerB1Single.lean` or addition to `MayerExpansion.lean` | The B.1 target |
| (b) keystone | `plaquetteFluctuationNorm_mean_zero` | `ZeroMeanCancellation.lean:142` | Already proved; B.1 reduces to a single application |
| (b) carrier | `plaquetteFluctuationNorm` | `ZeroMeanCancellation.lean:126` | The variable `w̃` |
| (b) raw | `plaquetteFluctuationRaw` | `MayerIdentity.lean:88` | Pre-normalised version (auxiliary) |
| (b) raw vanishing | `plaquetteFluctuationRaw_zero_beta` | `MayerIdentity.lean:101` | β=0 sanity (not strictly needed for B.1 but cross-check) |
| (b) truncation scaffold | `TruncatedActivities` | `MayerExpansion.lean:50` | Carrier structure where B.1 hooks in |
| (e) pairing target | `ConnectedCardDecayMayerData` | `ClusterRpowBridge.lean:2229` | F3-MAYER ultimate target structure |
| (e) Clay-facing assembly | `ShiftedF3MayerCountPackageExp` | `ClusterRpowBridge.lean:4355` | Pairs Mayer + Count packages |
| (e) terminal | `clayMassGap_of_shiftedF3MayerCountPackageExp` | `ClusterRpowBridge.lean:4855` | Produces `ClayYangMillsMassGap N_c` |

---

## What this scope does NOT do

- **Does not prove** `truncatedK_zero_of_card_one`.
- **Does not move** F3-MAYER from `BLOCKED`.
- **Does not move** F3-COUNT (still `CONDITIONAL_BRIDGE` until B.2 word decoder lands).
- **Does not move** any percentage (5% / 28% / 23-25% / 50% all preserved).
- **Does not assume** F3-COUNT has closed; this scope is conditional on the
  F3-COUNT closure event that triggers `COWORK-AUDIT-FRESH-PERCENTAGE-MOVE-001`.

The scope is purely a **forward-looking implementation blueprint** for Codex
to pick up **after** F3-COUNT moves to FORMAL_KERNEL.

---

## Honesty preservation

- F3-MAYER row: unchanged (`BLOCKED`)
- F3-COUNT row: unchanged (`CONDITIONAL_BRIDGE`)
- F3-COMBINED row: unchanged (`BLOCKED`)
- All 4 percentages: unchanged at 5% / 28% / 23-25% / 50%
- This document is a **forward-looking blueprint**, not a proof artifact.

---

## Cross-references

- `F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 143-261 — the full B.1-B.6 roster
- `F3_MAYER_DEPENDENCY_MAP.md` §(a) lines 51-140 — already-proved A.0-A.7 scaffolding (B.1's keystone is at A.2 line 142)
- `dashboard/mayer_mathlib_precheck.md` — Mathlib has-vs-lacks 13-row table; B.1 has zero gaps
- `dashboard/f3_decoder_iteration_scope.md` — sibling B.2 scope for F3-COUNT (this is the F3-MAYER analog)
- `YangMills/ClayCore/ZeroMeanCancellation.lean:142` — the keystone B.1 reduces to
- `YangMills/ClayCore/MayerExpansion.lean:50` — `TruncatedActivities` scaffold
- `YangMills/ClayCore/ClusterRpowBridge.lean:2229` — `ConnectedCardDecayMayerData` ultimate target
- `BLUEPRINT_F3Mayer.md` — Brydges-Kennedy / Mayer / Ursell mathematical context
- `UNCONDITIONALITY_LEDGER.md:98` — F3-MAYER row (`BLOCKED on F3-COUNT closure first`)
- `REC-CODEX-MAYER-MATHLIB-CAYLEY-OR-PRUFER-001` (OPEN) — eventual Mathlib PR for B.5 forest-formula
- `REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001` (OPEN) — eventual project-side BK formula scope (for B.3)
