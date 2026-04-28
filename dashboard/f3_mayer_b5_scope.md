# F3-MAYER §(b)/B.5 — Mayer/Ursell Identity Scope (final F3-MAYER scope)

**Cowork-authored Codex-ready signature scaffold for F3-MAYER §(b)/B.5.**

**Author**: Cowork
**Created**: 2026-04-27T06:00:00Z (under `COWORK-F3-MAYER-B5-SCOPE-001`)
**Status**: **forward-looking blueprint only**. F3-MAYER is `BLOCKED` (gated on F3-COUNT closure first per LEDGER:88). §(b)/B.5 is **OPEN** — the **MEDIUM-HIGH-difficulty Mayer/Ursell identity**, the bridge between the algebraic cluster expansion (already proved at `MayerIdentity.lean:138`) and the consumer-ready `ConnectedCardDecayMayerData` structure.

**🏁 This is the FINAL F3-MAYER scope.** After this delivery, **all 6 MAYER theorems are scoped** — completing the F3-MAYER pre-supply pattern's scoping phase (~760 LOC total project-side roadmap). Nothing in this document moves any LEDGER row or percentage.

---

## Mandatory disclaimer

> **F3-MAYER row in `UNCONDITIONALITY_LEDGER.md` is `BLOCKED`** (gated on
> F3-COUNT row closure first). §(b)/B.5 is the **MEDIUM-HIGH** sixth and
> final missing Mayer theorem to be scoped. It packages the connection
> between the already-proved algebraic cluster expansion
> (`boltzmann_cluster_expansion_pointwise` at `MayerIdentity.lean:138`)
> and the consumer-ready `TruncatedActivities.ofConnectedCardDecay K`
> structure consumed by `ConnectedCardDecayMayerData.h_mayer`. **B.5 is
> not the analytic boss (B.3) — it is identity-rewriting via Möbius
> inversion**, but it is still 200 LOC of careful combinatorial Lean.
> This document scopes B.5 as a Codex-ready implementation blueprint to
> be picked up *after* (1) F3-COUNT closes, (2) B.1 + B.2 + B.3 + B.4
> land, and (3) Codex has bandwidth for ~200 LOC of identity-rewriting
> Lean work. **Nothing here moves the F3-MAYER row from `BLOCKED` or
> moves any percentage. All 4 percentages preserved at 5% / 28% / 23-25%
> / 50%.**

---

## Context — completing the F3-MAYER scope corpus

`F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 145+ enumerates **six missing
Mayer theorems** B.1-B.6. After this delivery, all 6 will be scoped:

| # | Theorem | Difficulty | Est. LOC | Status |
|---|---|---|---:|---|
| B.1 | Single-vertex truncated-K = 0 | EASY | ~30 | **scoped** in `f3_mayer_b1_scope.md` |
| B.2 | Disconnected-polymer truncated-K = 0 | MEDIUM | ~150 | **scoped** in `f3_mayer_b2_scope.md` |
| B.3 | BK polymer bound `|K(Y)| ≤ ‖w̃‖∞^|Y|` | HIGH | ~250 | **scoped** in `f3_mayer_b3_scope.md` |
| B.4 | Sup bound `‖w̃‖∞ ≤ 4 N_c · β` | EASY-MEDIUM | ~80 | **scoped** in `f3_mayer_b4_scope.md` (hypothesis-flag pending) |
| **B.5** | **Mayer/Ursell identity in project notation** | **MEDIUM-HIGH** | **~200** | **SCOPED — this document** |
| B.6 | Bundled witness | EASY (glue) | ~50 | **scoped** in `f3_mayer_b6_scope.md` |

**Total F3-MAYER LOC budget after B.5**: ~30 + 150 + 250 + 80 + **200** + 50 = **~760 LOC** of forward-planned project-side Lean work, exactly matching BLUEPRINT_F3Mayer's ~700 LOC estimate.

**Why B.5 is positioned between B.3 and B.6 in the recommended implementation order**: B.5 introduces `truncatedK` formally (via the Möbius inversion) which B.3 then bounds and B.6 then bundles. So:

`B.1 → B.4 → B.2 → B.5 → B.3 → B.6`

B.5 is the bridge between the Wilson-Haar measure-theoretic infrastructure (B.1, B.2) and the analytic estimation (B.3). It introduces the truncated activity `K(Y)` as the project-internal Mayer/Ursell identity.

---

## (a) Precise Lean signature

The target theorem (verbatim from `F3_MAYER_DEPENDENCY_MAP.md:225-234`):

```lean
theorem truncatedK_satisfies_mayer_identity
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (hβ : 0 < β) (F : G → ℝ) (hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L) (hpq : 1 ≤ siteLatticeDist p.site q.site) :
    wilsonConnectedCorr (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F p q
    = (TruncatedActivities.ofConnectedCardDecay
        (truncatedK β F p q) p q (4 * N_c * β) 1
        (by positivity) zero_le_one
        (truncatedK_abs_le_card_decay β F p q)).connectingSum p q
```

**Carried-over hypothesis flag from B.4**: per `f3_mayer_b4_scope.md` and
`REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001`, the smallness hypothesis
should be tightened to `β < 1/(2 * N_c)` for downstream consumption of
the `r = 4 N_c β` constant. B.5's signature uses `0 < β` plus `|F U| ≤ 1`
which is a separate set of hypotheses, but if B.5 invokes B.4's bound
inline, the hypothesis set should match.

**Note on `truncatedK β F p q` and `truncatedK_abs_le_card_decay β F p q`**:
both are project-internal forthcoming definitions/theorems that B.5 itself
introduces. The signature references them recursively because B.5 *defines*
`truncatedK` as part of its proof — the signature shape simultaneously:

- Asserts the Mayer identity equation
- Implicitly defines `truncatedK β F p q` as the function satisfying it
- Implicitly relies on `truncatedK_abs_le_card_decay` (which is the
  combination of B.3 + B.4 substituted into the connected-card-decay
  shape required by `TruncatedActivities.ofConnectedCardDecay`)

So B.5 is structured in **3 internal phases**:

1. **Define `truncatedK β F p q : Finset Plaquette → ℝ`** via Möbius
   inversion on the cluster-expansion identity (~80 LOC; the "Möbius
   bookkeeping" half).
2. **Prove `truncatedK_abs_le_card_decay β F p q`** by composing B.3
   (BK polymer bound) with B.4 (sup bound) (~30 LOC; bridges to the
   structure target).
3. **Prove the Mayer identity itself** by chaining the cluster expansion
   (already proved at `MayerIdentity.lean:138`) with the Möbius inversion
   to identify the connecting sum (~90 LOC; the "BK identification" half).

**File location** (proposed): a new helper file
`YangMills/ClayCore/MayerInversion.lean` (~200 LOC) per BLUEPRINT_F3Mayer
§4.1 file (1) (originally named `MayerInterpolation.lean` but B.5's job is
the inversion identity, not the interpolation; the BLUEPRINT layout
combined them for brevity). Alternative: append to existing
`YangMills/ClayCore/MayerExpansion.lean` (which already has the
`TruncatedActivities` scaffold at line 50).

---

## (b) Statement of the Möbius inversion + identification (B.5 fragment)

The mathematical content of B.5 is the **Mayer/Ursell identity**: the
Wilson connected correlator can be written as a sum over connected
polymers of truncated activities, where each truncated activity is the
"connected" part of the un-truncated activity extracted by Möbius
inversion on the partition lattice.

### Starting point: the algebraic cluster expansion (already proved)

`MayerIdentity.lean:138` proves:

```lean
theorem boltzmann_cluster_expansion_pointwise
    (N_c : ℕ) [NeZero N_c] (β : ℝ) (U : SU(N_c))
    (plaquettes : Finset (ConcretePlaquette d L)) :
    Real.exp (-β * ∑ _p ∈ plaquettes, wilsonPlaquetteEnergy N_c U) =
    ∑ S ∈ plaquettes.powerset, ∏ _p ∈ S, plaquetteFluctuationRaw N_c β U
```

This is the **algebraic identity** `exp(-β · ∑E) = ∑_S ∏_S w_raw` (sum
over subsets `S` of the plaquette index set, product over `S` of the raw
plaquette fluctuation `w_raw = exp(-β · E) - 1`).

### Step 1 — From raw to normalised fluctuation

Divide both sides by the partition function `Z_p(β)^|plaquettes|`:

```
exp(-β · ∑ E) / Z_p^|plaquettes| = ∑_S ∏_S (w_raw / Z_p)
                                 = ∑_S ∏_S w̃                 (definition of w̃)
```

Then the Wilson density is `∏ exp(-β · E_r) / Z_p` for each plaquette `r`,
which factorizes into `∏_r (1 + w̃_r)`:

```
exp(-β · ∑ E) / Z_p^|plaquettes| = ∑_S ∏_{r ∈ S} w̃_r
```

### Step 2 — Wilson correlator in raw cluster form

The Wilson correlator with observables `F_p, F_q` is:

```
⟨F_p · F_q⟩_β = ∫ F(U_p) · F(U_q) · ∏_r (1 + w̃_r(U_r)) dHaar
              = ∑_S ∫ F(U_p) · F(U_q) · ∏_{r ∈ S} w̃_r dHaar
```

So `⟨F_p F_q⟩ = ∑_S ⟨F_p F_q · ∏_{r ∈ S} w̃_r⟩` (where `⟨·⟩` denotes Haar
expectation).

### Step 3 — Möbius inversion on partition lattice

The **connected correlator** is `⟨F_p ; F_q⟩ := ⟨F_p · F_q⟩ - ⟨F_p⟩ · ⟨F_q⟩`.
By Möbius inversion on the **partition lattice** of `S`, the connected
part of `∑_S ⟨F_p F_q · ∏ w̃⟩` extracts only the **connected** subsets `S`:

```
⟨F_p ; F_q⟩ = ∑_{Y polymer containing p, q} K(Y)
```

where the **truncated activity** `K(Y)` is:

```
K(Y) = ∑_{π partition of Y into blocks} μ(π) · ∏_{block β ∈ π} ⟨F · ∏_{r ∈ β} w̃⟩
```

with `μ(π)` the Möbius function of the partition lattice. This is the
**Mayer/Ursell identity**.

For polymers containing both `p` and `q`, the Möbius extraction picks
exactly the **connected parts**. The non-connected parts are killed by
the Möbius cancellation (i.e., disconnected `Y` give `K(Y) = 0`, which is
B.2's content).

### Step 4 — Identification with `TruncatedActivities.ofConnectedCardDecay`

The `TruncatedActivities.ofConnectedCardDecay` constructor (at
`MayerExpansion.lean:50ish`) takes:
- `K : Finset ι → ℝ` (the truncated activity)
- `p q : ι` (the connecting endpoints)
- `r A₀ : ℝ` (the bound constants from B.3 + B.4)
- `hr_nonneg : 0 ≤ r`, `hA_nonneg : 0 ≤ A₀`
- `hK_abs_le : |K(Y)| ≤ if (p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y) then A₀ * r^|Y| else 0`

and produces a `TruncatedActivities ι` structure. The `connectingSum` of
this structure is `∑_{Y connecting p, q} K(Y)` — exactly the right-hand
side of the Mayer identity.

So B.5 boils down to:

```
⟨F_p ; F_q⟩ = ∑_{Y connecting p, q} K(Y)
            = (TruncatedActivities.ofConnectedCardDecay K p q r A₀ ...).connectingSum p q
```

The first equality is the Mayer/Ursell identity (Step 3). The second is
the definitional unfolding of `connectingSum` — a near-tautology once the
definitions match.

### Single-line mathematical content of B.5

B.5 = "the Wilson connected correlator equals the sum-over-polymers of
the Möbius-truncated activity, identified with the project's
`TruncatedActivities.ofConnectedCardDecay` consumer-ready structure".

The Lean proof has **two halves**:

- **Möbius bookkeeping (~80 LOC)**: define `truncatedK` via Möbius
  inversion on the partition lattice; prove its key algebraic identity
  (the Mayer/Ursell identity)
- **BK identification (~120 LOC)**: chain `boltzmann_cluster_expansion_pointwise`
  with the Möbius identity; identify with `TruncatedActivities.ofConnectedCardDecay`;
  prove the connecting-sum equality

---

## (c) Connection to `dashboard/mayer_mathlib_precheck.md` has-vs-lacks table

The mayer Mathlib precheck (filed 20:20Z) classified Mathlib's BK / Möbius
/ partition-lattice readiness. The relevant rows for **B.5** are:

| Mathlib facility | Status | Relevance to B.5 |
|---|:---:|---|
| `Mathlib.Order.Partition.Finpartition` | **HAS** (partial) | Finite partitions of a `Finset`; needed for the partition-lattice Möbius sum |
| `Mathlib.Order.Partition.PartitionLattice` (or equivalent) | **PARTIAL** — Mathlib has Möbius for general posets but not the partition-lattice instance with connected-cumulant structure | This is the core gap; project-side Möbius wrapper required (~30 LOC) |
| `Möbius` for arithmetic functions | **HAS** | Wrong flavor — arithmetic Möbius vs. partition-lattice Möbius |
| `ArithmeticFunction.moebius` | **HAS** | Same — wrong flavor |
| Project's `boltzmann_cluster_expansion_pointwise` (`MayerIdentity.lean:138`) | **HAS** | The keystone B.5 chains with |
| Project's `wilsonConnectedCorr` definition | **HAS** (consuming `wilsonConnectedCorr`) | The LHS of the identity |
| Project's `wilsonPlaquetteEnergy_continuous` | **HAS** | Continuity prerequisite for the identity's integral arguments |
| Project's `plaquetteFluctuationNorm` (`ZeroMeanCancellation.lean:126`) | **HAS** | The variable `w̃` |
| Project's `plaquetteFluctuationRaw_zero_beta` | **HAS** (`MayerIdentity.lean:101`) | β = 0 sanity check (not strictly needed but useful for testing) |
| Project's `TruncatedActivities` structure (`MayerExpansion.lean:50`) | **HAS** | Target structure |
| Project's `TruncatedActivities.ofConnectedCardDecay` constructor | **HAS** (`ClusterRpowBridge.lean:1738` per dependency map) | The actual constructor B.5 instantiates |
| Project's `TruncatedActivities.connectingSum` | **HAS** (`MayerExpansion.lean:103`) | The RHS function |
| Project's `B.1 truncatedK_zero_of_card_one` (forthcoming) | needed | Singleton vanishing (for Möbius cancellation) |
| Project's `B.2 truncatedK_zero_of_not_polymerConnected` (forthcoming) | needed | Disconnected vanishing (for Möbius cancellation) |
| Project's `B.3 truncatedK_abs_le_normSup_pow` (forthcoming) | needed | BK bound (for `hK_abs_le` field) |
| Project's `B.4 plaquetteFluctuationNorm_sup_le` (forthcoming) | needed | Sup bound (for explicit `r = 4 N_c β`) |

### What Mathlib LACKS (critical for B.5)

- **Partition-lattice Möbius with connected-cumulant structure**: Mathlib
  has `Finpartition` but the specific Möbius inversion on the partition
  lattice that extracts the connected cumulants is not formalized. The
  project's `MayerExpansion.lean` is the home-rolled wrapper, but it
  doesn't yet have the inversion identity itself. **~30 LOC project-side**
  to add the inversion.
- **Connected cumulant generating function**: a standard combinatorial
  primitive in statistical mechanics; not in Mathlib. Project's
  `wilsonClusterActivityRaw` (`MayerIdentity.lean:115`) is the raw
  un-truncated version; B.5 derives the **truncated** version.

### Conclusion

B.5 has **~30-50 LOC of project-side Möbius gap**. The Mathlib precheck's
"Most savings available" finding (line 168-176 of
`mayer_mathlib_precheck.md`) is the tree-count bound (relevant to B.3, not
B.5). For B.5 specifically, the Mathlib gap is the partition-lattice
Möbius instance — small (~30 LOC) but necessary.

The total **~200 LOC project-side** estimate for B.5 splits roughly:

- ~80 LOC Möbius bookkeeping (define `truncatedK` via inversion + prove
  the inversion identity + handle B.1/B.2 vanishing cases)
- ~120 LOC BK identification (chain with `boltzmann_cluster_expansion_pointwise`,
  identify with `TruncatedActivities.ofConnectedCardDecay`, prove
  `connectingSum` equality)

---

## (d) Decomposition into project-side ~200 LOC + Mathlib-side gaps

**Project-side LOC budget for B.5**: **~200 LOC** (per
`F3_MAYER_DEPENDENCY_MAP.md:242`):

### Phase 1 — Möbius bookkeeping (~80 LOC)

| Sub-step | LOC | Content |
|---|---:|---|
| `def partitionLatticeMoebius (Y : Finset Plaquette)` | ~15 | Möbius function on the partition lattice of `Y`; project-side wrapper around Mathlib's `Finpartition` |
| `def truncatedK (β : ℝ) (F : G → ℝ) (p q : Plaquette) : Finset Plaquette → ℝ` | ~25 | The Möbius inversion definition: `K(Y) = ∑_{π partition of Y} μ(π) · ∏_{block β ∈ π} ⟨F · ∏_{r ∈ β} w̃⟩` |
| `theorem truncatedK_eq_clustered_extraction` | ~20 | The Mayer/Ursell identity at the algebraic level: `∑_Y K(Y) = ⟨F_p ; F_q⟩` (connected correlator) |
| `theorem truncatedK_zero_of_card_one_via_Möbius` | ~10 | B.1 fits as a corollary: singleton partition has trivial Möbius weight, so `K({p}) = ⟨w̃_p⟩ = 0` |
| `theorem truncatedK_zero_of_not_polymerConnected_via_Möbius` | ~10 | B.2 fits as a corollary: disconnected `Y` gives Möbius cancellation across components |

### Phase 2 — BK identification (~120 LOC)

| Sub-step | LOC | Content |
|---|---:|---|
| `theorem truncatedK_abs_le_card_decay` | ~30 | Compose B.3 (`truncatedK_abs_le_normSup_pow`) with B.4 (`plaquetteFluctuationNorm_sup_le`) to get `|K(Y)| ≤ (4 N_c β)^|Y|` for connected `Y`; combine with B.1 + B.2 vanishing for the case-split shape of `hK_abs_le` |
| `theorem connectingSum_eq_sum_truncatedK` | ~20 | Definitional unfolding: `(TruncatedActivities.ofConnectedCardDecay K ...).connectingSum p q = ∑_{Y connecting p,q} K(Y)`; near-tautology |
| `theorem wilsonConnectedCorr_eq_connectingSum` | ~30 | The main identification: chain `boltzmann_cluster_expansion_pointwise` + Möbius inversion + `connectingSum_eq_sum_truncatedK` |
| `theorem truncatedK_satisfies_mayer_identity` (the B.5 target) | ~20 | Combine all the above into the structure-target shape; instantiate `TruncatedActivities.ofConnectedCardDecay` with `K`, `r = 4 N_c β`, `A₀ = 1`, and the bound proof |
| `#print axioms truncatedK_satisfies_mayer_identity` directive | ~1 | Pin oracle trace to `[propext, Classical.choice, Quot.sound]` |
| Doc comments + cross-references | ~19 | Mandatory disclaimer + cross-reference to keystone, B.1, B.2, B.3, B.4 scopes; cite Mayer/Ursell historical references; explain Möbius derivation |

**Risk profile**: MEDIUM-HIGH. Risks:

- **Möbius bookkeeping correctness**: Möbius inversion on the partition
  lattice has well-known sign-confusion pitfalls. The project must define
  the partition Möbius function unambiguously (probably via the standard
  inclusion-exclusion shape) and prove the inversion identity by
  induction on `|Y|`.
- **API shape match**: the Mayer identity must produce **exactly** the
  `TruncatedActivities.ofConnectedCardDecay` consumer shape. Any
  off-by-one in the field names, the constants `r` and `A₀`, or the
  sign conventions will fail.
- **B.1 + B.2 + B.3 + B.4 dependencies**: B.5 cites all four prior
  theorems. If any of them changes shape (e.g., B.4 hypothesis tightens
  to `β < 1/(2 N_c)` per `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001`),
  B.5's signature must be updated too.

**Where B.5 is harder than B.6**: B.6 is pure glue (~50 LOC, no math).
B.5 is **~200 LOC of identity-rewriting** — the substantive
combinatorial Lean content that B.6 then bundles.

**Where B.5 is easier than B.3**: B.3 is the analytic estimation
(convergence theorem). B.5 is identity-rewriting (no convergence
question, just algebraic manipulation). B.3 has the `1/|T|` cancellation
magic step; B.5 has the Möbius-inversion sign cancellations.

---

## (e) Klarner-Ursell pairing role — B.5 introduces `truncatedK` formally

After B.5 lands, the F3-MAYER side has:

- `truncatedK β F p q : Finset Plaquette → ℝ` (the Mayer activity, defined
  via Möbius inversion)
- `truncatedK_satisfies_mayer_identity` (the identity proven)
- `truncatedK_zero_of_card_one` (B.1; corollary of the Möbius identity)
- `truncatedK_zero_of_not_polymerConnected` (B.2; corollary of the Möbius
  identity)
- `truncatedK_abs_le_normSup_pow` (B.3; the BK polymer bound)
- `truncatedK_abs_le_card_decay` (B.5's intermediate; combines B.3 + B.4)

These five theorems collectively **formally define the truncated activity
function `K` and prove all its properties** needed by
`TruncatedActivities.ofConnectedCardDecay`. B.6 then bundles them:

```
physicalConnectedCardDecayMayerWitness
  := { K := truncatedK β F p q
     , hK_abs_le := truncatedK_abs_le_card_decay β F p q
     , h_mayer := truncatedK_satisfies_mayer_identity β F p q
     }
```

(plus the trivial `hr_nonneg = by positivity` and `hA_nonneg = zero_le_one`).

After B.6 lands, the full Klarner-Ursell pairing fires:

```
∑_{Y polymer connecting p, q} |K_β(Y)|
  ≤ ∑_n count(n; p, q) · (4 N_c β)^n           [B.3 + B.4]
  ≤ ∑_n K^n · (4 N_c β)^n                       [Klarner: count ≤ K^n]
  = 1 / (1 − K · 4 N_c β)                       [geometric series]
  finite ⟺ β < 1/(28 N_c)                       [K = 7]
```

**B.5's specific role**: it is the **single theorem** that defines
`truncatedK` formally and proves the Mayer/Ursell identity. Without B.5,
the project has no formal `K` function, and B.3/B.4 cannot bound it.
B.5 is thus the **structural keystone** of the F3-MAYER side — the entry
point for everything else.

**B.5 vs B.3 distinction**: B.5 is *identity-rewriting* (defines K, proves
the Mayer identity). B.3 is *analytic estimation* (bounds K). They are
complementary: B.5 introduces the object; B.3 estimates it.

---

## Summary table — pre-supplied API surface for §(b)/B.5

| Section | Identifier | File:line | Role in §(b)/B.5 |
|---|---|---|---|
| (a) signature | `truncatedK_satisfies_mayer_identity` | (proposed) `MayerInversion.lean` (~200 LOC) or appended to `MayerExpansion.lean` | The B.5 target |
| (b) keystone | `boltzmann_cluster_expansion_pointwise` | `MayerIdentity.lean:138` | Already proved; the algebraic identity B.5 chains with |
| (b) raw activity | `wilsonClusterActivityRaw` | `MayerIdentity.lean:115` | Project-internal raw (un-truncated) version |
| (b) raw fluctuation | `plaquetteFluctuationRaw` | `MayerIdentity.lean:88` | Pre-normalised |
| (b) raw vanishing | `plaquetteFluctuationRaw_zero_beta` | `MayerIdentity.lean:101` | β = 0 sanity check |
| (b) variable | `plaquetteFluctuationNorm` | `ZeroMeanCancellation.lean:126` | The `w̃` |
| (b) keystone for B.1 | `plaquetteFluctuationNorm_mean_zero` | `ZeroMeanCancellation.lean:142` | Already proved; used in Möbius cancellation for singleton |
| (b) target structure | `ConnectedCardDecayMayerData` | `ClusterRpowBridge.lean:2229` | Where B.5 plugs in via B.6 |
| (b) target constructor | `TruncatedActivities.ofConnectedCardDecay` | `ClusterRpowBridge.lean:1738` (per dependency map) | The actual constructor |
| (b) target struct base | `TruncatedActivities` | `MayerExpansion.lean:50` | The base structure |
| (b) connectingSum | `TruncatedActivities.connectingSum` | `MayerExpansion.lean:103` | The RHS function |
| (b) Möbius wrapper (NEW) | `partitionLatticeMoebius` | (proposed) `MayerInversion.lean` | Project-side wrapper around `Finpartition` |
| (b) truncatedK def (NEW) | `truncatedK β F p q` | (proposed) `MayerInversion.lean` | The Möbius-extracted Mayer activity |
| (b) truncatedK identity (NEW) | `truncatedK_eq_clustered_extraction` | (proposed) `MayerInversion.lean` | Algebraic Mayer/Ursell at the function level |
| (b) hK_abs_le bridge (NEW) | `truncatedK_abs_le_card_decay` | (proposed) `MayerInversion.lean` | Composes B.3 + B.4 + B.1/B.2 vanishing |
| (b) connecting sum identification (NEW) | `wilsonConnectedCorr_eq_connectingSum` | (proposed) `MayerInversion.lean` | Chains all of the above |
| (e) consumer | `ConnectedCardDecayMayerData.h_mayer` | `ClusterRpowBridge.lean:2245` | The field B.5 inhabits (via B.6) |
| (e) terminal | `clayMassGap_of_shiftedF3MayerCountPackageExp` | `ClusterRpowBridge.lean:4855` | Final assembly |

---

## What this scope does NOT do

- **Does not prove** `truncatedK_satisfies_mayer_identity` or any of the
  Möbius sublemmas.
- **Does not move** F3-MAYER from `BLOCKED`.
- **Does not move** F3-COUNT (still `CONDITIONAL_BRIDGE`).
- **Does not move** any percentage (5% / 28% / 23-25% / 50% all preserved).
- **Does not assume** F3-COUNT or B.1 + B.2 + B.3 + B.4 has closed; B.5
  is conditional on all four prerequisites.
- **Does not silently fix** the carried-over hypothesis-strength flag
  from B.4; B.5's signature should match B.4's `β < 1/(2 N_c)` choice.

The scope is purely a **forward-looking implementation blueprint** for
Codex to pick up **after** F3-COUNT moves to FORMAL_KERNEL and B.1 + B.2
+ B.3 + B.4 land.

---

## Honesty preservation

- F3-MAYER row: unchanged (`BLOCKED`)
- F3-COUNT row: unchanged (`CONDITIONAL_BRIDGE`)
- F3-COMBINED row: unchanged (`BLOCKED`)
- All 4 percentages: unchanged at 5% / 28% / 23-25% / 50%
- Tier 2 axiom count: unchanged at 4
- README badges: unchanged
- This document is a **forward-looking blueprint**, not a proof artifact.

---

## 🏁 F3-MAYER scope corpus: COMPLETE after this delivery

After B.5 is filed, **all 6 F3-MAYER theorems are scoped**:

| Theorem | LOC | Status |
|---|---:|---|
| B.1 single-vertex | ~30 | scoped (`f3_mayer_b1_scope.md`) |
| B.2 disconnected polymers | ~150 | scoped (`f3_mayer_b2_scope.md`) |
| B.3 BK polymer bound (analytic boss) | ~250 | scoped (`f3_mayer_b3_scope.md`) |
| B.4 sup bound | ~80 | scoped (`f3_mayer_b4_scope.md`; hypothesis-flag pending) |
| **B.5 Mayer/Ursell identity** | **~200** | **scoped (this delivery; FINAL)** |
| B.6 bundled witness (glue) | ~50 | scoped (`f3_mayer_b6_scope.md`) |
| **Total** | **~760** | **6 of 6 scoped** |

**F3-MAYER pre-supply pattern's scoping phase: COMPLETE.** Codex inherits
the full 6-theorem implementation roadmap (~760 LOC project-side) when
F3-COUNT closes. This matches BLUEPRINT_F3Mayer's ~700 LOC estimate
within rounding.

---

## Cross-references

- `F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 221-242 — B.5 official entry
- `BLUEPRINT_F3Mayer.md` §2 (lines 180-238) — Mayer/Ursell identity
  exposition
- `BLUEPRINT_F3Mayer.md` §4.1 file (1) — `MayerInterpolation.lean`
  (B.5's home)
- `dashboard/f3_mayer_b1_scope.md` — sibling B.1 scope (singleton
  vanishing; corollary of B.5)
- `dashboard/f3_mayer_b2_scope.md` — sibling B.2 scope (disconnected
  vanishing; corollary of B.5)
- `dashboard/f3_mayer_b3_scope.md` — sibling B.3 scope (BK polymer
  bound; bounds B.5's `K`)
- `dashboard/f3_mayer_b4_scope.md` — sibling B.4 scope (sup bound;
  composes with B.3 in B.5's `truncatedK_abs_le_card_decay`; hypothesis-flag
  pending)
- `dashboard/f3_mayer_b6_scope.md` — sibling B.6 scope (bundled witness;
  consumes B.5's `truncatedK` + `truncatedK_satisfies_mayer_identity`)
- `dashboard/mayer_mathlib_precheck.md` — Mathlib has-vs-lacks 13-row
  table; B.5 has ~30 LOC project-side Möbius gap
- `YangMills/ClayCore/MayerIdentity.lean:138` — keystone
  `boltzmann_cluster_expansion_pointwise`
- `YangMills/ClayCore/MayerIdentity.lean:88` — `plaquetteFluctuationRaw`
- `YangMills/ClayCore/MayerIdentity.lean:115` — `wilsonClusterActivityRaw`
- `YangMills/ClayCore/MayerExpansion.lean:50` — `TruncatedActivities`
  structure
- `YangMills/ClayCore/MayerExpansion.lean:103` — `connectingSum`
- `YangMills/ClayCore/ZeroMeanCancellation.lean:126` —
  `plaquetteFluctuationNorm`
- `YangMills/ClayCore/ZeroMeanCancellation.lean:142` —
  `plaquetteFluctuationNorm_mean_zero` (used in B.1 corollary via Möbius)
- `YangMills/ClayCore/ClusterRpowBridge.lean:2229` —
  `ConnectedCardDecayMayerData` target structure
- `YangMills/ClayCore/ClusterRpowBridge.lean:1738` (per dependency
  map) — `TruncatedActivities.ofConnectedCardDecay` constructor
- Mayer & Mayer 1940: J.E. Mayer, M.G. Mayer, *Statistical Mechanics*
  (Wiley, 1940) — original Mayer expansion
- Ursell 1927: H.D. Ursell, "*The evaluation of Gibbs' phase-integral for
  imperfect gases*", Math. Proc. Cambridge Philos. Soc. **23** (1927),
  685-697 — original Ursell expansion
- Brydges 1986: D. Brydges, "*A short course on cluster expansions*", in
  *Phénomènes critiques, systèmes aléatoires, théories de jauge* (Les
  Houches XLIII), 129-183 — modern exposition
- `UNCONDITIONALITY_LEDGER.md:88` — F3-COUNT row (`CONDITIONAL_BRIDGE`)
- `UNCONDITIONALITY_LEDGER.md:89` — F3-MAYER row (`BLOCKED`)
- `UNCONDITIONALITY_LEDGER.md:90` — F3-COMBINED row (`BLOCKED`; β <
  1/(28 N_c) regime)
- `REC-CODEX-MAYER-MATHLIB-CAYLEY-OR-PRUFER-001` (OPEN priority 6) — Cayley
  formula recommendation; not needed for B.5 (B.3-relevant)
- `REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001` (OPEN priority
  7) — BK formula project-side recommendation; not directly needed for
  B.5 (B.3-relevant) but related
- `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001` (OPEN priority 7) —
  carried-over hypothesis flag from B.4

---

## Recommended implementation order (preserved from B.3 scope)

`B.1 → B.4 → B.2 → B.5 → B.3 → B.6`

**B.5 is in the middle**, not last. Rationale:
- B.1, B.4, B.2 establish the foundation (keystone + sup bound +
  measure-theoretic infra)
- **B.5 introduces `truncatedK` formally** — the object that B.3 then
  bounds and B.6 then bundles
- B.3 (analytic boss) follows B.5 because it operates on the `truncatedK`
  defined in B.5
- B.6 (glue) is last

This ordering ensures each step builds on the prior steps' API and the
hardest analytic content (B.3) is tackled when the most infrastructure
is in place.
