# F3-MAYER §(b)/B.6 — Bundled `ConnectedCardDecayMayerData` Witness Scope

**Cowork-authored Codex-ready signature scaffold for F3-MAYER §(b)/B.6.**

**Author**: Cowork
**Created**: 2026-04-27T04:25:00Z (under `COWORK-F3-MAYER-B6-SCOPE-001`)
**Status**: **forward-looking blueprint only**. F3-MAYER is `BLOCKED` (gated on F3-COUNT closure first per LEDGER:88). §(b)/B.6 is **OPEN** and is the natural **terminal** glue step — it is gated on B.1 + B.2 + B.3 + B.4 + B.5 all landing first. **Nothing in this document moves any LEDGER row or percentage.**

---

## Mandatory disclaimer

> **F3-MAYER row in `UNCONDITIONALITY_LEDGER.md` is `BLOCKED`** (gated on
> F3-COUNT row closure first). §(b)/B.6 is the **terminal** of six missing
> Mayer theorems — pure glue (~50 LOC) that bundles B.1-B.5 into the
> `ConnectedCardDecayMayerData` structure at `ClusterRpowBridge.lean:2229`
> consumed by the Klarner-Ursell pairing at line 4371 (`ofSubpackages`).
> This document scopes B.6 only as a Codex-ready implementation blueprint
> to be picked up *after* F3-COUNT closes and *after* B.1 + B.2 + B.3 + B.4
> + B.5 all land. **Nothing here moves the F3-MAYER row from `BLOCKED` or
> moves any percentage. All 4 percentages preserved at 5% / 28% / 23-25% /
> 50%.**

> **CARRIED-OVER FINDING**: the proposed signature in
> `F3_MAYER_DEPENDENCY_MAP.md:250` carries the same hypothesis-strength
> mismatch (`β < log(2)/N_c`) flagged for B.4 in
> `dashboard/f3_mayer_b4_scope.md` and tracked at
> `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001`. B.6's hypothesis must
> match B.4's whatever Codex chooses (recommended: `β < 1/(2 * N_c)`),
> since B.6 consumes B.4's bound directly.

---

## Context

`F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 145+ enumerates **six missing Mayer
theorems** B.1-B.6. Cowork has now scoped B.1 (`f3_mayer_b1_scope.md`,
single-vertex), B.2 (`f3_mayer_b2_scope.md`, disconnected polymer), B.4
(`f3_mayer_b4_scope.md`, sup bound). The present document covers the
**terminal sixth** case (bundled witness, EASY ~50 LOC), which is the pure
glue assembling B.1-B.5 into the consumer-ready structure.

| # | Theorem | Difficulty | Est. LOC | Status |
|---|---|---|---:|---|
| B.1 | Single-vertex truncated-K = 0 | EASY | ~30 | **scoped** in `f3_mayer_b1_scope.md` |
| B.2 | Disconnected-polymer truncated-K = 0 | MEDIUM | ~150 | **scoped** in `f3_mayer_b2_scope.md` |
| B.3 | BK polymer bound `|K(Y)| ≤ ‖w̃‖∞^|Y|` | HIGH | ~250 | not yet scoped (Mathlib precheck filed) |
| B.4 | Sup bound `‖w̃‖∞ ≤ 4 N_c · β` | EASY-MEDIUM | ~80 | **scoped** in `f3_mayer_b4_scope.md` |
| B.5 | Mayer/Ursell identity | MEDIUM-HIGH | ~200 | not yet scoped |
| **B.6** | **Bundled `ConnectedCardDecayMayerData` witness** | **EASY** | **~50** | **OPEN — this document** |

**Why B.6 last (terminal)**: B.6 is pure assembly. It instantiates the
3-field structure `ConnectedCardDecayMayerData N_c (4 N_c β) 1 (by
positivity) zero_le_one` by:
- Field `K` = the project-internal `truncatedK β F p q` (introduced in
  B.5)
- Field `hK_abs_le` = case-split combining B.1 (singleton vanishing), B.2
  (disconnected vanishing), B.3 (BK polymer bound) with B.4 (sup bound `r =
  4 N_c β`) on the connected case
- Field `h_mayer` = direct application of B.5

So **B.6 cannot start until B.1, B.2, B.3, B.4, B.5 all land**. Once they
do, B.6 is mechanical and the F3-MAYER side's contribution to
`clayMassGap_smallBeta_for_N_c` is complete. After B.6, F3-MAYER moves
from `BLOCKED` to `FORMAL_KERNEL` (subject to Cowork audit).

---

## (a) Precise Lean signature

The target witness (verbatim from `F3_MAYER_DEPENDENCY_MAP.md:249-253`):

```lean
def physicalConnectedCardDecayMayerWitness
    (N_c : ℕ) [NeZero N_c] (β : ℝ) (hβ : 0 < β) (hβ_small : β < Real.log 2 / N_c) :
    ConnectedCardDecayMayerData N_c (4 * N_c * β) 1
      (by positivity) zero_le_one
```

**⚠ CARRIED-OVER HYPOTHESIS FLAG**: per the B.4 scope, `β < log(2)/N_c` is
too weak for the algebra-of-exponentials body. **Cowork recommends** the
corrected signature (matching B.4's recommended hypothesis):

```lean
def physicalConnectedCardDecayMayerWitness
    (N_c : ℕ) [NeZero N_c] (β : ℝ) (hβ : 0 < β) (hβ_small : β < 1 / (2 * N_c)) :
    ConnectedCardDecayMayerData N_c (4 * N_c * β) 1
      (by positivity) zero_le_one
```

The constants are fixed by the structure target:
- `r = 4 * N_c * β` — supplied by B.4 (sup bound)
- `A₀ = 1` — universal constant; the inequality `|K(Y)| ≤ 1 · r^|Y|` is
  what B.3 + B.4 jointly establish
- `hr_nonneg : 0 ≤ r` — `by positivity` since `β > 0` and `N_c ≥ 1`
- `hA_nonneg : 0 ≤ 1` — `zero_le_one`

**File location** (proposed): adjacent to `ConnectedCardDecayMayerData` in
`YangMills/ClayCore/ClusterRpowBridge.lean` around line 2300 (inside
`namespace ConnectedCardDecayMayerData` or right after it). Alternatively
in a fresh file `YangMills/ClayCore/MayerB6BundledWitness.lean` if Codex
prefers separation; B.6 is small enough that either location works.

---

## (b) Statement of the structure-assembly argument (B.6 fragment)

The target `ConnectedCardDecayMayerData N_c r A₀ hr_nonneg hA_nonneg` is
defined at `ClusterRpowBridge.lean:2229` as a 3-field structure:

| Field | Type | Mathematical content |
|---|---|---|
| `K` | `∀ {d L} ... β F p q Y → ℝ` | The Mayer/Ursell truncated activity |
| `hK_abs_le` | `∀ ... \|K β F p q Y\| ≤ if (p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y) then A₀ * r^Y.card else 0` | The BK-style polymer bound, with auto-zero on disconnected/non-anchored polymers |
| `h_mayer` | `... → wilsonConnectedCorr (...) = (TruncatedActivities.ofConnectedCardDecay K p q r A₀ ...).connectingSum p q` | The Mayer/Ursell identity |

### B.6 assembly (instantiates each field)

**Field 1: `K`**:
```lean
K := fun β F p q Y => truncatedK β F p q Y
```

This is the project-internal Mayer truncated activity (introduced
implicitly by B.5's signature). The `K` field is just the function `truncatedK`
which Codex constructs in B.5; B.6 plugs it in.

**Field 2: `hK_abs_le`** (the BK bound, with case-split):

The `hK_abs_le` field requires showing `|K(Y)| ≤ if (p ∈ Y ∧ q ∈ Y ∧
PolymerConnected Y) then A₀ * r^|Y| else 0`. Case-split:

- **Case `p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y`**: apply B.3
  `truncatedK_abs_le_normSup_pow` to get `|K(Y)| ≤ ‖w̃‖∞^|Y|`, then apply
  B.4 `plaquetteFluctuationNorm_sup_le` to get `‖w̃‖∞^|Y| ≤ (4 N_c β)^|Y|
  = r^|Y|`. Use `A₀ = 1` so the bound becomes `≤ 1 * r^|Y| = r^|Y|`.
  Combine: `|K(Y)| ≤ r^|Y|`. ✓

- **Case `¬ (p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y)`** — sub-cases:
  - **`Y` is a single vertex**: B.1 `truncatedK_zero_of_card_one` gives
    `K(Y) = 0`, so `|K(Y)| = 0 ≤ 0`. ✓
  - **`Y` is not polymer-connected**: B.2
    `truncatedK_zero_of_not_polymerConnected` gives `K(Y) = 0`, so
    `|K(Y)| = 0 ≤ 0`. ✓
  - **`p ∉ Y` or `q ∉ Y`** (other negations of the conjunct): need
    additional vanishing argument. **This is a sub-case Codex must
    handle**: when the polymer doesn't contain both endpoints, the
    truncated activity doesn't appear in the cluster sum, so
    by-convention `K(Y) = 0` for these cases — but this convention must
    be explicit in B.5's definition of `truncatedK`. If B.5 defines
    `truncatedK` to vanish off-anchored polymers, this sub-case is
    immediate; if not, an additional lemma is needed.

**Field 3: `h_mayer`**: direct application of B.5
`truncatedK_satisfies_mayer_identity`. The B.5 signature already produces
exactly the Mayer/Ursell identity in the shape required by `h_mayer`. ✓

### Single-line mathematical content

B.6 = "the three fields of `ConnectedCardDecayMayerData` are inhabited by
direct case-analysis on B.1-B.5". No new mathematical content; pure
elementary glue.

---

## (c) Connection to `dashboard/mayer_mathlib_precheck.md` has-vs-lacks table

The mayer Mathlib precheck (filed 20:20Z) classified Mathlib's BK / Möbius
/ Haar factorisation readiness into 13 rows. The relevant rows for **B.6**
are:

| Mathlib facility | Status | Relevance to B.6 |
|---|:---:|---|
| `Finset.card_eq_one`, `Finset.card_eq_zero` (case-split on polymer cardinality) | **HAS** | Used in B.6 case-split for `Y` singleton vs nonempty disconnected |
| `if-then-else` rewriting (`if_pos`, `if_neg`) | **HAS** | Required to dispatch the case-split in `hK_abs_le` |
| `pow_nonneg`, `pow_le_pow_left` (monotonicity of `r^|Y|`) | **HAS** | B.4 → B.6 chain: `(4 N_c β)^|Y|` step |
| `abs_le_of_le` / `abs_nonneg` | **HAS** | For `\|K(Y)\| ≤ 0 ⇒ K(Y) = 0` direction |
| `by positivity` tactic for `0 ≤ 4 N_c β` | **HAS** | Discharges `hr_nonneg` directly |
| `zero_le_one` | **HAS** | Discharges `hA_nonneg` directly |
| Project's `B.1` `truncatedK_zero_of_card_one` (forthcoming) | needed | Singleton vanishing |
| Project's `B.2` `truncatedK_zero_of_not_polymerConnected` (forthcoming) | needed | Disconnected vanishing |
| Project's `B.3` `truncatedK_abs_le_normSup_pow` (forthcoming) | needed | BK polymer bound |
| Project's `B.4` `plaquetteFluctuationNorm_sup_le` (forthcoming) | needed | Sup bound supplying `r = 4 N_c β` |
| Project's `B.5` `truncatedK_satisfies_mayer_identity` (forthcoming) | needed | The Mayer/Ursell identity itself |
| Project's `ConnectedCardDecayMayerData` structure | **HAS** | Target; defined `ClusterRpowBridge.lean:2229` |
| Project's `ofSubpackages` combinator | **HAS** | Downstream consumer; defined `ClusterRpowBridge.lean:4371` |

### What Mathlib LACKS (critical for B.6)

**Nothing.** B.6 is purely project-internal glue using only B.1-B.5 as
inputs. No Mathlib gaps are introduced.

### Conclusion

B.6 has **zero strict Mathlib gaps**. The only dependencies are project-
internal forthcoming theorems (B.1-B.5). Once they all land, B.6 is
mechanical case-analysis with `by positivity` and `zero_le_one`
discharging the trivial structure fields.

This makes B.6 the **lowest-risk** of the six theorems: no new mathematics,
no measure-theoretic subtleties, no algebra-of-exponentials, no
combinatorics. Just `def ... := ⟨..., ..., ...⟩` with three
trivially-discharged Lean-level proofs.

---

## (d) Decomposition into project-side ~50 LOC + Mathlib-side gaps

**Project-side LOC budget for B.6**: **~50 LOC** (per
`F3_MAYER_DEPENDENCY_MAP.md:257`):

| Sub-step | LOC | Content |
|---|---:|---|
| `def physicalConnectedCardDecayMayerWitness` declaration with structure target and named hypotheses | ~5 | Standard `def` with explicit type signature |
| `K` field instantiation: `fun β F p q Y => truncatedK β F p q Y` | ~3 | Direct plug-in of B.5's `truncatedK` |
| `hK_abs_le` field — case-split on `(p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y)` | ~25 | Use `if_pos`/`if_neg`; positive case applies B.3 + B.4 (~10 LOC); negative case sub-splits on `Y.card = 1` vs `Y.card ≥ 2 ∧ ¬connected` vs `p ∉ Y ∨ q ∉ Y` (~15 LOC) — the last sub-case may require auxiliary B.5 corollary depending on `truncatedK` definition |
| `h_mayer` field — direct application of B.5 | ~5 | One-line `exact B.5_theorem ...` |
| `hr_nonneg : 0 ≤ 4 * N_c * β` field — `by positivity` | ~1 | Auto-discharged |
| `hA_nonneg : 0 ≤ 1` field — `zero_le_one` | ~1 | Auto-discharged |
| `#print axioms physicalConnectedCardDecayMayerWitness` directive | ~1 | Pin to `[propext, Classical.choice, Quot.sound]` |
| Doc comments + cross-references | ~9 | Mandatory disclaimer + B.1-B.5 citations + `ofSubpackages` consumer note |

**Risk profile**: VERY LOW. Pure glue; no new mathematics; no
measure-theoretic subtleties; no Mathlib gaps; no combinatorics. The only
mild pitfall is the case-sub-split on the third disjunct of `¬ (p ∈ Y ∧ q
∈ Y ∧ PolymerConnected Y)` — the sub-case `p ∉ Y ∨ q ∉ Y` may need an
additional small lemma if B.5's `truncatedK` definition doesn't already
vanish off-anchored polymers by construction.

**Where B.6 is harder than nothing**: only the case-split bookkeeping. The
positive case is literally `B.3 ∘ B.4 ∘ pow_le_pow_left`; the negative
cases are `B.1` (singleton) and `B.2` (disconnected); the residual `p ∉ Y
∨ q ∉ Y` case is either definitional or one B.5-corollary lemma.

**Where B.6 is easier than every other B.\***:
- Easier than B.1 (which has the keystone application): B.6 has no fresh
  computation; B.1 has the unfold-and-rewrite step
- Easier than B.2 (Wilson-Haar Fubini): B.6 has no measure-theoretic
  argument
- Easier than B.3 (BK forest formula): B.6 has no random-walk machinery
- Easier than B.4 (algebra-of-exponentials): B.6 has no analytic
  inequality
- Easier than B.5 (Mayer/Ursell identity): B.6 doesn't need to prove the
  identity — it just uses B.5

This is exactly the "EASY" labeling in the dependency map: B.6 is glue that
collapses into ~50 LOC once the harder theorems exist.

---

## (e) Klarner-Ursell pairing terminus — B.6 produces the ultimate inhabitant

After B.1 + B.2 + B.3 + B.4 + B.5 land, B.6 produces an inhabitant of
`ConnectedCardDecayMayerData N_c (4 N_c β) 1 ...` at every `(N_c, β)` with
the smallness hypothesis. This inhabitant is the **F3-MAYER side input** to
the Klarner-Ursell pairing at `ofSubpackages` (`ClusterRpowBridge.lean:4371`):

```lean
def ofSubpackages
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackageExp)
    (hKr_lt1 : count.K * wab.r < 1) :
    ShiftedF3MayerCountPackageExp N_c wab
```

The pairing takes:
- `mayer` = a `ShiftedF3MayerPackage N_c wab` (which contains B.6's
  `ConnectedCardDecayMayerData` witness as its `data` field)
- `count` = a `ShiftedF3CountPackageExp` (which the F3-COUNT side
  produces from `ShiftedConnectingClusterCountBoundExp` once F3-COUNT B.2
  closes via the v2.71 chain)
- `hKr_lt1` = `count.K * wab.r < 1`, the geometric-series convergence
  threshold

For the specific physical assembly:
- `count.K = 7` (Klarner constant for d=4 lattice animals; this is what
  F3-COUNT delivers via the line-1096 consumer)
- `wab.r = 4 * N_c * β` (B.4's sup bound, threaded through B.6 via the
  `r` parameter)

The convergence condition `count.K * wab.r < 1` becomes:

```
7 * 4 * N_c * β < 1
⟺ β < 1 / (28 * N_c)
```

This is the **exact small-β regime** `β < 1/(28 N_c)` that the project's
`F3-COMBINED` LEDGER row (line 90) records:
`clayMassGap_smallBeta_for_N_c for N_c >= 2 at beta < 1/(28 N_c)`.

So B.6 is the **single point** where the F3-MAYER side connects to the
F3-COUNT side via `ofSubpackages`. Without B.6, no `ShiftedF3MayerPackage`
inhabitant exists, the pairing cannot be invoked, and `clayMassGap_smallBeta_for_N_c`
remains uninhabited even when both F3-COUNT and F3-MAYER (B.1-B.5)
individually close.

**Strategic note**: B.6 is the **last 50 LOC** between F3-COUNT closure +
B.1-B.5 closure and the F3-COMBINED row promotion. After B.6 lands, the
final assembly at `clayMassGap_of_shiftedF3MayerCountPackageExp`
(`ClusterRpowBridge.lean:4855`) is mechanical (the `ShiftedF3MayerCountPackageExp`
produces `ClayYangMillsMassGap N_c` at small β by direct construction).

---

## Summary table — pre-supplied API surface for §(b)/B.6

| Section | Identifier | File:line | Role in §(b)/B.6 |
|---|---|---|---|
| (a) signature | `physicalConnectedCardDecayMayerWitness` | (proposed) `ClusterRpowBridge.lean:2300` (in or near `namespace ConnectedCardDecayMayerData`) or `MayerB6BundledWitness.lean` | The B.6 target |
| (a) target structure | `ConnectedCardDecayMayerData` | `ClusterRpowBridge.lean:2229` | The structure to inhabit |
| (b) field 1 input | `truncatedK` (introduced by B.5) | (project-internal forthcoming) | The Mayer activity for `K` field |
| (b) field 2 case (positive) input | `truncatedK_abs_le_normSup_pow` (B.3) + `plaquetteFluctuationNorm_sup_le` (B.4) | (forthcoming) | BK bound × sup bound for connected case |
| (b) field 2 case (singleton) input | `truncatedK_zero_of_card_one` (B.1) | (forthcoming) | Singleton vanishing |
| (b) field 2 case (disconnected) input | `truncatedK_zero_of_not_polymerConnected` (B.2) | (forthcoming) | Disconnected vanishing |
| (b) field 3 input | `truncatedK_satisfies_mayer_identity` (B.5) | (forthcoming) | Mayer/Ursell identity |
| (e) consumer | `ShiftedF3MayerPackage.data` field, then `ofSubpackages` | `ClusterRpowBridge.lean:4371` | Pairs Mayer + Count |
| (e) terminal | `clayMassGap_of_shiftedF3MayerCountPackageExp` | `ClusterRpowBridge.lean:4855` | Produces `ClayYangMillsMassGap N_c` |

---

## What this scope does NOT do

- **Does not prove** `physicalConnectedCardDecayMayerWitness`.
- **Does not move** F3-MAYER from `BLOCKED`.
- **Does not move** F3-COUNT (still `CONDITIONAL_BRIDGE` until residual-
  extension compatibility theorem proves).
- **Does not move** F3-COMBINED (still `BLOCKED` per LEDGER:90).
- **Does not move** any percentage (5% / 28% / 23-25% / 50% all preserved).
- **Does not assume** F3-COUNT or B.1-B.5 has closed; this scope is
  conditional on all six prerequisites.
- **Does not silently fix** the carried-over hypothesis-strength mismatch;
  it flags the issue and points to the existing
  `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001`.

The scope is purely a **forward-looking implementation blueprint** for
Codex to pick up **after** F3-COUNT moves to FORMAL_KERNEL and B.1-B.5 land.

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

## Cross-references

- `F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 244-259 — B.6 official entry
- `F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 145-148 — full B.1-B.6 roster
- `dashboard/f3_mayer_b1_scope.md` — sibling B.1 scope (single-vertex
  vanishing; ~30 LOC)
- `dashboard/f3_mayer_b2_scope.md` — sibling B.2 scope (disconnected
  polymers; ~150 LOC)
- `dashboard/f3_mayer_b4_scope.md` — sibling B.4 scope (sup bound; ~80 LOC;
  flagged hypothesis-strength mismatch carried forward to B.6)
- `dashboard/mayer_mathlib_precheck.md` — Mathlib has-vs-lacks 13-row
  table; B.6 has zero strict Mathlib gaps (purely project-internal glue)
- `YangMills/ClayCore/ClusterRpowBridge.lean:2229` — `ConnectedCardDecayMayerData`
  target structure (3 fields)
- `YangMills/ClayCore/ClusterRpowBridge.lean:2257` — `namespace ConnectedCardDecayMayerData`
  start (B.6 fits inside or right after this namespace)
- `YangMills/ClayCore/ClusterRpowBridge.lean:2261-2272` — `toTruncatedActivities`
  conversion to `TruncatedActivities`
- `YangMills/ClayCore/ClusterRpowBridge.lean:4371` — `ofSubpackages`
  combinator (downstream consumer)
- `YangMills/ClayCore/ClusterRpowBridge.lean:4855` — `clayMassGap_of_shiftedF3MayerCountPackageExp`
  terminal endpoint
- `BLUEPRINT_F3Mayer.md` §4.1 file (4) — original ~100 LOC sketch that
  shrinks to ~50 LOC once `ofSubpackages` exists
- `UNCONDITIONALITY_LEDGER.md:88` — F3-COUNT row (`CONDITIONAL_BRIDGE`)
- `UNCONDITIONALITY_LEDGER.md:89` — F3-MAYER row (`BLOCKED on F3-COUNT
  closure first`)
- `UNCONDITIONALITY_LEDGER.md:90` — F3-COMBINED row (`BLOCKED`; small-β
  regime `β < 1/(28 N_c)`)
- `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001` (OPEN) — tracks the
  hypothesis-strength mismatch carried forward to B.6

---

## F3-MAYER scope corpus completion status (post-B.6)

After B.6 is filed, **4 of 6 MAYER theorems** are scoped:

| Theorem | Status |
|---|---|
| B.1 single-vertex | **scoped** |
| B.2 disconnected polymers | **scoped** |
| B.4 sup bound | **scoped** (hypothesis-flag pending) |
| **B.6 bundled witness** | **scoped (this delivery)** |
| B.3 BK polymer bound (HIGH ~250 LOC) | not yet scoped |
| B.5 Mayer/Ursell identity (MEDIUM-HIGH ~200 LOC) | not yet scoped |

Remaining MAYER scoping work: B.3 + B.5 (the 2 hardest theorems, total
~450 LOC). Both are deferred until F3-COUNT closes since they will be
implemented after the Mayer side unblocks. The Mathlib precheck filed at
20:20Z already maps the B.3 Mathlib gap landscape (zero matches for
Brydges-Kennedy / forest-formula content); when B.3 is scoped, Cowork
has the precheck to draw from.

The 4 scoped theorems collectively represent **~310 LOC** of forward-
planned project-side Lean work, with explicit Klarner-Ursell pairing logic
making it auditable that the geometric-series threshold `β < 1/(28 N_c)`
falls out of the final assembly. Without these scopes, Codex would have
to re-derive the assembly logic from scratch when starting MAYER
implementation; with them, the pre-supply pattern saves several Codex
implementation cycles.
