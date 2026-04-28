# F3-MAYER §(b)/B.3 — BK Polymer Bound Scope (the analytic boss)

**Cowork-authored Codex-ready signature scaffold for F3-MAYER §(b)/B.3.**

**Author**: Cowork
**Created**: 2026-04-27T05:20:00Z (under `COWORK-F3-MAYER-B3-SCOPE-001`)
**Status**: **forward-looking blueprint only**. F3-MAYER is `BLOCKED` (gated on F3-COUNT closure first per LEDGER:88). §(b)/B.3 is **OPEN** — the **HIGHEST-difficulty** of the six MAYER theorems and the analytic boss of the F3-MAYER side. Nothing in this document moves any LEDGER row or percentage.

---

## Mandatory disclaimer

> **F3-MAYER row in `UNCONDITIONALITY_LEDGER.md` is `BLOCKED`** (gated on
> F3-COUNT row closure first). §(b)/B.3 is the **HIGHEST-difficulty** of
> six missing Mayer theorems — the Brydges-Kennedy random-walk
> interpolation formula proving the polymer bound `|K(Y)| ≤ ‖w̃‖∞^|Y|`.
> This document scopes B.3 only as a Codex-ready implementation blueprint
> to be picked up *after* (1) F3-COUNT closes, (2) B.1 + B.2 + B.4 +
> (likely) B.5 land, and (3) Codex has bandwidth for ~250 LOC of analytic
> Lean work. **B.3 is not the small-LOC sibling of B.4** — it is
> substantively the largest analytic content piece in the entire MAYER
> blueprint (BLUEPRINT_F3Mayer §3.1, §3.2). **Nothing here moves the
> F3-MAYER row from `BLOCKED` or moves any percentage. All 4 percentages
> preserved at 5% / 28% / 23-25% / 50%.**

---

## Context

`F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 145+ enumerates **six missing Mayer
theorems** B.1-B.6. Cowork has now scoped B.1, B.2, B.4, B.6 (4 of 6); the
present document covers the **HIGHEST-difficulty** sixth case (the BK
polymer bound, ~250 LOC HIGH). After this document plus the B.5 scope
(MEDIUM-HIGH ~200 LOC, queued), all 6 MAYER theorems will be scoped.

| # | Theorem | Difficulty | Est. LOC | Status |
|---|---|---|---:|---|
| B.1 | Single-vertex truncated-K = 0 | EASY | ~30 | **scoped** in `f3_mayer_b1_scope.md` |
| B.2 | Disconnected-polymer truncated-K = 0 | MEDIUM | ~150 | **scoped** in `f3_mayer_b2_scope.md` |
| **B.3** | **BK polymer bound `|K(Y)| ≤ ‖w̃‖∞^|Y|`** | **HIGH** | **~250** | **OPEN — this document** |
| B.4 | Sup bound `‖w̃‖∞ ≤ 4 N_c · β` | EASY-MEDIUM | ~80 | **scoped** in `f3_mayer_b4_scope.md` (hypothesis-flag pending) |
| B.5 | Mayer/Ursell identity | MEDIUM-HIGH | ~200 | not yet scoped (META-12 seed `COWORK-F3-MAYER-B5-SCOPE-001` pending) |
| B.6 | Bundled witness | EASY (glue) | ~50 | **scoped** in `f3_mayer_b6_scope.md` |

**B.3 is the analytic boss**: it is the only one of the six theorems whose
mathematical content is **research-level statistical mechanics**
(Brydges-Kennedy 1987 / Battle-Federbush). Mathlib has **zero** content in
this area (per `dashboard/mayer_mathlib_precheck.md` §(b)); B.3 is fully
project-side. The existing recommendation `REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001`
(OPEN priority 7) recommends keeping B.3 project-side rather than attempting
an upstream Mathlib PR.

---

## (a) Precise Lean signature

The target theorem (verbatim from `F3_MAYER_DEPENDENCY_MAP.md:189-194`):

```lean
theorem truncatedK_abs_le_normSup_pow
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (F : G → ℝ) (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L))
    (hY_conn : PolymerConnected Y) :
    |truncatedK β F p q Y| ≤ ‖plaquetteFluctuationNorm N_c β‖_∞ ^ Y.card
```

**Carried-over hypothesis flag from B.4**: per `f3_mayer_b4_scope.md` and
`REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001`, B.3 should also use the
corrected smallness hypothesis (consistent with downstream B.6 `r = 4 N_c
β` consumption); add `(hβ : β > 0)` and `(hβ_small : β < 1 / (2 * N_c))`
if B.3 needs the `‖w̃‖∞` bound rather than just an abstract value.

**Signature note on `‖·‖∞` form**: matches the form recommended in
`f3_mayer_b4_scope.md` for downstream consistency. Use
`MeasureTheory.essSup` over `sunHaarProb N_c` (continuous on compact ⇒ essSup
= sup).

**File location** (proposed per BLUEPRINT_F3Mayer §4.1 file (3)):
`YangMills/ClayCore/BrydgesKennedyEstimate.lean` (~250 LOC). This matches
the BLUEPRINT's 4-file plan (`MayerInterpolation.lean`,
`HaarFactorization.lean`, `BrydgesKennedyEstimate.lean`,
`PhysicalConnectedCardDecayWitness.lean` — the last is B.6's home per the
B.6 scope).

---

## (b) Statement of the BK random-walk argument (B.3 fragment)

The mathematical content of B.3 is the **Brydges-Kennedy theorem** (BK
1987 §3, Thm 3.1) which **avoids the `|Y|!` blowup** that a naive Möbius
inversion would give.

### Naive bound (does not work)

A direct Möbius inversion gives:

```
|K(Y)| ≤ (number of partitions of Y) · ‖w̃‖∞^|Y|
       ≤ Bell(|Y|) · ‖w̃‖∞^|Y|
       ≤ |Y|! · ‖w̃‖∞^|Y|
```

Super-exponential in `|Y|`. **Unsummable** in the cluster-expansion sum
∑ count(Y) · |K(Y)| even with Klarner's `count(Y) ≤ K^|Y|`.

### BK reorganization (the working bound)

BK reorganizes the sum by **trees on Y** instead of **partitions of Y**.
Define the interpolated correlator:

```
Φ(s_1, ..., s_{|Y|−1}) = ⟨F_p F_q · ∏_{r ∈ Y} (1 + s_r · w̃(U_r))⟩
```

parameterised by `s_r ∈ [0, 1]` for each `r ∈ Y \ {p, q}`. Then the
truncated activity has the BK formula:

```
K(Y) = ∫_0^1 ... ∫_0^1 (∏ ds_r) · ∂/∂s_{r_1} ∂/∂s_{r_2} ... Φ
```

with bookkeeping over **forests on Y**.

Equivalently (Battle-Federbush form):

```
K(Y) = ∑_{T tree on Y} (1/|T|) · ∫ (∏ over edges of T) ⟨...⟩
```

### Why `|Y|^|Y|` collapses to 1

Cayley's formula gives `|Y|^(|Y|−2)` trees. The naive bound from
Battle-Federbush would give `|Y|^|Y|` after multiplying by some weight. BK
shows that with the `1/|T|` weight (and the zero-mean cancellation of
single-vertex blocks from B.1), the final estimate is:

```
|K(Y)| ≤ ‖w̃‖∞^|Y|
```

**No factorial. No `|Y|^|Y|`. No tree count appears in the final
estimate** — the BK bookkeeping cancels it.

This is the core BK theorem (BK 1987 §3, Thm 3.1). The Lean proof must
formalize this combinatorial cancellation argument.

### Single-line mathematical content of B.3

B.3 = "the BK random-walk / forest formula reorganization of `K(Y)` plus
the `1/|T|` weight cancellation gives `|K(Y)| ≤ ‖w̃‖∞^|Y|` for connected
polymers `Y`". The Lean proof is the formalization of this BK theorem
(~250 LOC, the largest analytic content in the F3-MAYER blueprint).

---

## (c) Connection to `dashboard/mayer_mathlib_precheck.md` has-vs-lacks table

The mayer Mathlib precheck (filed 20:20Z, audited at
`COWORK-MAYER-MATHLIB-PRECHECK-001`) classified Mathlib's BK / Möbius /
forest-formula readiness. The relevant rows for **B.3** are:

| Mathlib facility | Status | Relevance to B.3 |
|---|:---:|---|
| `Mathlib.Combinatorics.SimpleGraph.Acyclic` (`SimpleGraph.IsTree`, `IsAcyclic`) | **HAS** | Tree predicate; needed for the trees-on-Y enumeration |
| `Mathlib.Combinatorics.SimpleGraph.Walk.IsPath` | **HAS** | For tree-on-Y construction |
| `MeasureTheory.Measure.pi` (product measure on finite product spaces) | **HAS** | Required for the integral identity over `[0,1]^(|Y|−1)` |
| `MeasureTheory.integral_prod` (Fubini for product measures) | **HAS** | Required to swap the BK integration order |
| Project's `plaquetteFluctuationNorm` (`ZeroMeanCancellation.lean:126`) | **HAS** | The variable `w̃` |
| Project's `plaquetteFluctuationNorm_mean_zero` (`ZeroMeanCancellation.lean:142`) | **HAS** | The keystone (single-vertex K = 0; needed for BK cancellation argument) |
| Project's `truncatedK β F p q` (introduced in B.5) | (forthcoming) | The Mayer activity |
| Project's `B.4 plaquetteFluctuationNorm_sup_le` | (forthcoming) | If B.3 wants concrete `r = 4 N_c β`; if B.3 just bounds by `‖w̃‖∞^|Y|` abstractly, B.4 not strictly needed |
| **BK interpolation formula** (Brydges-Kennedy 1987) | **LACKS** (zero matches) | **THIS IS THE PROJECT-SIDE WORK** |
| **Mayer/Ursell identity** | **LACKS** (zero matches) | NOT directly needed for B.3; B.5's territory |
| **Cayley's formula** `|spanning_trees(K_n)| = n^(n-2)` | **LACKS** | NOT strictly needed — the loose bound `tree_count ≤ |Y|^(|Y|-2)` suffices, and even that loose bound can be avoided since BK doesn't use the tree count in the final estimate |
| Project-side spanning-tree enumeration | **LACKS** | NOT strictly needed (loose bound suffices); ~50-150 LOC project-side workaround if needed |

### What Mathlib LACKS (critical for B.3)

- **Brydges-Kennedy interpolation formula proper**: zero matches in
  Mathlib for `Brydges`, `brydges`, `forestFormula`, `forest_formula`,
  `Mayer`, `Ursell` (statistical-mechanics flavor; `Mayer-Vietoris` in
  sheaf cohomology is unrelated). The canonical reference (Brydges-Kennedy
  J. Stat. Phys. 48, 1987) has not been formalized in any Lean project.
- **Polymer/cluster expansion** infrastructure: zero matches for
  `cluster_expansion`, `clusterExpansion`, `polymer_expansion`. The
  project's existing `MayerExpansion.lean` (`TruncatedActivities` structure)
  is the only project-internal wrapper.
- **Möbius inversion on partition lattice with connected-cumulant
  structure**: not in Mathlib in the form needed.

### Conclusion

B.3 has **massive Mathlib gaps**. The recommendation `REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001`
(OPEN priority 7) explicitly recommends **project-side implementation
rather than upstream Mathlib PR** — the analytic content is too
specialized (statistical mechanics) to expect rapid Mathlib acceptance,
and an upstream PR would be ~600-1000 LOC, multi-month, and likely meet
Mathlib reviewer skepticism.

The ~250 LOC project-side estimate stands. The Mathlib precheck's "Most
expensive gap" finding (line 158-166 of `mayer_mathlib_precheck.md`) names
the BK interpolation formula as the most expensive gap in any project work
to date.

---

## (d) Decomposition into project-side ~250 LOC + Mathlib-side gaps

**Project-side LOC budget for B.3**: **~250 LOC** (per
`F3_MAYER_DEPENDENCY_MAP.md:202` and BLUEPRINT_F3Mayer §4.1 file (3)):

| Sub-step | LOC | Content |
|---|---:|---|
| `def interpolatedClusterAverage (Y : Finset Plaquette) (s : Y → ℝ) → ℝ` | ~30 | The polynomial Φ in `s_r ∈ [0,1]`; multiplicative product `∏_{r ∈ Y} (1 + s_r · w̃(U_r))` integrated against Haar |
| `def truncatedKFromInterpolation (β F p q Y) : ℝ` | ~40 | The BK formula: ∫_0^1 ... ∫_0^1 (∏ ds_r) · partial-derivatives of Φ; needs Lean infrastructure for partial derivatives of polynomials |
| `theorem truncatedKFromInterpolation_eq_truncatedK` | ~30 | Equivalence of the BK-interpolation form with the project's `truncatedK` (via Möbius inversion or direct expansion) |
| `def treesOnY (Y : Finset Plaquette) : Finset (SimpleGraph Y)` | ~25 | Spanning trees of the complete graph on `Y` (for the forest-formula sum); use `SimpleGraph.IsTree` predicate |
| `theorem treesOnY_card_le_loose_bound` | ~15 | Loose bound `|treesOnY Y| ≤ |Y|^(|Y|-2)` (or even `≤ |Y|!`; the BK estimate doesn't use the count tightly) |
| `theorem K_battle_federbush_form` | ~50 | The Battle-Federbush expansion: `K(Y) = ∑_{T tree on Y} (1/|T|) · ∫ (∏ over edges of T) ⟨...⟩`; this is the bulk of the BK derivation |
| `theorem K_abs_le_pointwise_pow` | ~30 | Pointwise bound: `|K(Y)| ≤ Σ_T (1/|T|) · ‖w̃‖∞^|Y|`; uses the keystone `plaquetteFluctuationNorm_mean_zero` for single-vertex T cancellation |
| `theorem sum_inv_T_card_le_one` | ~20 | The BK cancellation: `Σ_T (1/|T|) ≤ 1` for trees on Y; this is where the `|Y|^|Y|` blowup is killed |
| `theorem truncatedK_abs_le_normSup_pow` (the B.3 target) | ~10 | Combine the above to get `|K(Y)| ≤ ‖w̃‖∞^|Y|` |
| `#print axioms truncatedK_abs_le_normSup_pow` directive | ~1 | Pin oracle trace to `[propext, Classical.choice, Quot.sound]` |
| Doc comments + cross-references | ~9 | Mandatory disclaimer + cross-reference to keystone, B.1, B.2, B.4 scopes; cite Brydges-Kennedy 1987 §3 Thm 3.1 |

**Risk profile**: HIGH. This is the single largest analytic Lean theorem
in the F3-MAYER blueprint. Risks:
- **Combinatorial bookkeeping**: the BK forest sum requires careful
  Finset manipulation; small index errors can derail the proof.
- **Polynomial calculus**: partial derivatives of `Φ(s_1, ..., s_{|Y|-1})`
  need Lean's polynomial-derivative or function-derivative API; choose
  carefully (project-side vs. Mathlib chains).
- **Tree-on-Y enumeration**: project-side construction of `treesOnY` may
  hit Mathlib gaps (no direct enumeration, only predicate). The
  workaround (use loose bound) avoids this but the bookkeeping still
  needs the tree predicate to exist.
- **The 1/|T| weight cancellation**: this is the magical step where
  `|Y|^|Y|` collapses to 1. If formalized as the cancellation Σ_T (1/|T|)
  ≤ 1, it's a finite combinatorial inequality, but proving it requires
  a specific reorganization of the BK forest sum.

**Where B.3 is harder than B.5**: B.5 (Mayer/Ursell identity) reorganizes
the connected correlator into the sum-over-polymers form using Möbius
inversion. B.3 takes that polymer activity `K(Y)` and bounds it. B.5 is
identity-rewriting (~200 LOC); B.3 is analytic estimation (~250 LOC). B.3
is the actual "convergence-of-the-cluster-expansion" theorem.

**Where B.3 is harder than every other B.\***:
- Harder than B.1 (singleton vanishing): B.1 uses keystone directly; B.3
  uses keystone in a complex BK reorganization
- Harder than B.2 (disconnected vanishing): B.2 uses Wilson-Haar
  factorisation; B.3 uses BK random-walk interpolation
- Harder than B.4 (sup bound): B.4 is algebra of exponentials on a single
  plaquette; B.3 is the reorganization of all polymer integrals
- Harder than B.5 (Mayer/Ursell identity): B.5 is identity-rewriting; B.3
  is analytic estimation
- Harder than B.6 (bundled witness): B.6 is glue (~50 LOC); B.3 is
  ~250 LOC of analytic Lean

This is exactly the "HIGH" labeling in the dependency map.

---

## (e) Klarner-Ursell pairing role — B.3 supplies the `r^|Y|` decay

After B.1 + B.2 + B.3 + B.4 (and B.5, B.6) lands, the F3-MAYER side
produces an inhabitant of `ConnectedCardDecayMayerData N_c (4 N_c β) 1
hr_nonneg hA_nonneg` (`ClusterRpowBridge.lean:2229`). The F3-COUNT side
produces a `ShiftedConnectingClusterCountBoundExp`.

The **Klarner-Ursell pairing**:

```
∑_{Y polymer connecting p,q} |K_β(Y)|
  ≤ ∑_n count(n; p, q) · ‖w̃‖∞^n        (B.3 supplies ‖w̃‖∞^|Y|; B.2 zeros disconnected)
  ≤ ∑_n count(n; p, q) · (4 N_c β)^n    (B.4 substitutes ‖w̃‖∞ ≤ 4 N_c β)
  ≤ ∑_n K^n · (4 N_c β)^n               (Klarner: count ≤ K^n)
  = 1 / (1 − K · 4 N_c β)               (geometric series)
  finite ⟺ K · 4 N_c β < 1
  ⟺ β < 1 / (28 N_c)                    (with K = 7 for d = 4)
```

**B.3's specific role**: it is the **single theorem** that translates
"`K(Y)` is a complex-looking polymer activity" into the **clean
exponentially-decaying bound** `|K(Y)| ≤ ‖w̃‖∞^|Y|`. Without B.3, the
sum-over-polymers cannot be bounded by a geometric series — it would have
the `|Y|!` blowup that destroys convergence.

**Without B.3, the entire cluster expansion does not converge.** B.3 is
the "convergence theorem" of the cluster expansion. It is the single
analytic piece that justifies all of F3-MAYER + F3-COMBINED's small-β
machinery. If B.3 fails (e.g., a counterexample), the project would have
to use a different cluster-expansion technique entirely (chessboard
estimates, transfer-matrix spectral analysis, etc., per
`OUT-STRONG-COUPLING` LEDGER row).

---

## Summary table — pre-supplied API surface for §(b)/B.3

| Section | Identifier | File:line | Role in §(b)/B.3 |
|---|---|---|---|
| (a) signature | `truncatedK_abs_le_normSup_pow` | (proposed) `BrydgesKennedyEstimate.lean` (~250 LOC) per BLUEPRINT_F3Mayer §4.1 file (3) | The B.3 target |
| (b) interpolation form (NEW) | `interpolatedClusterAverage` | (proposed) same file or `MayerInterpolation.lean` per BLUEPRINT §4.1 file (1) | The polynomial Φ in `s_r ∈ [0,1]` |
| (b) BK formula (NEW) | `truncatedKFromInterpolation` | (proposed) same | The `K(Y) = ∫ ds · ∂Φ` integral identity |
| (b) keystone | `plaquetteFluctuationNorm_mean_zero` | `ZeroMeanCancellation.lean:142` | Already proved; used in BK cancellation step |
| (b) variable | `plaquetteFluctuationNorm` | `ZeroMeanCancellation.lean:126` | The `w̃` |
| (b) tree predicate | `SimpleGraph.IsTree` | `Mathlib.Combinatorics.SimpleGraph.Acyclic` | Used in `treesOnY` enumeration |
| (b) trees-on-Y (NEW) | `treesOnY (Y : Finset Plaquette)` | (proposed) same | Spanning trees of complete graph on `Y` |
| (b) loose tree-count bound (NEW) | `treesOnY_card_le_loose_bound` | (proposed) same | `|treesOnY Y| ≤ |Y|^(|Y|-2)` (loose; not strictly needed but useful) |
| (b) Battle-Federbush form (NEW) | `K_battle_federbush_form` | (proposed) same | `K(Y) = Σ_T (1/|T|) · ∫ (∏ over edges of T)` |
| (b) BK cancellation (NEW) | `sum_inv_T_card_le_one` | (proposed) same | `Σ_T (1/|T|) ≤ 1` (the magical step) |
| (b) target | `truncatedK_abs_le_normSup_pow` | (proposed) same | The B.3 target proper |
| (e) consumer | `hK_abs_le` field of `ConnectedCardDecayMayerData` | `ClusterRpowBridge.lean:2237` | Where B.3 plugs in (when paired with B.4 for the explicit `r = 4 N_c β` substitution) |
| (e) terminal | `clayMassGap_of_shiftedF3MayerCountPackageExp` | `ClusterRpowBridge.lean:4855` | Final assembly |

---

## What this scope does NOT do

- **Does not prove** `truncatedK_abs_le_normSup_pow`.
- **Does not prove** any of the BK sublemmas (`interpolatedClusterAverage`,
  `truncatedKFromInterpolation_eq_truncatedK`, `K_battle_federbush_form`,
  `sum_inv_T_card_le_one`).
- **Does not move** F3-MAYER from `BLOCKED`.
- **Does not move** F3-COUNT (still `CONDITIONAL_BRIDGE`).
- **Does not move** any percentage (5% / 28% / 23-25% / 50% all preserved).
- **Does not assume** F3-COUNT or B.1 + B.2 + B.4 + B.5 has closed; this
  scope is conditional on all five prerequisites (since B.3's proof
  refers to keystone from B.1 and uses `truncatedK` from B.5).
- **Does not silently fix** the carried-over hypothesis-strength flag
  from B.4; B.3's smallness hypothesis (if needed for the explicit `r =
  4 N_c β` substitution) should match B.4's recommended `β < 1/(2 N_c)`.

The scope is purely a **forward-looking implementation blueprint** for
Codex to pick up **after** F3-COUNT moves to FORMAL_KERNEL and B.1 + B.2
+ B.4 + B.5 land.

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

- `F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 184-203 — B.3 official entry
- `BLUEPRINT_F3Mayer.md` §3 (lines 240-336) — the full BK strategy
  exposition
- `BLUEPRINT_F3Mayer.md` §3.1 (lines 242-261) — Brydges-Kennedy
  interpolation formula
- `BLUEPRINT_F3Mayer.md` §3.2 (lines 263-281) — why BK avoids the |Y|!
  blowup
- `BLUEPRINT_F3Mayer.md` §4.1 file (3) (lines 360-365) — `BrydgesKennedyEstimate.lean`
  ~250 LOC plan
- `BLUEPRINT_F3Mayer.md` §4.3 (lines 382-406) — Mathlib gaps to expect
- `dashboard/f3_mayer_b1_scope.md` — sibling B.1 scope (single-vertex)
- `dashboard/f3_mayer_b2_scope.md` — sibling B.2 scope (disconnected)
- `dashboard/f3_mayer_b4_scope.md` — sibling B.4 scope (sup bound; supplies
  the explicit `r = 4 N_c β` for downstream consumption)
- `dashboard/f3_mayer_b6_scope.md` — sibling B.6 scope (bundled witness;
  consumes B.3 + B.4 jointly in `hK_abs_le` field)
- `dashboard/mayer_mathlib_precheck.md` — Mathlib has-vs-lacks 13-row
  table; B.3 has zero strict Mathlib content; project-side ~250 LOC
- `YangMills/ClayCore/ZeroMeanCancellation.lean:126` — `plaquetteFluctuationNorm`
- `YangMills/ClayCore/ZeroMeanCancellation.lean:142` — keystone `plaquetteFluctuationNorm_mean_zero`
  (used in BK cancellation step)
- `YangMills/ClayCore/ClusterRpowBridge.lean:2237` — `hK_abs_le` consumer
  field of `ConnectedCardDecayMayerData`
- Brydges-Kennedy 1987: D. Brydges, T. Kennedy, "Mayer expansions and
  the Hamilton-Jacobi equation", J. Stat. Phys. **48** (1987), 19-49 —
  the canonical reference. §3 Thm 3.1 is the BK polymer bound.
- Battle-Federbush form: G. Battle, P. Federbush, "A note on cluster
  expansions, tree graph identities, extra 1/N! factors!!!", Lett.
  Math. Phys. **8** (1984), 55-57 — equivalent reformulation.
- `UNCONDITIONALITY_LEDGER.md:88` — F3-COUNT row (`CONDITIONAL_BRIDGE`)
- `UNCONDITIONALITY_LEDGER.md:89` — F3-MAYER row (`BLOCKED`)
- `UNCONDITIONALITY_LEDGER.md:90` — F3-COMBINED row (`BLOCKED`; β <
  1/(28 N_c) regime)
- `REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001` (OPEN priority
  7) — recommendation to keep B.3 project-side
- `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001` (OPEN priority 7) —
  carried-over hypothesis flag from B.4
- `REC-CODEX-MAYER-MATHLIB-CAYLEY-OR-PRUFER-001` (OPEN priority 6) — Cayley's
  formula recommendation; **not strictly needed for B.3** since the loose
  tree-count bound suffices

---

## F3-MAYER scope corpus completion status (post-B.3)

After B.3 is filed, **5 of 6 MAYER theorems** are scoped:

| Theorem | Status |
|---|---|
| B.1 single-vertex | **scoped** |
| B.2 disconnected polymers | **scoped** |
| **B.3 BK polymer bound** | **scoped (this delivery)** |
| B.4 sup bound | **scoped** (hypothesis-flag pending) |
| B.5 Mayer/Ursell identity | not yet scoped (META-12 seed `COWORK-F3-MAYER-B5-SCOPE-001` queued) |
| B.6 bundled witness | **scoped** |

After B.5 lands, **all 6 MAYER theorems will be scoped** completing the
F3-MAYER pre-supply pattern. Total project-side LOC budget: ~30 + 150 +
**250** + 80 + 200 + 50 = **~760 LOC** of forward-planned project-side
Lean work, exactly matching BLUEPRINT_F3Mayer's ~700 LOC estimate.

---

## Recommended implementation order for Codex

When Codex starts F3-MAYER implementation (post-F3-COUNT closure), the
recommended order is:

1. **B.1** (~30 LOC EASY): keystone application; warm-up; validates the
   project's API for `truncatedK`
2. **B.4** (~80 LOC EASY-MEDIUM): sup bound; supplies the constant
   `r = 4 N_c β`
3. **B.2** (~150 LOC MEDIUM): Wilson-Haar factorisation; introduces the
   measure-theoretic infrastructure for B.3
4. **B.5** (~200 LOC MEDIUM-HIGH): Mayer/Ursell identity; introduces
   `truncatedK` formally; required for B.3's API surface
5. **B.3** (~250 LOC HIGH, this scope): the BK polymer bound; the
   analytic boss; depends on B.1 (keystone) + B.5 (`truncatedK` definition)
   + B.4 (concrete `r` substitution)
6. **B.6** (~50 LOC EASY glue): bundled witness; assembles all 5 prior
   theorems

This ordering ensures each step builds on the prior steps' API. **B.3
should be tackled last among the analytic theorems** because it's the
hardest and benefits most from the prior infrastructure. B.6 follows B.3
because B.6 is pure glue.
