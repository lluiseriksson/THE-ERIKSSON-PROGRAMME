# F3-MAYER §(b)/B.2 — Truncated-Activity Vanishing on Disconnected Polymers Scope

**Cowork-authored Codex-ready signature scaffold for F3-MAYER §(b)/B.2.**

**Author**: Cowork
**Created**: 2026-04-27T02:45:00Z (under `COWORK-F3-MAYER-B2-SCOPE-001`)
**Status**: **forward-looking blueprint only**. F3-MAYER is `BLOCKED` (gated on F3-COUNT closure first per LEDGER:98). §(b)/B.2 is **OPEN** and B.1 is **OPEN** (B.2 should be undertaken after B.1 lands). Nothing in this document moves any LEDGER row or percentage.

---

## Mandatory disclaimer

> **F3-MAYER row in `UNCONDITIONALITY_LEDGER.md` is `BLOCKED`** (gated on
> F3-COUNT row closure first). §(b)/B.2 is the **second** of six missing
> Mayer theorems and is the natural successor to B.1 once B.1 lands. This
> document scopes B.2 only as a Codex-ready implementation blueprint to be
> picked up *after* (1) F3-COUNT closes (Codex's reconstructive contract proof
> + B.2 word decoder), (2) `COWORK-AUDIT-FRESH-PERCENTAGE-MOVE-001` validates
> the F3-COUNT row promotion, and (3) B.1 lands per
> `dashboard/f3_mayer_b1_scope.md`. **Nothing here moves the F3-MAYER row from
> `BLOCKED` or moves any percentage. All 4 percentages preserved at 5% / 28% /
> 23-25% / 50%.**

---

## Context

`F3_MAYER_DEPENDENCY_MAP.md` §(b) (lines 145+) enumerates **six missing Mayer
theorems** B.1–B.6. `dashboard/f3_mayer_b1_scope.md` covers the easiest case
(single-vertex polymers, ~30 LOC). The present document covers the **second**
case (geometrically disconnected polymers, ~150 LOC, MEDIUM difficulty), which
is the first nontrivial Wilson-Haar factorisation step.

| # | Theorem | Difficulty | Est. LOC | Status |
|---|---|---|---:|---|
| B.1 | Truncated-activity vanishing on single-vertex polymers | EASY | ~30 | OPEN — scope `f3_mayer_b1_scope.md` |
| **B.2** | **Truncated-activity vanishing on disconnected polymers** | **MEDIUM** | **~150** | **OPEN — this document** |
| B.3 | BK polymer-bound `\|K(Y)\| ≤ ‖w̃‖_∞^\|Y\|` (analytic boss) | HIGH | ~250 | OPEN |
| B.4 | Sup bound `‖w̃‖_∞ ≤ 4 N_c · β` | EASY-MEDIUM | ~80 | OPEN |
| B.5 | Mayer/Ursell identity in project notation | MEDIUM-HIGH | ~200 | OPEN |
| B.6 | The bundled witness | EASY | ~50 | OPEN |

**Why B.2 next after B.1**: B.2 introduces the **Wilson-Haar factorisation**
machinery that B.3 and B.5 will reuse. B.1 only needs the keystone
`plaquetteFluctuationNorm_mean_zero`; B.2 additionally needs to express the
Wilson plaquette weight as a product over independent Haar coordinates and
push the integral through the product. Once B.2 lands, B.3 and B.5 can build
on the same factorisation API rather than re-deriving it.

---

## (a) Precise Lean signature

The target theorem (verbatim from `F3_MAYER_DEPENDENCY_MAP.md:170-175`):

```lean
theorem truncatedK_zero_of_not_polymerConnected
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (F : G → ℝ) (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L))
    (hY : ¬ PolymerConnected Y) :
    truncatedK β F p q Y = 0
```

In English: when the polymer `Y` is not nearest-neighbour connected (i.e. it
splits into ≥ 2 site-disjoint components in the lattice graph), the
truncated activity `K(Y)` is identically zero.

**File location** (proposed): a new helper file
`YangMills/ClayCore/MayerB2Disconnected.lean`, or an addition to the existing
`MayerExpansion.lean` adjacent to `TruncatedActivities` (line 50). The
disjoint-component decomposition can be packaged as its own section
`/-! ### Polymer-connected component decomposition -/`.

`PolymerConnected` itself is defined at
`YangMills/ClayCore/PolymerDiameterBound.lean:61` as

```lean
def PolymerConnected {d L : ℕ}
    (X : Finset (ConcretePlaquette d L)) : Prop :=
  ∀ p ∈ X, ∀ q ∈ X, ∃ path : List (ConcretePlaquette d L),
    path.head? = some p ∧
    path.getLast? = some q ∧
    path.Nodup ∧
    (∀ x ∈ path, x ∈ X) ∧
    List.IsChain (fun a b => siteLatticeDist a.site b.site ≤ 1) path
```

The negation `¬ PolymerConnected Y` therefore says: **there exist** `p₀, q₀ ∈ Y`
with no nearest-neighbour path inside `Y` joining them — i.e. `Y` splits into
at least two non-empty components.

---

## (b) Statement of the Wilson-Haar factorisation argument (B.2 fragment)

The mathematical content of B.2 is the standard observation that **the
Wilson plaquette weight is a product over plaquettes**, and the **Haar
measure on the configuration space is a product over independent link
variables**. So when a polymer `Y` splits into two site-disjoint subsets
`Y = Y₁ ⊔ Y₂` with `Y₁`, `Y₂` ≠ ∅, the integrand for `K(Y)` factorises:

```
∫ ∏_{p ∈ Y} w̃_p(U) dHaar(U)
  = ( ∫ ∏_{p ∈ Y₁} w̃_p dHaar_{links(Y₁)} )
  · ( ∫ ∏_{p ∈ Y₂} w̃_p dHaar_{links(Y₂)} )
```

**The keystone (already proved at `ZeroMeanCancellation.lean:142`)**:

```lean
theorem plaquetteFluctuationNorm_mean_zero :
    ∫ w̃_p dHaar = 0
```

The crucial **monomial extension** of the keystone (NOT yet proved; the
required B.2 sublemma):

```lean
theorem prod_plaquetteFluctuationNorm_mean_zero_of_nonempty
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (F : G → ℝ)
    (Y : Finset (ConcretePlaquette d L)) (hYne : Y.Nonempty) :
    ∫ U, (∏ p ∈ Y, plaquetteFluctuationNorm N_c β U) ∂(sunHaarProb N_c) = 0
```

Wait — this is wrong as stated. The product is over **plaquettes** but each
plaquette `p` involves its own SU(N_c) link variables, and Haar integration
is over *all* links. The correct shape is:

```lean
theorem prod_plaquetteFluctuationNorm_mean_zero_of_disjoint
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (F : G → ℝ)
    {Y₁ Y₂ : Finset (ConcretePlaquette d L)}
    (hdisj : siteDisjoint Y₁ Y₂)
    (hY₁ne : Y₁.Nonempty) :
    ∫ U, (∏ p ∈ Y₁ ∪ Y₂, w̃_p (U|_links(Y₁ ∪ Y₂))) dHaarConfig
    = (∫ ∏_{p ∈ Y₁} w̃_p dHaarConfig|_{links(Y₁)})
      · (∫ ∏_{p ∈ Y₂} w̃_p dHaarConfig|_{links(Y₂)})
```

and then the `Y₁` factor is zero because its integrand is a `w̃_p`-product
including the keystone-vanishing `w̃_{p_0}` for some fixed `p_0 ∈ Y₁`.

**The single-line mathematical content of B.2**: when `Y` splits into
site-disjoint `Y₁ ⊔ Y₂` (both non-empty, which is exactly the negation of
`PolymerConnected`), Haar factorises across the disjoint link sets, and
within `Y₁` the keystone (`mean_zero`) plus integrability gives a vanishing
factor, so the product is 0. The truncated activity `K(Y)` is built from
this product (after Möbius truncation), so `K(Y) = 0` follows.

---

## (c) Connection to `dashboard/mayer_mathlib_precheck.md` has-vs-lacks table

The mayer Mathlib precheck (filed 20:20Z, audited at
`COWORK-MAYER-MATHLIB-PRECHECK-001`) classified Mathlib's BK / Möbius / Haar
factorisation readiness into 13 rows. The relevant rows for **B.2** are:

| Mathlib facility | Status | Relevance to B.2 |
|---|:---:|---|
| `MeasureTheory.Measure.pi` (product measure on finite product spaces) | **HAS** | Needed for the disjoint-link Haar factorisation. |
| `MeasureTheory.integral_prod_mul` (integral of product = product of integrals on independent factors) | **HAS** in basic form (Fubini chain) | Direct primitive needed by B.2. |
| `IsCompact.integrableOn`, `Continuous.integrableOn_isFiniteMeasure` | **HAS** | Integrability prerequisite for Fubini. |
| Project's `plaquetteFluctuationNorm_mean_zero` (`ZeroMeanCancellation.lean:142`) | **HAS** | The keystone B.2 reduces to (within one factor). |
| Project's `plaquetteFluctuationNorm_integrable` (`ZeroMeanCancellation.lean:133`) | **HAS** | Integrability bound for Fubini. |
| **Wilson-specific** Haar factorisation across disjoint plaquette site sets | **LACKS** (project-side wrapper required) | **THIS IS THE BUSINESS END OF B.2** — ~80 LOC of project-side glue. |
| `Finset.prod_union` (product of disjoint Finset union = product of products) | **HAS** | Used to cleanly split `∏ p ∈ Y₁ ∪ Y₂`. |
| `Finset.disjoint_union_eq_left` / similar | **HAS** | Partition lemmas. |
| `BrydgesKennedyForest`, `MayerUrsell`, polymer-graph cluster-expansion | **LACKS** | NOT needed for B.2 (only B.3 / B.5 hit this gap). |

**Conclusion**: B.2 has **one Mathlib gap** — the Wilson-specific Haar
factorisation across disjoint plaquette sites — which is **necessarily
project-side** (because the Wilson plaquette weight is project-internal).
This is in line with `mayer_mathlib_precheck.md` §(b) line 156 ("Wilson-specific
wrapper" estimated at ~50 LOC project-side; B.2 may need ~80 LOC because it
also handles the polymer connectivity decomposition).

The harder Mathlib gaps (BK forest formula, Mayer/Ursell identity) do not
appear in B.2 — they appear in B.3 and B.5.

---

## (d) Decomposition into project-side ~150 LOC + Mathlib-side gaps

**Project-side LOC budget for B.2**: **~150 LOC** (per `F3_MAYER_DEPENDENCY_MAP.md:182`):

| Sub-step | LOC | Content |
|---|---:|---|
| Define `siteDisjoint` for two `Finset (ConcretePlaquette d L)` (or reuse existing) | ~10 | Sites of `Y₁` ∩ sites of `Y₂` = ∅ (link-disjointness as derived consequence) |
| Translate `¬ PolymerConnected Y` into `∃ Y₁ Y₂, Y = Y₁ ⊔ Y₂ ∧ Y₁.Nonempty ∧ Y₂.Nonempty ∧ siteDisjoint Y₁ Y₂` | ~30 | The decomposition lemma. Standard graph theory — pick one connected component as `Y₁`, complement (in `Y`) as `Y₂`. Both non-empty by the failure of connectivity. Site-disjoint by construction. |
| Wilson-Haar factorisation wrapper: `∫ (f|_{Y₁} · f|_{Y₂}) dHaar = (∫ f|_{Y₁} dHaar_{Y₁}) · (∫ f|_{Y₂} dHaar_{Y₂})` for site-disjoint `Y₁`, `Y₂` | ~60 | Uses `MeasureTheory.Measure.pi` and Fubini (`MeasureTheory.integral_prod`). Project-side wrapper because the Wilson plaquette → link mapping is project-internal. |
| Apply keystone `plaquetteFluctuationNorm_mean_zero` to one factor | ~20 | Pick any `p₀ ∈ Y₁` (`Y₁.Nonempty`); the `Y₁` integrand is `w̃_{p₀} · ∏_{p ∈ Y₁ \ {p₀}} w̃_p`; integrate over `links(p₀)` first using Fubini; the inner integral is `∫ w̃_{p₀} dHaar = 0` by keystone; the product collapses to 0. |
| Conclude `K(Y) = 0` for `¬ PolymerConnected Y` | ~15 | Möbius truncation on `Y` factors through the Möbius truncation on `Y₁` and `Y₂` (because Möbius respects disjoint unions); product of zero × anything = 0. |
| `#print axioms` directive | ~1 | Pin oracle trace to `[propext, Classical.choice, Quot.sound]` |
| Doc comments + cross-references | ~14 | Mandatory disclaimer + cross-reference to keystone, B.1, and `f3_mayer_b1_scope.md` |

**Mathlib-side gaps**: **NONE** for B.2 directly. All primitives in place:
- `MeasureTheory.Measure.pi` ✓
- `MeasureTheory.integral_prod` (Fubini for product measures) ✓
- `Finset.prod_union` ✓
- `Finset.card_eq_sum_ones`, `Finset.sum_powerset` (for Möbius bookkeeping) ✓
- Project keystone `plaquetteFluctuationNorm_mean_zero` ✓
- Project integrability `plaquetteFluctuationNorm_integrable` ✓

**Risk profile**: MEDIUM. The decomposition lemma (translating
`¬ PolymerConnected` into a disjoint-union witness) is elementary graph
theory but requires careful Lean bookkeeping. The Wilson-Haar factorisation
wrapper is project-internal but standard Fubini. No new mathematical content;
formalization of well-known facts.

**Where B.2 is harder than B.1**: B.1 needs only the keystone applied
directly. B.2 needs (a) the disjoint-component decomposition (graph-theoretic
unwrapping of `¬ PolymerConnected`), (b) the Wilson-Haar factorisation across
disjoint link sets (Fubini wrapper), (c) keystone applied within one factor.
Steps (a) and (b) are the "MEDIUM difficulty" content; step (c) is identical
to B.1.

---

## (e) Klarner-Ursell pairing argument (status preserved from B.1 scope)

After B.1 + B.2 (and the rest of B.3-B.6) lands, the F3-MAYER side produces
an inhabitant of `ConnectedCardDecayMayerData N_c (4 N_c β) 1 hr_nonneg
hA_nonneg` (`ClusterRpowBridge.lean:2229`). The F3-COUNT side (post-Codex
contract proof + B.2 word decoder) produces a
`ShiftedConnectingClusterCountBoundExp` (`LatticeAnimalCount.lean:1096`
consumer chain).

The **Klarner-Ursell pairing** (geometric series convergence at
`ShiftedF3MayerCountPackageExp.ofSubpackages`,
`ClusterRpowBridge.lean:4371`):

```
∑_{Y polymer connecting p,q} |K_β(Y)|
  = ∑_{Y connecting AND PolymerConnected} |K_β(Y)|        (B.2: disconnected polymers contribute 0)
  ≤ ∑_{Y connected} A₀ · r^|Y|                             (B.3 + cardinality bound)
  = A₀ · ∑_n count(n; p, q) · r^n
  ≤ A₀ · ∑_n K^n · r^n                                     (Klarner: count ≤ K^n)
  = A₀ · 1/(1 − K · r)                                     (geometric series!)
  = finite                                                  (when K · r < 1)
```

**B.2's role in the pairing**: B.2 is what justifies restricting the sum on
the LHS from "all polymers containing `p` and `q`" to "polymers that are
**polymer-connected** and contain `p` and `q`". Without B.2, the LHS sum
would include disconnected polymers and the F3-COUNT bound (which counts
*connected* lattice animals, not arbitrary subsets) would not apply directly.
**B.2 is the bridge that lets the connected-animal F3-COUNT bound be used in
the cluster-expansion sum.**

For the specific physical assembly, `K = 7` (Klarner constant for d=4 lattice
animals) and `r = 4 N_c · β` (B.4 bound). Smallness `K · r < 1` reduces to
`β < 1/(28 N_c)`.

**Strategic note**: the order B.1 → B.2 → B.4 → B.6 → B.3 → B.5 remains
recommended (easy/medium first to validate API; HIGH-difficulty B.3 +
MEDIUM-HIGH B.5 last when the rest of the structure is proved). B.2 is the
natural successor to B.1 because it (a) extends the keystone application
pattern from singletons to multi-component sets, (b) introduces the
Wilson-Haar factorisation infrastructure that B.3 and B.5 will reuse, (c)
unblocks the F3-COUNT/F3-MAYER pairing argument by restricting the sum to
connected polymers.

---

## Summary table — pre-supplied API surface for §(b)/B.2

| Section | Identifier | File:line | Role in §(b)/B.2 |
|---|---|---|---|
| (a) signature | `truncatedK_zero_of_not_polymerConnected` | (proposed) `MayerB2Disconnected.lean` or addition to `MayerExpansion.lean` | The B.2 target |
| (a) hypothesis | `PolymerConnected` (negation) | `PolymerDiameterBound.lean:61` | The hypothesis predicate (negated) |
| (b) keystone | `plaquetteFluctuationNorm_mean_zero` | `ZeroMeanCancellation.lean:142` | Already proved; B.2 reduces to applying it within one factor of a disjoint product |
| (b) integrability | `plaquetteFluctuationNorm_integrable` | `ZeroMeanCancellation.lean:133` | Required for Fubini in the factorisation step |
| (b) carrier | `plaquetteFluctuationNorm` | `ZeroMeanCancellation.lean:126` | The variable `w̃` |
| (b) decomposition (NEW sublemma) | `polymerNotConnected_iff_exists_disjoint_decomp` | (proposed) `MayerB2Disconnected.lean` | `¬ PolymerConnected Y ↔ ∃ Y₁ Y₂, Y = Y₁ ⊔ Y₂ ∧ Y₁.Nonempty ∧ Y₂.Nonempty ∧ siteDisjoint Y₁ Y₂` |
| (b) Wilson-Haar factorisation (NEW sublemma) | `wilsonHaar_integral_prod_disjoint_factor` | (proposed) `MayerB2Disconnected.lean` | Fubini wrapper specialised to disjoint plaquette site sets |
| (b) zero corollary (NEW sublemma) | `prod_w_tilde_integral_zero_of_left_factor_meanzero` | (proposed) `MayerB2Disconnected.lean` | Product `∫ ∏ w̃_p` = 0 when there's a non-empty `Y₁` factor |
| (b) truncation scaffold | `TruncatedActivities` | `MayerExpansion.lean:50` | Carrier structure where B.2 hooks in |
| (e) pairing target | `ConnectedCardDecayMayerData` | `ClusterRpowBridge.lean:2229` | F3-MAYER ultimate target structure |
| (e) consumer | `ClusterRpowBridge.lean:550` (`¬ PolymerConnected Y → K_bound Y = 0` hypothesis) | `ClusterRpowBridge.lean:550-651` | The exact existing consumer that requires B.2 |
| (e) Clay-facing assembly | `ShiftedF3MayerCountPackageExp` | `ClusterRpowBridge.lean:4355` | Pairs Mayer + Count packages |
| (e) terminal | `clayMassGap_of_shiftedF3MayerCountPackageExp` | `ClusterRpowBridge.lean:4855` | Produces `ClayYangMillsMassGap N_c` |

**Important consumer note**: `ClusterRpowBridge.lean:550` already has the
shape `¬ PolymerConnected Y → K_bound Y = 0` as a *hypothesis* of an
existing lemma. B.2 is therefore the proof of this hypothesis for the
specific `K_bound = truncatedK β F p q`. The consumer is wired up; B.2 closes
the gap.

---

## What this scope does NOT do

- **Does not prove** `truncatedK_zero_of_not_polymerConnected`.
- **Does not prove** the Wilson-Haar factorisation sublemma.
- **Does not prove** the polymer-not-connected disjoint-decomposition sublemma.
- **Does not move** F3-MAYER from `BLOCKED`.
- **Does not move** F3-COUNT (still `CONDITIONAL_BRIDGE` until Codex's
  reconstructive contract proof + B.2 word decoder lands).
- **Does not move** any percentage (5% / 28% / 23-25% / 50% all preserved).
- **Does not assume** F3-COUNT or B.1 has closed; this scope is conditional
  on both events.

The scope is purely a **forward-looking implementation blueprint** for Codex
to pick up **after** F3-COUNT moves to FORMAL_KERNEL and B.1 lands per
`f3_mayer_b1_scope.md`.

---

## Honesty preservation

- F3-MAYER row: unchanged (`BLOCKED`)
- F3-COUNT row: unchanged (`CONDITIONAL_BRIDGE`)
- F3-COMBINED row: unchanged (`BLOCKED`)
- All 4 percentages: unchanged at 5% / 28% / 23-25% / 50%
- Tier 2 axiom count: unchanged at 4 (per freshness audit-007)
- README badges: unchanged
- This document is a **forward-looking blueprint**, not a proof artifact.

---

## Cross-references

- `F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 165-182 — B.2 official entry
- `F3_MAYER_DEPENDENCY_MAP.md` §(a) lines 51-140 — already-proved A.0-A.7 scaffolding (B.2's keystone is at A.2 line 142)
- `dashboard/f3_mayer_b1_scope.md` — sibling B.1 scope (the prerequisite warm-up)
- `dashboard/mayer_mathlib_precheck.md` — Mathlib has-vs-lacks 13-row table; B.2 has zero strict Mathlib gaps but requires a Wilson-specific Fubini wrapper
- `dashboard/f3_decoder_iteration_scope.md` — F3-COUNT B.2 scope (different B.2 — F3-COUNT's anchored word decoder, not F3-MAYER's disconnected polymer)
- `YangMills/ClayCore/ZeroMeanCancellation.lean:142` — the keystone B.2 reduces to (within one factor)
- `YangMills/ClayCore/ZeroMeanCancellation.lean:133` — integrability prerequisite for Fubini
- `YangMills/ClayCore/PolymerDiameterBound.lean:61` — `PolymerConnected` definition (negated in B.2 hypothesis)
- `YangMills/ClayCore/MayerExpansion.lean:50` — `TruncatedActivities` scaffold
- `YangMills/ClayCore/ClusterRpowBridge.lean:550` — the consumer with `¬ PolymerConnected Y → K_bound Y = 0` hypothesis (B.2 is the proof of this hypothesis for `truncatedK β F p q`)
- `YangMills/ClayCore/ClusterRpowBridge.lean:2229` — `ConnectedCardDecayMayerData` ultimate target
- `BLUEPRINT_F3Mayer.md` — Brydges-Kennedy / Mayer / Ursell mathematical context
- `UNCONDITIONALITY_LEDGER.md:98` — F3-MAYER row (`BLOCKED on F3-COUNT closure first`)
- `REC-CODEX-MAYER-MATHLIB-CAYLEY-OR-PRUFER-001` (OPEN) — eventual Mathlib PR for B.5 forest-formula
- `REC-CODEX-MAYER-MATHLIB-BK-FORMULA-PROJECT-SIDE-001` (OPEN) — eventual project-side BK formula scope (for B.3)

---

## Naming-disambiguation note

**There are two distinct "B.2" steps in the project**, and they are easy to
confuse:

1. **F3-COUNT B.2** — the anchored word decoder for the lattice-animal count.
   This is the F3-COUNT side and is what Codex is currently working on
   (`CODEX-F3-RESIDUAL-PARENT-INVARIANT-001` IN_PROGRESS toward v2.66). It is
   scoped in `dashboard/f3_decoder_iteration_scope.md` and
   `dashboard/f3_decoder_iteration_skeleton.md`. **F3-COUNT B.2 must close
   before any F3-MAYER step is taken.**

2. **F3-MAYER §(b)/B.2** — disconnected polymer truncated-activity vanishing.
   This is the F3-MAYER side and is what the present document scopes. It is
   the **second** of six F3-MAYER theorems and is the natural follow-up to
   B.1 once F3-COUNT has been closed.

When this document says "B.2" without further qualification, it refers to
F3-MAYER §(b)/B.2 in the context of the F3-MAYER work plan. The F3-COUNT B.2
will be referred to as "Codex's reconstructive decoder" or "F3-COUNT B.2"
throughout the F3-MAYER scoping documents.
