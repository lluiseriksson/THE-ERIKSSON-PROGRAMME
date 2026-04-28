# F3-MAYER §(b)/B.4 — Sup Bound for Normalised Plaquette Fluctuation Scope

**Cowork-authored Codex-ready signature scaffold for F3-MAYER §(b)/B.4.**

**Author**: Cowork
**Created**: 2026-04-27T04:05:00Z (under `COWORK-F3-MAYER-B4-SCOPE-001`)
**Status**: **forward-looking blueprint only**. F3-MAYER is `BLOCKED` (gated on F3-COUNT closure first per LEDGER:88). §(b)/B.4 is **OPEN**, gated on B.1 + B.2 + (probably) B.3 landing first per the recommended order. **Nothing in this document moves any LEDGER row or percentage.**

---

## Mandatory disclaimer

> **F3-MAYER row in `UNCONDITIONALITY_LEDGER.md` is `BLOCKED`** (gated on
> F3-COUNT row closure first). §(b)/B.4 is the **fourth** of six missing
> Mayer theorems. It supplies the constant `r = 4 N_c · β` for the
> Klarner-Ursell geometric series and is "EASY-MEDIUM" difficulty in the
> recommended B.1 → B.2 → B.4 → B.6 → B.3 → B.5 closure order. This
> document scopes B.4 only as a Codex-ready implementation blueprint to be
> picked up *after* F3-COUNT closes (which now reduces to proving
> `PhysicalPlaquetteGraphResidualExtensionCompatibility1296` per the
> v2.71/v2.72 narrowing chain) and after B.1 + B.2 land per their own
> Cowork scopes. **Nothing here moves the F3-MAYER row from `BLOCKED` or
> moves any percentage. All 4 percentages preserved at 5% / 28% / 23-25% /
> 50%.**

> **IMPORTANT FINDING (flagged in section (c))**: the original proposed
> signature in `F3_MAYER_DEPENDENCY_MAP.md` used `β < log(2)/N_c`, which was
> too weak for the proof's `exp(2βN_c) − 1 ≤ 4βN_c` step.  The corrected B.4
> hypothesis is `β < 1/(2N_c)`; the final F3-COMBINED convergence regime
> remains the stronger `β < 1/(28N_c)`.  Tracked by
> `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001`.

---

## Context

`F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 145+ enumerates **six missing Mayer
theorems** B.1–B.6. `dashboard/f3_mayer_b1_scope.md` covers B.1 (single-vertex
truncated-K vanishing, EASY ~30 LOC), `dashboard/f3_mayer_b2_scope.md` covers
B.2 (disconnected polymers, MEDIUM ~150 LOC). The present document covers
the **fourth** case (sup bound on the normalised fluctuation, EASY-MEDIUM
~80 LOC), which is the natural next step after B.1 and B.2 in the
recommended easy-first closure order.

| # | Theorem | Difficulty | Est. LOC | Status |
|---|---|---|---:|---|
| B.1 | Single-vertex truncated-K = 0 | EASY | ~30 | **scoped** in `f3_mayer_b1_scope.md` |
| B.2 | Disconnected-polymer truncated-K = 0 | MEDIUM | ~150 | **scoped** in `f3_mayer_b2_scope.md` |
| B.3 | BK polymer bound `|K(Y)| ≤ ‖w̃‖∞^|Y|` | HIGH | ~250 | not yet scoped (Mathlib precheck filed) |
| **B.4** | **Sup bound `‖w̃‖∞ ≤ 4 N_c · β`** | **EASY-MEDIUM** | **~80** | **OPEN — this document** |
| B.5 | Mayer/Ursell identity | MEDIUM-HIGH | ~200 | not yet scoped |
| B.6 | Bundled witness | EASY | ~50 | scope queued (META-10 seed) |

**Why B.4 next after B.1/B.2**: B.4 is purely **algebra of exponentials**
on a single plaquette — no polymer combinatorics, no Wilson-Haar
factorisation, no random-walk machinery. It uses the SU(N_c) trace bound
`|Re tr U| ≤ N_c` plus elementary `exp(x) − 1 ≤ 2x` arithmetic. The
result `‖w̃‖∞ ≤ 4 N_c · β` supplies the constant `r` in the Klarner-Ursell
geometric-series convergence at `β < 1/(28 N_c)`. Once B.4 lands, B.6
(bundled witness) becomes pure glue.

---

## (a) Precise Lean signature

The target theorem (now matching the corrected `F3_MAYER_DEPENDENCY_MAP.md`
B.4 entry):

```lean
theorem plaquetteFluctuationNorm_sup_le
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (hβ : β > 0) (hβ_small : β < 1 / (2 * N_c)) :
    ‖plaquetteFluctuationNorm N_c β‖_∞ ≤ 4 * N_c * β
```

**Historical hypothesis mismatch flag**: the old proposed
`hβ_small : β < Real.log 2 / N_c` was **insufficient** for the
algebra-of-exponentials body. See section (c) for the analysis. The corrected
signature is:

```lean
theorem plaquetteFluctuationNorm_sup_le
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (hβ : β > 0) (hβ_small : β < 1 / (2 * N_c)) :
    ‖plaquetteFluctuationNorm N_c β‖_∞ ≤ 4 * N_c * β
```

**Note on `‖·‖∞`**: in the project's measure-theoretic context, this should
be `MeasureTheory.essSup` over `sunHaarProb N_c`. Since `plaquetteFluctuationNorm`
is continuous on the compact group `SU(N_c)`, the essential supremum equals
the iSup of the function, which equals its (attained) maximum on `SU(N_c)`.
Codex should choose between `essSup` (matches `‖·‖∞` notation; requires AE
machinery) or `iSup`-attainment (cleaner for continuous functions on
compact). The B.3 proof (HIGH) consumes essSup, so for downstream
consistency, Cowork recommends **`essSup` form**:

```lean
theorem plaquetteFluctuationNorm_essSup_le
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (hβ : β > 0) (hβ_small : β < 1 / (2 * N_c)) :
    MeasureTheory.essSup (fun U => ‖plaquetteFluctuationNorm N_c β U‖)
      (sunHaarProb N_c) ≤ 4 * N_c * β
```

**File location** (proposed): adjacent to `plaquetteFluctuationNorm` at
`YangMills/ClayCore/ZeroMeanCancellation.lean:126`, immediately after the
existing zero-mean and integrability lemmas at lines 130-159. The new
theorem fits at ~line 200 of that file.

`plaquetteFluctuationNorm` itself is defined at `ZeroMeanCancellation.lean:126`:

```lean
noncomputable def plaquetteFluctuationNorm (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    ↥(specialUnitaryGroup (Fin N_c) ℂ) → ℝ :=
  fun U => plaquetteWeight N_c β U / singlePlaquetteZ N_c β - 1
```

with `plaquetteWeight U = exp(-β · wilsonPlaquetteEnergy U) = exp(-β · Re tr U)`
per `WilsonPlaquetteEnergy.lean:36-38`.

---

## (b) Statement of the algebra-of-exponentials argument (B.4 fragment)

The mathematical content of B.4 is the standard observation that for
`U ∈ SU(N_c)`, the quantity `Re tr U` is bounded by `N_c` in absolute
value, and therefore the plaquette weight satisfies

```
exp(-β N_c) ≤ plaquetteWeight U ≤ exp(β N_c)
```

The single-plaquette partition function `Z_p(β) = ∫ plaquetteWeight dHaar`
is between these same bounds (since Haar is a probability measure), so

```
exp(-β N_c) ≤ Z_p(β) ≤ exp(β N_c)
```

The normalised fluctuation `w̃ = plaquetteWeight / Z_p − 1` is therefore
bounded:

```
exp(-β N_c) / exp(β N_c) − 1 ≤ w̃(U) ≤ exp(β N_c) / exp(-β N_c) − 1
exp(-2 β N_c) − 1               ≤ w̃(U) ≤ exp(2 β N_c) − 1
```

For `β > 0`, `|exp(-2 β N_c) − 1| < |exp(2 β N_c) − 1|`, so

```
|w̃(U)| ≤ exp(2 β N_c) − 1
```

uniformly in `U`. This gives the L∞ bound:

```
‖w̃‖∞ ≤ exp(2 β N_c) − 1
```

The final step uses **the elementary inequality** `exp(x) − 1 ≤ 2x` for
`x ∈ [0, 1]` (equivalently the bound `exp(x) ≤ 1 + 2x` whose validity range
ends at the unique positive root of `exp(x) = 1 + 2x`, which is
`x ≈ 1.256`). Setting `x = 2 β N_c` and requiring `2 β N_c < 1` (i.e.
`β < 1/(2 N_c)`) gives:

```
‖w̃‖∞ ≤ exp(2 β N_c) − 1 ≤ 2 · 2 β N_c = 4 β N_c
```

QED. □

The whole proof is **3 inequalities**:
1. `|Re tr U| ≤ N_c` for `U ∈ SU(N_c)` — from unitarity (Mathlib has this; see (c))
2. Two-sided exp-bound on `w̃` from the bound on `plaquetteWeight` and `Z_p`
3. `exp(x) − 1 ≤ 2x` for `x ∈ [0, 1]` — convexity / Taylor remainder

---

## (c) Connection to `dashboard/mayer_mathlib_precheck.md` has-vs-lacks table

The mayer Mathlib precheck (filed 20:20Z, audited at
`COWORK-MAYER-MATHLIB-PRECHECK-001`) classified Mathlib's BK / Möbius /
Haar factorisation readiness into 13 rows. Subsection (c) (lines 108-138)
specifically covered `essSup` and the L∞-norm-on-compact-continuous-function
machinery. The relevant rows for **B.4** are:

| Mathlib facility | Status | Relevance to B.4 |
|---|:---:|---|
| `MeasureTheory.essSup` + `essSup_le_iff` (`Mathlib.MeasureTheory.Function.EssSup`) | **HAS** | Direct primitive needed. The L∞ bound translates to `essSup ‖w̃‖ ≤ 4 N_c β` via this API. |
| `IsCompact.exists_isMaxOn` (continuous on compact attains sup) | **HAS** | Gives `‖w̃‖∞ = sup |w̃|` for continuous on compact. |
| `Continuous.essSup_le` | **HAS** (chained via `essSup_le_iff` + `Continuous.aestronglyMeasurable`) | Reduces essSup bound to AE pointwise bound. |
| `Real.exp_le_one_add_iff` / `Real.exp_le_one_add_of_nonneg` | **PARTIAL** | Mathlib has `Real.add_one_le_exp` (`1 + x ≤ exp x`); the reverse `exp x − 1 ≤ 2x` for `x ∈ [0, 1]` is **not a direct named lemma** but follows from `Real.exp_one_lt_three` + monotonicity, or via Taylor remainder. ~10 LOC ad-hoc. |
| `Real.exp_le_exp` (monotonicity of exp) | **HAS** | Used in step 2 (bounding plaquetteWeight by exp(±βN_c)). |
| Project's `wilsonPlaquetteEnergy_continuous` (`WilsonPlaquetteEnergy.lean:41`) | **HAS** | Continuity prerequisite for the essSup bound. |
| Project's `plaquetteFluctuationNorm` (`ZeroMeanCancellation.lean:126`) | **HAS** | The variable `w̃`. |
| Project's `singlePlaquetteZ_pos` (`ZeroMeanCancellation.lean:82`) | **HAS** | Strict positivity of `Z_p` needed for division. |
| **Trace bound** `|Re tr U| ≤ N_c` for `U ∈ SU(N_c)` | **MAYBE-LACKS** | Mathlib has `Complex.abs_re_le_abs` and `Matrix.trace` for matrices; the specific bound `|Re tr U| ≤ N_c` for `U ∈ specialUnitaryGroup (Fin N_c) ℂ` is not a standard named lemma. Needs ~15 LOC project-side combining `Matrix.unitaryGroup`'s `unitary_norm_eq_one` (each diagonal entry has |·| ≤ 1) + `|Re z| ≤ |z|` + `|tr U| ≤ Σ |U_ii| ≤ N_c`. |

### What Mathlib LACKS (critical for B.4)

- **`Real.exp_sub_one_le_two_mul_self` (or similar) for `x ∈ [0, 1]`**: not a
  named lemma. Cowork searched Mathlib for `exp_sub_one`, `exp_le_one_add_two_mul`,
  `Real.exp_lt_one_add` — all return inappropriate or partial results. The
  bound `exp(x) − 1 ≤ 2x` for `x ∈ [0, 1]` is folklore but unformalized.
  **~10 LOC** to prove via `Real.exp_one_lt_d9` + interval arithmetic, or
  via `Real.exp_le_iff_le_log` chain. Mathlib does have the **reverse**
  `Real.add_one_le_exp` (`1 + x ≤ exp x`) which is the easier direction.
- **Trace bound for `SU(N_c)`**: project-side as above; ~15 LOC.

### Conclusion

B.4 has **two small Mathlib gaps**, both project-side ~25 LOC total:
- ad-hoc `exp(x) − 1 ≤ 2x` for `x ∈ [0, 1]` (~10 LOC)
- ad-hoc `|Re tr U| ≤ N_c` for `U ∈ SU(N_c)` (~15 LOC)

The harder Mathlib gaps (BK forest formula, Mayer/Ursell identity) do not
appear in B.4. B.4 is purely single-plaquette algebra; no polymer or
combinatorics machinery enters.

### ⚠ HYPOTHESIS-STRENGTH FINDING (the flagged inconsistency)

**The proposed `hβ_small : β < Real.log 2 / N_c` is insufficient for the
proof body's `exp(2 β N_c) − 1 ≤ 4 β N_c` step.**

Setting `y = 2 β N_c`, we need `exp(y) − 1 ≤ 2y`, equivalently
`exp(y) ≤ 1 + 2y`. The function `g(y) = 1 + 2y − exp(y)` satisfies `g(0) = 0`,
`g'(0) = 1 > 0`, `g(log 2) = 1 + 2 log 2 − 2 ≈ 0.386 > 0`. The unique
positive root of `g(y) = 0` is `y ≈ 1.256`.

- Under proposed `β < log(2)/N_c`: `y < 2 log 2 ≈ 1.386 > 1.256`. **The bound
  fails** for `β ∈ (0.628 / N_c, log(2) / N_c)`. Concretely at `β = log 2 / N_c`:
  `y = 2 log 2`, `exp(y) − 1 = 4 − 1 = 3`, `4 β N_c = 4 log 2 ≈ 2.77`. So
  `3 > 2.77`, the bound fails by ~8%.
- Under the **corrected** `β < 1/(2 N_c)`: `y < 1 < 1.256`. **The bound holds**
  comfortably. At `y = 1`: `exp(1) − 1 ≈ 1.718`, `2y = 2`, ratio ~0.86.

**Recommendation**: tighten the hypothesis to `β < 1/(2 * N_c)` for B.4.
The project's actual small-β regime is `β < 1/(28 N_c)` per the F3-COMBINED
LEDGER row, which is much smaller than `1/(2 N_c)` and well within the
bound's validity range. Either form is sufficient for downstream B.5/B.6
consumption.

Tracked at `REC-CODEX-MAYER-B4-HYPOTHESIS-TIGHTEN-001` and cross-reference
repair `REC-COWORK-B4-SCOPE-REC-BACKREF-001`; both are resolved by the
2026-04-27 Codex documentation pass that corrected `F3_MAYER_DEPENDENCY_MAP.md`
and added this back-reference.

This finding does not affect the broader B.1-B.6 plan; it just means Codex
should use the corrected hypothesis when implementing B.4. The scope's
recommended form (in section (a)) uses `β < 1 / (2 * N_c)`.

---

## (d) Decomposition into project-side ~80 LOC + Mathlib-side gaps

**Project-side LOC budget for B.4**: **~80 LOC** (per `F3_MAYER_DEPENDENCY_MAP.md:219`):

| Sub-step | LOC | Content |
|---|---:|---|
| Trace bound: `|Re tr U| ≤ N_c` for `U ∈ specialUnitaryGroup (Fin N_c) ℂ` | ~15 | Use `unitary_norm_eq_one` per coordinate + `|Re z| ≤ ‖z‖` + `|Σ a_i| ≤ Σ |a_i| ≤ N_c · 1`. Alternatively use `Matrix.UnitaryGroup` machinery if available. |
| Two-sided `plaquetteWeight` bound: `exp(-β N_c) ≤ plaquetteWeight U ≤ exp(β N_c)` | ~15 | From `wilsonPlaquetteEnergy = Re tr U`, `|Re tr U| ≤ N_c`, `Real.exp_le_exp`. |
| Two-sided `Z_p` bound: `exp(-β N_c) ≤ Z_p ≤ exp(β N_c)` | ~10 | Integrate the plaquetteWeight bound against the probability measure `sunHaarProb N_c`. |
| Two-sided `w̃` bound: `exp(-2 β N_c) − 1 ≤ w̃ ≤ exp(2 β N_c) − 1` | ~10 | Divide the plaquetteWeight bound by the `Z_p` bound; subtract 1. |
| Absolute-value bound: `|w̃| ≤ exp(2 β N_c) − 1` | ~10 | Take max of two sides; for `β > 0`, the upper side dominates (since `exp` is convex). |
| Mathlib-or-ad-hoc lemma: `exp(x) − 1 ≤ 2x` for `x ∈ [0, 1]` | ~10 | `Real.exp_le_iff_le_log` chain or Taylor remainder. |
| Final substitution: `x = 2 β N_c`, conclude `‖w̃‖∞ ≤ 4 β N_c` | ~5 | Compose with the lemma above. |
| `essSup` translation: lift pointwise bound to `essSup` via `Continuous.aestronglyMeasurable` + `essSup_le_iff` | ~10 | Use `IsCompact.essSup_eq_iSup` for continuous functions on compact. |
| Hypothesis-mismatch handling (recommend Codex tighten hypothesis to `β < 1/(2 N_c)`) | docs | Section (c) flag |
| `#print axioms` directive | ~1 | Pin oracle trace to `[propext, Classical.choice, Quot.sound]` |
| Doc comments + cross-references | ~5 | Mandatory disclaimer + cross-reference to `wilsonPlaquetteEnergy`, B.1, B.2 scopes |

**Risk profile**: LOW. Pure algebra of exponentials; no measure-theoretic
subtleties beyond `essSup`/`iSup` translation; no combinatorics; no
project-internal scaffolding that doesn't already exist. The only mild
pitfall is the hypothesis-strength mismatch flagged in section (c).

**Where B.4 is harder than B.1**: B.4 needs (a) the SU(N_c) trace bound
(15 LOC project-side), (b) the elementary `exp(x) − 1 ≤ 2x` bound (10 LOC
ad-hoc since Mathlib doesn't expose it directly), (c) the L∞ → essSup
translation (10 LOC). B.1 needs only the keystone applied directly. This is
why B.4 is "EASY-MEDIUM" rather than EASY.

**Where B.4 is easier than B.2**: no Wilson-Haar factorisation, no polymer
decomposition, no Fubini wrapper. Single-plaquette only.

---

## (e) Klarner-Ursell pairing role — B.4 supplies `r`

After B.1 + B.2 + B.3 + B.4 (and the rest of B.5-B.6) lands, the F3-MAYER
side produces an inhabitant of `ConnectedCardDecayMayerData N_c (4 N_c β) 1
hr_nonneg hA_nonneg` (`ClusterRpowBridge.lean:2229`). The F3-COUNT side
(post the residual-extension-compatibility chain) produces a
`ShiftedConnectingClusterCountBoundExp` (`LatticeAnimalCount.lean:1096`
consumer chain).

The **Klarner-Ursell pairing** at `ShiftedF3MayerCountPackageExp.ofSubpackages`
(`ClusterRpowBridge.lean:4371`):

```
∑_{Y polymer connecting p,q} |K_β(Y)|
  ≤ ∑_{Y connected} A₀ · r^|Y|                      (B.3 bound; r is the new constant)
  ≤ A₀ · ∑_n count(n; p, q) · r^n
  ≤ A₀ · ∑_n K^n · r^n                              (Klarner: count ≤ K^n)
  = A₀ · 1/(1 − K · r)                              (geometric series; converges for K · r < 1)
```

**B.4's specific role**: the constant `r` in the geometric series is **exactly
the `‖w̃‖∞` bound** that B.4 supplies. Per the BLUEPRINT, `r = 4 N_c · β`,
which is what B.4 proves. The geometric-series convergence at `K · r < 1`
becomes:

```
K · r < 1
⟺ 7 · 4 N_c · β < 1                          (K = 7 for d = 4 lattice animals)
⟺ β < 1 / (28 N_c)
```

This is the **exact small-β regime** `β < 1/(28 N_c)` that the project's
`F3-COMBINED` LEDGER row records. So B.4's role is to:

1. Supply the explicit `r = 4 N_c · β` formula
2. Justify the inequality `r > 0` (used for geometric-series convergence)
3. Connect the `essSup` of `w̃` to the explicit constant `4 N_c · β`

Without B.4, the assembly at `ClusterRpowBridge.lean:4371` cannot instantiate
`r` to a numeric expression in `β` and `N_c`, so the small-β threshold
`β < 1/(28 N_c)` would not be derivable.

**B.4 is the single quantitative bridge** between the lattice-side bound
`r` (analytic; from gauge-coupling smallness) and the combinatorial-side
constant `K = 7` (from Klarner d=4 lattice-animal count). Without B.4 the
threshold is non-computable; with B.4 it is the explicit `1/(28 N_c)`
appearing in the F3-COMBINED row.

---

## Summary table — pre-supplied API surface for §(b)/B.4

| Section | Identifier | File:line | Role in §(b)/B.4 |
|---|---|---|---|
| (a) signature | `plaquetteFluctuationNorm_sup_le` (or `_essSup_le`) | (proposed) `ZeroMeanCancellation.lean:200` | The B.4 target |
| (a) variable | `plaquetteFluctuationNorm` | `ZeroMeanCancellation.lean:126` | The `w̃` |
| (b) energy | `wilsonPlaquetteEnergy` | `WilsonPlaquetteEnergy.lean:36` | `Re tr U` |
| (b) energy continuity | `wilsonPlaquetteEnergy_continuous` | `WilsonPlaquetteEnergy.lean:41` | Continuity prerequisite |
| (b) weight | `plaquetteWeight` | (project-internal `WilsonPlaquetteEnergy.lean` or adjacent) | `exp(-β · Re tr U)` |
| (b) partition function | `singlePlaquetteZ` | `ZeroMeanCancellation.lean:69` | `Z_p(β)` |
| (b) `Z_p > 0` | `singlePlaquetteZ_pos` | `ZeroMeanCancellation.lean:82` | Positivity prerequisite |
| (c) trace bound (NEW sublemma) | `wilsonPlaquetteEnergy_abs_le_dim` | (proposed) `WilsonPlaquetteEnergy.lean` | `|Re tr U| ≤ N_c` for `U ∈ SU(N_c)` |
| (c) exp inequality (NEW sublemma) | `Real.exp_sub_one_le_two_mul_self_of_le_one` | (proposed) project-internal helper | `exp(x) − 1 ≤ 2x` for `x ∈ [0, 1]` |
| (e) pairing target | `ConnectedCardDecayMayerData` | `ClusterRpowBridge.lean:2229` | F3-MAYER ultimate target |
| (e) pairing constant `r` | (numeric `4 * N_c * β`) | (consumed at) `ClusterRpowBridge.lean:4371` | Geometric series base |
| (e) Clay-facing assembly | `ShiftedF3MayerCountPackageExp` | `ClusterRpowBridge.lean:4355` | Pairs Mayer + Count |
| (e) terminal | `clayMassGap_of_shiftedF3MayerCountPackageExp` | `ClusterRpowBridge.lean:4855` | Produces `ClayYangMillsMassGap N_c` |

---

## What this scope does NOT do

- **Does not prove** `plaquetteFluctuationNorm_sup_le` / `_essSup_le`.
- **Does not prove** the trace bound or the exp inequality sublemmas.
- **Does not move** F3-MAYER from `BLOCKED`.
- **Does not move** F3-COUNT (still `CONDITIONAL_BRIDGE` until the residual-
  extension compatibility theorem proves; v2.71/v2.72 narrowed but did not
  close).
- **Does not move** any percentage (5% / 28% / 23-25% / 50% all preserved).
- **Does not assume** F3-COUNT or B.1 + B.2 has closed; this scope is
  conditional on all three.
- **Does not prove** the hypothesis-strength correction; it records the
  corrected B.4 statement and preserves the section (c) audit trail for the
  earlier dependency-map mismatch.

The scope is purely a **forward-looking implementation blueprint** for Codex
to pick up **after** F3-COUNT moves to FORMAL_KERNEL and B.1 + B.2 land.

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

- `F3_MAYER_DEPENDENCY_MAP.md` §(b) lines 204-219 — B.4 official entry (with
  the hypothesis-strength mismatch flagged in section (c))
- `F3_MAYER_DEPENDENCY_MAP.md` §(a) lines 51-140 — already-proved A.0-A.7
  scaffolding; B.4 reuses A.2 line 142 keystone for the `Z_p` positivity
  step
- `dashboard/f3_mayer_b1_scope.md` — sibling B.1 scope (single-vertex)
- `dashboard/f3_mayer_b2_scope.md` — sibling B.2 scope (disconnected polymer)
- `dashboard/mayer_mathlib_precheck.md` — Mathlib has-vs-lacks 13-row
  table; B.4 has 2 small project-side gaps (trace bound + exp inequality)
- `YangMills/ClayCore/ZeroMeanCancellation.lean:126` — `plaquetteFluctuationNorm`
  definition
- `YangMills/ClayCore/ZeroMeanCancellation.lean:69` — `singlePlaquetteZ`
- `YangMills/ClayCore/ZeroMeanCancellation.lean:82` — `singlePlaquetteZ_pos`
- `YangMills/ClayCore/ZeroMeanCancellation.lean:142` — `plaquetteFluctuationNorm_mean_zero`
  (the keystone for B.1; not directly used in B.4 but consumed downstream
  in B.5)
- `YangMills/ClayCore/WilsonPlaquetteEnergy.lean:36` — `wilsonPlaquetteEnergy`
  definition
- `YangMills/ClayCore/WilsonPlaquetteEnergy.lean:41` — continuity proof
- `YangMills/ClayCore/ClusterRpowBridge.lean:2229` — `ConnectedCardDecayMayerData`
  ultimate target structure
- `YangMills/ClayCore/ClusterRpowBridge.lean:4371` — `ShiftedF3MayerCountPackageExp.ofSubpackages`
  consumer (where B.4's `r = 4 N_c · β` constant is consumed)
- `BLUEPRINT_F3Mayer.md` §3.3 — algebra-of-exponentials derivation Cowork
  drew from for the proof skeleton
- `UNCONDITIONALITY_LEDGER.md:88` — F3-COUNT row (`CONDITIONAL_BRIDGE`,
  v2.71 evidence)
- `UNCONDITIONALITY_LEDGER.md:89` — F3-MAYER row (`BLOCKED on F3-COUNT
  closure first`)
- `UNCONDITIONALITY_LEDGER.md:90` — F3-COMBINED row (`BLOCKED`; the small-β
  regime `β < 1/(28 N_c)` recorded here is exactly the threshold B.4
  contributes to)

---

## Recommended next-session order for F3-MAYER scoping

After B.4 is scoped, the natural next moves are:

1. **B.6 scope** (already queued at `COWORK-F3-MAYER-B6-SCOPE-001`
   priority 7) — bundled witness, ~50 LOC pure glue. Closes the easy
   half of B.* (B.1 + B.2 + B.4 + B.6 = ~310 LOC across 4 theorems).
2. **B.5 scope** — Mayer/Ursell identity, ~200 LOC MEDIUM-HIGH. Use
   Möbius inversion on the partition lattice; partial Mathlib support
   per `mayer_mathlib_precheck.md` row "Möbius inversion on partition
   lattice".
3. **B.3 scope** — BK polymer bound, ~250 LOC HIGH. The hardest of the
   six theorems; `mayer_mathlib_precheck.md` already maps the Mathlib
   gap landscape (zero matches for Brydges-Kennedy / forest-formula).

This ordering matches the recommended `B.1 → B.2 → B.4 → B.6 → B.5 → B.3`
closure order in `f3_mayer_b1_scope.md` (scopes filed in the order the
proofs will be needed).
