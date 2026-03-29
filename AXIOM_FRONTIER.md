# AXIOM_FRONTIER.md v0.15.0 (live-census corrected: 2026-03-29)

## Source Census

Census date: 2026-03-29.
**Authoritative grep — full YangMills/ tree** (run by `census_verify.py`):

```bash
grep -rn "\baxiom\b" YangMills/ --include="*.lean" | grep -v "^\s*--"
```

Previous censuses covered only `P8_PhysicalGap/` + `Experimental/LieSUN/` and missed
`YangMills/ClayCore/` entirely. The corrected scope is **all of `YangMills/`**.

---

## Summary

| Category                                        | Count |
|-------------------------------------------------|-------|
| Clay-core (genuine mathematical gaps)           | 3     |
| Clay-core (proof exists, unconnected)           | 1     |
| ClayCore/BalabanRG infrastructure               | 4     |
| Mathlib-gap — P8_PhysicalGap                    | 7     |
| Mathlib-gap — Experimental/LieSUN               | 7     |
| Mathlib-gap — Experimental/Semigroup            | 4     |
| **Total unique axiom declaration names**        | **26** |

> **Duplicate pairs (C3 not committed — 2026-03-29)**:
> Three axiom names appear in **two files each** and will cause Lean redeclaration errors
> if both files are imported in the same module graph:
> - `generatorMatrix` — `DirichletConcrete.lean:23` and `LieDerivativeRegularity.lean:18`
> - `gen_skewHerm` — `DirichletConcrete.lean:26` and `LieDerivativeRegularity.lean:20`
> - `gen_trace_zero` — `DirichletConcrete.lean:29` and `LieDerivativeRegularity.lean:22`
>
> **Closure C3 was described in earlier changelog entries as committed (commit `0f0b604`),
> but live grep confirms the rename did NOT reach the public repo.**
> The 26 unique-name count treats these 3 pairs as 3 distinct names (the same name
> appearing in two files). Unique mathematical content: still 26 gaps.

### Changelog vs. v0.14.0

| v0.14.0 Claim | Correction in v0.15.0 |
|---|---|
| Total: **20** mathematical gaps | **26** — census scope was wrong (missed ClayCore/) |
| 23 Lean declaration names | **26** — and C3 was not committed (no primed names) |
| C3 applied (primed names in DirichletConcrete) | **C3 NOT COMMITTED** — duplicates still exist |
| Scope: P8 + LieSUN + Semigroup | **Scope: all of YangMills/** |
| HilleYosidaDecomposition axioms not listed | **+2 new**: `hille_yosida_core`, `poincare_to_variance_decay` |
| ClayCore/BalabanRG not in scope | **+4 new**: `blockFinset`, `blockFinset_spec`, `p91_tight_weak_coupling_window`, `physical_rg_rates_from_E26` |

---

## Clay-Core Axioms (Genuine Mathematical Gaps)

Proofs require original mathematics beyond Mathlib or known results not yet in the library.

| Axiom | File | Content | Status |
|---|---|---|---|
| `sun_bakry_emery_cd` | `P8_PhysicalGap/BalabanToLSI.lean:73` | SU(N) satisfies Bakry-Émery CD(N/4, ∞) — Ricci curvature computation | ⚠ open |
| `balaban_rg_uniform_lsi` | `P8_PhysicalGap/BalabanToLSI.lean:102` | Balaban RG promotes per-site Haar-LSI to uniform finite-volume DLR-LSI | ⚠ open |
| `sun_lieb_robinson_bound` | `P8_PhysicalGap/SUN_LiebRobin.lean:47` | Lieb-Robinson bound for SU(N) lattice observables | ⚠ open |

### Clay-Core Axiom with Existing Proof (Not Yet Connected)

| Axiom | Axiom File | Proof File | Status |
|---|---|---|---|
| `sz_lsi_to_clustering` | `P8_PhysicalGap/BalabanToLSI.lean:126` | `P8_PhysicalGap/StroockZegarlinski.lean:156` | ⚠ unconnected |

> **`sz_lsi_to_clustering` — ABSTRACT_INTERFACE_GAP (source-verified 2026-03-29)**:
>
> **Axiom** (`BalabanToLSI.lean:126`): takes `(gibbsFamily) (E) (α_star) (hLSI)` — 4 args.
>
> **Theorem** (`StroockZegarlinski.lean:156`): additionally requires
> `[hP : ∀ L, IsProbabilityMeasure (gibbsFamily L)]` and
> `(hE_strong : ∀ L, IsDirichletFormStrong E (gibbsFamily L))`.
> The theorem also calls `hille_yosida_semigroup` internally, so the result
> would be conditional on that axiom.
>
> **Call site** (`BalabanToLSI.lean:171`): only provides the 4 axiom args —
> `hP` and `hE_strong` are NOT in scope there.
>
> **Status: ABSTRACT_INTERFACE_GAP — connection requires non-trivial Lean engineering.**

---

## ClayCore/BalabanRG Axioms

Quantitative bounds and infrastructure for the Balaban renormalization group programme.
These axioms were **absent from all previous versions** of this document because the census
scope incorrectly excluded `YangMills/ClayCore/`.

| Axiom | File | Content |
|---|---|---|
| `blockFinset` | `ClayCore/BalabanRG/FiniteBlocks.lean:17` | Finite block decomposition for Balaban RG |
| `blockFinset_spec` | `ClayCore/BalabanRG/FiniteBlocks.lean:20` | Specification properties of the block finite set |
| `p91_tight_weak_coupling_window` | `ClayCore/BalabanRG/P91WeakCouplingWindow.lean:51` | P.91 tight weak-coupling window estimate |
| `physical_rg_rates_from_E26` | `ClayCore/BalabanRG/PhysicalRGRates.lean:101` | Physical RG rate estimates from Equation 26 of the programme |

> These axioms support the Balaban RG quantitative bounds needed for `balaban_rg_uniform_lsi`.
> Their mathematical status (Clay-core gap vs. Mathlib infrastructure gap) requires
> individual file inspection to classify precisely.

---

## Mathlib-Gap Axioms (Infrastructure Gaps)

Standard mathematics blocked by missing Lean 4 / Mathlib 4 infrastructure.

### P8_PhysicalGap

| Axiom | File:Line | Content | Mathlib Blocker |
|---|---|---|---|
| `bakry_emery_lsi` | `BalabanToLSI.lean:63` | Bakry-Émery curvature criterion implies LSI | BE theory not in Mathlib |
| `instIsProbabilityMeasure_sunHaarProb` | `BalabanToLSI.lean:48` | Abstract Haar measure is a probability measure (`attribute [instance]`) | Opaque interface gap |
| `instIsTopologicalGroupSUN` | `SUN_StateConstruction.lean:78` | `IsTopologicalGroup ↥(specialUnitaryGroup (Fin n) ℂ)` — `@[instance] axiom` | `Subgroup.toTopologicalGroup` not threaded to `specialUnitaryGroup` |
| `sunDirichletForm_contraction` | `SUN_DirichletCore.lean:178` | Beurling-Deny normal contraction (truncation reduces Dirichlet form) | Needs `lieD'_chain` rule |
| `hille_yosida_semigroup` | `MarkovSemigroupDef.lean:126` | Beurling-Deny/Hille-Yosida: symmetric closed Dirichlet form → Markov semigroup | C₀-semigroup theory absent from Mathlib 4 |
| `poincare_to_covariance_decay` | `StroockZegarlinski.lean:21` | Poincaré inequality → covariance decay via Markov semigroup | Requires operator semigroup + decay estimates |
| `sun_variance_decay` | `SUN_LiebRobin.lean:41` | Variance decay for SU(N) Markov semigroup | Depends on `hille_yosida_semigroup` |

### Experimental/LieSUN

| Axiom | File:Line | Content | Mathlib Blocker | Dup? |
|---|---|---|---|---|
| `sunGeneratorData` | `LieDerivReg_v4.lean:26` | SU(N) generator matrix construction + properties bundle | SU(N) as LieGroup not in Mathlib | |
| `lieDerivReg_all` | `LieDerivReg_v4.lean:43` | Lie derivative integrability for all generators and L² functions | Requires smooth manifold instance | |
| `generatorMatrix` | `LieDerivativeRegularity.lean:18` | SU(N) generator matrix function | SU(N) LieGroup instance | ⚠ |
| `gen_skewHerm` | `LieDerivativeRegularity.lean:20` | Generator matrices are skew-Hermitian | SU(N) LieGroup instance | ⚠ |
| `gen_trace_zero` | `LieDerivativeRegularity.lean:22` | Generator matrices are traceless | SU(N) LieGroup instance | ⚠ |
| `matExp_traceless_det_one` | `LieExpCurve.lean:76` | `det(matExp((t:ℂ)•X)) = 1` when `X.trace=0` | Mathlib4 may have `Matrix.det_exp`; not yet verified | |
| `dirichlet_lipschitz_contraction` | `DirichletContraction.lean:55` | Lipschitz contraction of Dirichlet form under truncation | Needs chain rule for `lieD'` | |

> **⚠ Duplicate declarations (C3 NOT committed)**:
> `generatorMatrix`, `gen_skewHerm`, `gen_trace_zero` are declared in **both**
> `LieDerivativeRegularity.lean` **and** `DirichletConcrete.lean` under the **same names**
> (unprimed). Any module importing both will fail with a Lean redeclaration error.
>
> Previous versions of this document incorrectly stated that closure C3 had renamed
> these to primed versions in `DirichletConcrete.lean`. **Live grep confirms C3 was
> not committed.** The fix remains: remove from `DirichletConcrete.lean` and import
> `LieDerivativeRegularity.lean` instead, OR rename to primed and re-commit C3.

### Experimental/Semigroup

| Axiom | File:Line | Content | Mathlib Blocker |
|---|---|---|---|
| `hille_yosida_core` | `HilleYosidaDecomposition.lean:62` | Core Hille-Yosida theorem for the semigroup decomposition | C₀-semigroup theory absent from Mathlib 4 |
| `poincare_to_variance_decay` | `HilleYosidaDecomposition.lean:69` | Poincaré inequality → variance decay via semigroup | C₀-semigroup + Poincaré spectral gap |
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | `VarianceDecayFromPoincare.lean:79` | `HasVarianceDecay sg` — bridge for all t; same root as `hille_yosida_semigroup` | C₀-semigroup theory |
| `gronwall_variance_decay` | `VarianceDecayFromPoincare.lean:133` | `HasVarianceDecay sg` from Gronwall: V′(t) ≤ −λ·V(t) ⟹ V(t) ≤ V(0)·e^{−λt} | C₀-semigroup theory |

> `hille_yosida_core` and `poincare_to_variance_decay` are **newly catalogued in v0.15.0**;
> they were absent from all previous versions because `HilleYosidaDecomposition.lean`
> was not individually inspected during earlier manual censuses.

---

## Experimental/ Sorry Declarations — RESOLVED (2026-03-29)

**Status: CLOSED** — both sorry converted to named `axiom` declarations by `apply_closures.py`
(commit `0f0b604`). `scripts/check_consistency.py` exits 0 with **zero sorry total** across
all Lean source. Confirmed by live census (2026-03-29): 0 sorry detected.

| File | Former line | Former comment | Resolution |
|---|---|---|---|
| `Experimental/Semigroup/VarianceDecayFromPoincare.lean` | 92 (now 79) | `-- need bridge for all t` | → `axiom variance_decay_from_bridge_and_poincare_semigroup_gap` |
| `Experimental/Semigroup/VarianceDecayFromPoincare.lean` | 117 (now 133) | `-- needs Gronwall` | → `axiom gronwall_variance_decay` (full signature) |

---

## Structural Issues to Resolve

1. **`sz_lsi_to_clustering` ABSTRACT_INTERFACE_GAP** — connect `StroockZegarlinski.lean`
   theorem to `BalabanToLSI.lean` axiom (requires `hP` + `hE_strong` at call site).

2. **Duplicate axiom names (C3 open)** — `generatorMatrix`, `gen_skewHerm`, `gen_trace_zero`
   declared under the same name in both `LieDerivativeRegularity.lean` and
   `DirichletConcrete.lean`. Fix: remove from `DirichletConcrete.lean` and import
   `LieDerivativeRegularity.lean`, OR rename to primed and commit C3 properly.

3. **Abstract `opaque` layer in `BalabanToLSI.lean`** — `SUN_State`, `sunHaarProb`,
   `sunDirichletForm`, `sunGibbsFamily` are `opaque`, creating an abstract interface
   disconnected from the concrete `SUN_StateConstruction` / `SUN_DirichletCore` stack.

4. **`matExp_traceless_det_one` — potential closure**: search Mathlib4 for `Matrix.det_exp`.
   If present: `det(exp(t·X)) = exp(tr(t·X)) = exp(0) = 1` closes this directly.

5. **ClayCore/BalabanRG axiom classification**: `blockFinset`, `blockFinset_spec`,
   `p91_tight_weak_coupling_window`, `physical_rg_rates_from_E26` require individual
   file inspection to determine whether they are Clay-core gaps or Mathlib infrastructure gaps.

---

## Next Minimal Action

Prove `sun_bakry_emery_cd` (`BalabanToLSI.lean:73`) — first Clay-core axiom in Phase 2.

---

## Previous Milestones

- **v0.14.0** (2026-03-29): Census scope extended; count corrected 18→20 (partial)
- **v0.13.0** (2026-03-29): Closures C1 (2 sorry→axiom) and C3 (attempted rename) applied
- **v0.9** (2026-03-28): AXIOM 6 — Haar-LSI Package Frontier closed
- **v0.9** (2026-03-28): 4 BalabanRG files verified (0 errors, 0 sorry)

---

*Last updated: 2026-03-29*
*Version: v0.15.0 — live-census corrected; 26 unique names, full YangMills/ scope*
*Census tool: `census_verify.py` (word-boundary regex, block-comment stripping)*
*C3 status: NOT committed — duplicate names remain in DirichletConcrete.lean*
*0 sorry confirmed across all Lean source*
