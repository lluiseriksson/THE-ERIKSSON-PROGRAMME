# AXIOM_FRONTIER.md v0.14.0 (census corrected: 2026-03-29)

## Source Census

Census date: 2026-03-29.
All files in `YangMills/P8_PhysicalGap/` (20 files),
`YangMills/Experimental/LieSUN/` (8 files), and
`YangMills/Experimental/Semigroup/` inspected individually using:

```bash
# Authoritative census — catches indented AND attributed axioms (e.g. @[instance] axiom):
grep -rn "\baxiom\b" YangMills/ --include="*.lean" | grep -v "^\s*--"
# Word-boundary regex avoids false matches on identifiers containing "axiom" as substring.
```

**Scope**: P8_PhysicalGap + Experimental/LieSUN + Experimental/Semigroup.
`YangMills/L0`–`L8` open_hypotheses are tracked via `open_hypotheses` field in
`registry/nodes.yaml` (not as named `axiom` declarations in those files).

---

## Summary

| Category                              | Count |
|---------------------------------------|-------|
| Clay-core axioms                      | 3     |
| Clay-core (proof exists, unconnected) | 1     |
| Mathlib-gap axioms                    | 16    |
| **Total unique mathematical gaps**    | **20** |

> **Lean declaration count vs. mathematical gap count (C3 effect)**
>
> After closure C3 (2026-03-29), `DirichletConcrete.lean` had three axiom names
> renamed with a prime suffix (`generatorMatrix'`, `gen_skewHerm'`, `gen_trace_zero'`)
> to eliminate Lean redeclaration errors with `LieDerivativeRegularity.lean`.
> Both files now contain axiom declarations for the same three mathematical objects,
> under distinct Lean names (primed vs. unprimed).
>
> **Total unique Lean axiom declaration names: 23** (20 mathematical gaps + 3 additional
> Lean identifiers that duplicate the content of `generatorMatrix`, `gen_skewHerm`,
> `gen_trace_zero` under primed names in `DirichletConcrete.lean`).
>
> This document counts by **distinct mathematical gaps** (20), not Lean names (23).

### Changelog vs. v0.13.0

| v0.13.0 Claim                          | Correction in v0.14.0                                                    |
|----------------------------------------|--------------------------------------------------------------------------|
| Total unique axiom names: **18**       | **20** — C1 closure added 2 named axioms omitted from the v0.13.0 count  |
| C1 axioms only in RESOLVED section     | Now listed in Mathlib-gap table under Experimental/Semigroup             |
| DirichletConcrete "duplicate" warning  | Updated: after C3, they are distinct primed names, not Lean duplicates   |

### Changelog vs. v0.9 (for reference)

| v0.9 Claim                    | Correction                                              |
|-------------------------------|---------------------------------------------------------|
| `sun_gibbs_dlr_lsi` is axiom  | **Proved theorem** in `BalabanToLSI.lean` (see file)   |
| `clustering_to_spectralGap` is axiom | **Proved theorem** in `StroockZegarlinski.lean`  |
| Axiom count: 10               | True count: **20 unique mathematical gaps**             |
| `hille_yosida` in "(P8 gap)"  | Actual: `hille_yosida_semigroup` in `MarkovSemigroupDef.lean` |

---

## Clay-Core Axioms (Genuine Mathematical Gaps)

Proofs require original mathematics beyond Mathlib or known results not yet in the library.

| Axiom | File | Content | Status |
|---|---|---|---|
| `sun_bakry_emery_cd` | `P8_PhysicalGap/BalabanToLSI.lean` | SU(N) satisfies Bakry-Émery CD(N/4, ∞) — Ricci curvature computation | ⚠ open |
| `balaban_rg_uniform_lsi` | `P8_PhysicalGap/BalabanToLSI.lean` | Balaban RG promotes per-site Haar-LSI to uniform finite-volume DLR-LSI | ⚠ open |
| `sun_lieb_robinson_bound` | `P8_PhysicalGap/SUN_LiebRobin.lean` | Lieb-Robinson bound for SU(N) lattice observables | ⚠ open |

### Clay-Core Axiom with Existing Proof (Not Yet Connected)

| Axiom | Axiom File | Proof File | Status |
|---|---|---|---|
| `sz_lsi_to_clustering` | `P8_PhysicalGap/BalabanToLSI.lean` | `P8_PhysicalGap/StroockZegarlinski.lean` | ⚠ unconnected |

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
> **To connect**: (1) import `StroockZegarlinski` in `BalabanToLSI`, (2) remove axiom,
> (3) verify that `sunGibbsFamily`/`sunDirichletForm` satisfy the missing hypotheses
> via the abstract interface, (4) update call site.
> This reduces `sz_lsi_to_clustering` to a dependency on `hille_yosida_semigroup`
> but does NOT achieve unconditional closure.
> **Status: ABSTRACT_INTERFACE_GAP — connection requires non-trivial Lean engineering.**

---

## Mathlib-Gap Axioms (Infrastructure Gaps)

Standard mathematics blocked by missing Lean 4 / Mathlib 4 infrastructure.

### P8_PhysicalGap

| Axiom | File | Content | Mathlib Blocker |
|---|---|---|---|
| `bakry_emery_lsi` | `BalabanToLSI.lean` | Bakry-Émery curvature criterion implies LSI | BE theory not in Mathlib |
| `instIsProbabilityMeasure_sunHaarProb` | `BalabanToLSI.lean` | Abstract Haar measure is a probability measure (instance via `attribute [instance]`) | Opaque interface gap |
| `instIsTopologicalGroupSUN` | `SUN_StateConstruction.lean` | `IsTopologicalGroup ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)` — `@[instance] axiom` | Mathlib: `Subgroup.toTopologicalGroup` not yet threaded to `specialUnitaryGroup` |
| `sunDirichletForm_contraction` | `SUN_DirichletCore.lean` | Beurling-Deny normal contraction (truncation reduces Dirichlet form) | Needs `lieD'_chain` rule |
| `hille_yosida_semigroup` | `MarkovSemigroupDef.lean` | Beurling-Deny/Hille-Yosida: symmetric closed Dirichlet form → Markov semigroup | C₀-semigroup theory absent from Mathlib 4 |
| `poincare_to_covariance_decay` | `StroockZegarlinski.lean` | Poincaré inequality → covariance decay via Markov semigroup | Requires operator semigroup + decay estimates |
| `sun_variance_decay` | `SUN_LiebRobin.lean` | Variance decay for SU(N) Markov semigroup | Depends on `hille_yosida_semigroup` |

### Experimental/LieSUN

| Axiom | File | Content | Mathlib Blocker |
|---|---|---|---|
| `sunGeneratorData` | `LieDerivReg_v4.lean` | SU(N) generator matrix construction + properties bundle | SU(N) as LieGroup not in Mathlib |
| `lieDerivReg_all` | `LieDerivReg_v4.lean` | Lie derivative integrability for all generators and L² functions | Requires smooth manifold instance |
| `generatorMatrix` | `LieDerivativeRegularity.lean` | SU(N) generator matrix function | SU(N) LieGroup instance |
| `gen_skewHerm` | `LieDerivativeRegularity.lean` | Generator matrices are skew-Hermitian | SU(N) LieGroup instance |
| `gen_trace_zero` | `LieDerivativeRegularity.lean` | Generator matrices are traceless | SU(N) LieGroup instance |
| `matExp_traceless_det_one` | `LieExpCurve.lean` | `det(matExp((t:ℂ)•X)) = 1` when `X.trace=0` — via Liouville/Jacobi formula | Mathlib4 may have `Matrix.det_exp`; connection not yet verified |
| `dirichlet_lipschitz_contraction` | `DirichletContraction.lean` | Lipschitz contraction of Dirichlet form under truncation | Needs chain rule for `lieD'` |

> **C3 rename — `DirichletConcrete.lean` primed axioms (2026-03-29)**:
> After closure C3, `DirichletConcrete.lean` declares `generatorMatrix'`, `gen_skewHerm'`,
> `gen_trace_zero'` (primed) — same mathematical content as the three rows above.
> These are separate Lean declaration names and appear in `grep` output.
> They are not listed as separate rows in this table because they represent no new
> mathematical gap; each is a Lean identifier alias for the corresponding unprimed axiom.
> See the Summary note on Lean declaration count (23) vs. mathematical gap count (20).

### Experimental/Semigroup  ← NEW in v0.14.0 (C1 closure, 2026-03-29)

These two axioms replaced `sorry` placeholders removed by closure C1.
They are tracked here because they represent genuine mathematical gaps
(C₀-semigroup theory for Markov processes), even though the files are in
`Experimental/`. `scripts/check_consistency.py` reports them as warnings (non-blocking)
because they carry the required `--` comment explaining the blocker.

| Axiom | File | Content | Mathlib Blocker |
|---|---|---|---|
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | `Experimental/Semigroup/VarianceDecayFromPoincare.lean` | `HasVarianceDecay sg` — bridge for all t, not just t=0; same root as `hille_yosida_semigroup` | C₀-semigroup theory absent from Mathlib 4 |
| `gronwall_variance_decay` | `Experimental/Semigroup/VarianceDecayFromPoincare.lean` | `HasVarianceDecay sg` from Gronwall: V′(t) ≤ −λ·V(t) ⟹ V(t) ≤ V(0)·e^{−λt} for Markov semigroup | C₀-semigroup theory absent from Mathlib 4 |

---

## Experimental/ Sorry Declarations — RESOLVED (2026-03-29)

**Status: CLOSED** — both sorry converted to named `axiom` declarations by `apply_closures.py`.
`scripts/check_consistency.py` now exits 0 with **zero sorry total** across all Lean source.
The 2 named axioms are now tracked in the Mathlib-gap table above under **Experimental/Semigroup**.

| File | Line | Former sorry comment | Resolution |
|---|---|---|---|
| `Experimental/Semigroup/VarianceDecayFromPoincare.lean` | 92 | `-- Documented blocker: need bridge for all t, not just t=0` | → `axiom variance_decay_from_bridge_and_poincare_semigroup_gap` |
| `Experimental/Semigroup/VarianceDecayFromPoincare.lean` | 117 | `-- Documented: needs Gronwall for V(t) ≤ C·exp(−kt) from V'(t) ≤ −k·V(t)` | → `axiom gronwall_variance_decay` (full signature) |

**Closure patch** (`apply_closures.py`, commit `0f0b604`):
- Line 92 sorry → `axiom variance_decay_from_bridge_and_poincare_semigroup_gap : HasVarianceDecay sg`
- Line 117 sorry → `axiom gronwall_variance_decay` with full type:
  `{μ} [IsProbabilityMeasure μ] (E) (sg : SymmetricMarkovTransport μ) (lam) (hlam) (hP : PoincareInequality μ E lam) (hBridge : SemigroupDirichletBridgeGlobal E sg) : HasVarianceDecay sg`

---

## Structural Issues to Resolve

1. **`sz_lsi_to_clustering` name clash** (`BalabanToLSI.lean` axiom vs
   `StroockZegarlinski.lean` theorem — same `YangMills` namespace, separate import graphs).
   These modules must be connected before the axiom can be discharged.

2. **Primed axiom aliases** in `DirichletConcrete.lean` (`generatorMatrix'`, `gen_skewHerm'`,
   `gen_trace_zero'` after C3 rename). These prevent the Lean redeclaration error but
   create a second copy of the same mathematical content. Long-term fix: have
   `DirichletConcrete.lean` import `LieDerivativeRegularity.lean` and use the
   unprimed names directly instead of re-declaring with prime.

3. **Abstract `opaque` layer in `BalabanToLSI.lean`**: `SUN_State`, `sunHaarProb`,
   `sunDirichletForm`, `sunGibbsFamily` are `opaque` (not `axiom`), creating a parallel
   abstract interface disconnected from the concrete `SUN_StateConstruction` /
   `SUN_DirichletCore` stack. The P8 consumer layer (`PhysicalMassGap.lean`) uses
   the abstract objects and cannot directly use the concrete SU(N) formalization.

4. **`matExp_traceless_det_one` — potential C4 closure**: if `Matrix.det_exp` exists
   in Mathlib4, `det(exp(t·X)) = exp(tr(t·X)) = exp(t·0) = 1` closes this directly.
   **Action**: search Mathlib4 for `Matrix.det_exp` or `det_exp`.

---

## Next Minimal Action

Prove `sun_bakry_emery_cd` (`BalabanToLSI.lean`) — first Clay-core axiom in Phase 2.

Requires:
- Ricci curvature computation on SU(N) as a Riemannian manifold (≥ K = N/4 > 0)
- Connection to the abstract Dirichlet form via Bakry-Émery criterion

---

## Previous Milestones

- **v0.13.0** (2026-03-29): Closures C1 (2 sorry→axiom) and C3 (redeclaration fix) applied
- **v0.9** (2026-03-28): AXIOM 6 — Haar-LSI Package Frontier (packaging layer) closed
- **v0.9** (2026-03-28): 4 BalabanRG files verified (0 errors, 0 sorry)

---

*Last updated: 2026-03-29*
*Version: v0.14.0 — corrects v0.13.0 undercount (18 → 20 mathematical gaps; 23 Lean declarations)*
*Census method: individual file inspection with `\baxiom\b` regex in non-comment lines*
*Files checked: 20 × P8_PhysicalGap + 8 × Experimental/LieSUN + Experimental/Semigroup*
*L0–L8 open_hypotheses: see `registry/nodes.yaml` `open_hypotheses` fields*
