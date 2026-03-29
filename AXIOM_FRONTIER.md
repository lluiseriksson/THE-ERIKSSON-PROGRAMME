# AXIOM_FRONTIER.md v0.12.0 (source-verified: 2026-03-29)

## Source Census

Census date: 2026-03-29.
All files in `YangMills/P8_PhysicalGap/` (20 files) and
`YangMills/Experimental/LieSUN/` (8 files) inspected individually using:

```bash
# Authoritative census — catches indented AND attributed axioms (e.g. @[instance] axiom):
grep -rn "^\s*axiom " YangMills/ --include="*.lean" | grep -v "^\s*--"
# Plus broad scan for attributed axioms:
# check each file for /\baxiom\b/ in non-comment code portions
```

**Scope**: P8_PhysicalGap + Experimental/LieSUN.
`YangMills/L0`–`L8` open_hypotheses are tracked via `open_hypotheses` field in
`registry/nodes.yaml` (not as named `axiom` declarations in those files).

---

## Summary

| Category                              | Count |
|---------------------------------------|-------|
| Clay-core axioms                      | 3     |
| Clay-core (proof exists, unconnected) | 1     |
| Mathlib-gap axioms                    | 14    |
| **Total unique axiom names**          | **18** |

### Two Errors Corrected vs. Previous Version (v0.9)

| v0.9 Claim                    | Correction                                              |
|-------------------------------|---------------------------------------------------------|
| `sun_gibbs_dlr_lsi` is axiom  | **Proved theorem** in `BalabanToLSI.lean` (see file)   |
| `clustering_to_spectralGap` is axiom | **Proved theorem** in `StroockZegarlinski.lean`  |
| Axiom count: 10               | True count: **18 unique axiom names**                   |
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

| Axiom | File | Content | Mathlib Blocker | Duplicate? |
|---|---|---|---|---|
| `sunGeneratorData` | `LieDerivReg_v4.lean` | SU(N) generator matrix construction + properties bundle | SU(N) as LieGroup not in Mathlib | |
| `lieDerivReg_all` | `LieDerivReg_v4.lean` | Lie derivative integrability for all generators and L² functions | Requires smooth manifold instance | |
| `generatorMatrix` | `LieDerivativeRegularity.lean` | SU(N) generator matrix function | SU(N) LieGroup instance | ⚠ |
| `gen_skewHerm` | `LieDerivativeRegularity.lean` | Generator matrices are skew-Hermitian | SU(N) LieGroup instance | ⚠ |
| `gen_trace_zero` | `LieDerivativeRegularity.lean` | Generator matrices are traceless | SU(N) LieGroup instance | ⚠ |
| `matExp_traceless_det_one` | `LieExpCurve.lean` | `det(matExp((t:ℂ)•X)) = 1` when `X.trace=0` — via Liouville/Jacobi formula | Mathlib4 may have `Matrix.det_exp`; connection not yet verified | |
| `dirichlet_lipschitz_contraction` | `DirichletContraction.lean` | Lipschitz contraction of Dirichlet form under truncation | Needs chain rule for `lieD'` | |

> **⚠ Duplicate declarations** (`generatorMatrix`, `gen_skewHerm`, `gen_trace_zero`):
> These three axioms are declared in **both** `LieDerivativeRegularity.lean` **and**
> `DirichletConcrete.lean`. Any module importing both will fail with a Lean redeclaration
> error. **Action required**: remove the declarations from `DirichletConcrete.lean`
> and import `LieDerivativeRegularity.lean` instead.

---

## Experimental/ Sorry Declarations (Non-Blocking)

These `sorry` occurrences are in `YangMills/Experimental/Semigroup/` scratch files.
They are reported as **warnings** by `scripts/check_consistency.py` but do NOT cause CI to fail.
Each carries an explicit `--` comment stating the blocker.
They must be converted to named `axiom` declarations before any promotion to the main pipeline.

| File | Line | Comment / Blocker |
|---|---|---|
| `Experimental/Semigroup/VarianceDecayFromPoincare.lean` | 92 | Need bridge for all t; same root as `hille_yosida_semigroup` |
| `Experimental/Semigroup/VarianceDecayFromPoincare.lean` | 117 | Gronwall for V(t) ≤ C·exp(−kt) from V′(t) ≤ −k·V(t) |

**Closure patch** (`apply_closures.py`):
- Line 92 sorry → `axiom <theorem_name>_semigroup_gap` (extracted dynamically from source)
- Line 117 sorry → `axiom gronwall_variance_decay` with full type:
  `{μ} [IsProbabilityMeasure μ] (E) (sg : SymmetricMarkovTransport μ) (lam) (hlam) (hP) (hBridge : SemigroupDirichletBridgeGlobal E sg) : HasVarianceDecay sg`

---

## Structural Issues to Resolve

1. **`sz_lsi_to_clustering` name clash** (`BalabanToLSI.lean` axiom vs
   `StroockZegarlinski.lean` theorem — same `YangMills` namespace, separate import graphs).
   These modules must be connected before the axiom can be discharged.

2. **Triple duplicate axioms** in `LieDerivativeRegularity.lean` / `DirichletConcrete.lean`:
   `generatorMatrix`, `gen_skewHerm`, `gen_trace_zero`. Remove duplicates from `DirichletConcrete.lean`.

3. **Abstract `opaque` layer in `BalabanToLSI.lean`**: `SUN_State`, `sunHaarProb`,
   `sunDirichletForm`, `sunGibbsFamily` are `opaque` (not `axiom`), creating a parallel
   abstract interface disconnected from the concrete `SUN_StateConstruction` /
   `SUN_DirichletCore` stack. The P8 consumer layer (`PhysicalMassGap.lean`) uses
   the abstract objects and cannot directly use the concrete SU(N) formalization.

---

## Next Minimal Action

Prove `sun_bakry_emery_cd` (`BalabanToLSI.lean`) — first Clay-core axiom in Phase 2.

Requires:
- Ricci curvature computation on SU(N) as a Riemannian manifold (≥ K = N/4 > 0)
- Connection to the abstract Dirichlet form via Bakry-Émery criterion

---

## Previous Milestones

- **v0.9** (2026-03-28): AXIOM 6 — Haar-LSI Package Frontier (packaging layer) closed
- **v0.9** (2026-03-28): 4 BalabanRG files verified (0 errors, 0 sorry)

---

*Last updated: 2026-03-29*
*Census method: individual file inspection with broad `\baxiom\b` regex in non-comment lines*
*Files checked: 20 × P8_PhysicalGap + 8 × Experimental/LieSUN = 28 files*
*L0–L8 open_hypotheses: see `registry/nodes.yaml` `open_hypotheses` fields*
