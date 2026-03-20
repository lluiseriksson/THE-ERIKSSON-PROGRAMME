# THE ERIKSSON PROGRAMME
Lean 4 Formalization of the Yang-Mills Mass Gap

**Status:** FORMALIZED_KERNEL — 8270+ jobs, 0 errors, 0 sorrys  
**Lean:** v4.29.0-rc6 + Mathlib  
**Last updated:** March 2026

## Goal

Machine-check a complete proof architecture for the Yang-Mills mass gap in Lean 4:
construct a non-trivial 4D SU(N) quantum Yang-Mills theory satisfying the
Wightman/Osterwalder-Schrader axioms and prove a positive spectral gap, with
every formalized step verified by the Lean 4 kernel.

This repository does **not** claim a finished Clay solution. What it does claim is
a maximally explicit formal verification framework: every dependency named,
every bridge tracked, every remaining gap isolated.

## What this repository is

The Eriksson Programme is a serious long-horizon formal verification project.
Its working principles are:

- every formal statement checked by Lean 4,
- every unresolved ingredient named explicitly,
- no hidden folklore assumptions,
- no informal “standard argument” placeholders inside the formal chain.

## Repository snapshot

- **Build health:** 8270+ jobs, 0 errors, 0 sorrys
- **Clay core:** 1 Clay core axiom
- **Named axioms:** 8
- **BalabanRG status:** decomposed into independent targets with concrete discharged subpaths
- **Current bridge status:** singleton, finite full, concrete `L¹`, and weighted `L¹` routes operational

## Original work and audit trail

| Resource | Link |
|---|---|
| Papers — The Eriksson Programme (viXra [1]–[68])

Papers organised as a closure tree.

| Symbol | Meaning |
|---|---|
| 🟢 CLOSES YM | On the unconditional closure path of ClayYangMillsTheorem |
| 🔵 SUPPORT | Provides lemmas / infrastructure consumed by the trunk |
| ⚪ CONTEXT | Independent contribution; not on the unconditional YM path |

### 🌳 TRUNK — Unconditional closure of Yang-Mills (viXra [61]–[68])

| Internal | viXra | Title | Role |
|---|---|---|---|
| P91 | [68] | Mechanical Audit Experiments and Reproducibility Appendix | 🟢 Terminal audit: 29/29 PASS |
| P90 | [67] | The Master Map | 🟢 Threat model, Triangular Mixing Lock, KP margin |
| P89 | [65] | Closing the Last Gap — Terminal KP Bound & Clay Checklist | 🟢 δ=0.021 < 1, polymer → OS → Wightman |
| P88 | [66] | Rotational Symmetry Restoration and the Wightman Axioms | 🟢 OS1 restoration, Wightman with Δ>0 |
| P87 | [62] | Irrelevant Operators, Anisotropy Bounds (Balaban RG) | 🟢 Symanzik classification, O(4)-breaking operators |
| P86 | [63] | Coupling Control, Mass Gap, OS Axioms, Non-triviality | 🟢 Coupling control, OS axioms |
| P85 | [64] | Spectral Gap and Thermodynamic Limit via Log-Sobolev | 🟢 LSI → spectral gap → thermodynamic limit |

### 🌿 BRANCH A — Balaban RG & UV Stability (viXra [54]–[61])

| Internal | viXra | Title | Role |
|---|---|---|---|
| P84 | [61] | UV Stability of Wilson-Loop Expectations | 🔵 UV stability via gradient-flow |
| P83 | [60] | Almost Reflection Positivity for Gradient-Flow Observables | 🔵 Reflection positivity |
| P82 | [59] | UV Stability under Quantitative Blocking Hypothesis | 🔵 UV stability via blocking |
| P81 | [58] | RG–Cauchy Summability for Blocked Observables | 🔵 RG-Cauchy summability |
| P80 | [57] | Influence Bounds for Polymer Remainders — Closing B6 | 🔵 Closes assumption B6 |
| P79 | [56] | Doob Influence Bounds for Polymer Remainders | 🔵 Doob martingale bounds |
| P78 | [55] | The Balaban–Dimock Structural Package | 🔵 Polymer repr., large-field suppression |
| P77 | [54] | Conditional Continuum Limit via Two-Layer + RG-Cauchy | 🔵 Conditional continuum limit |

### 🌿 BRANCH B — Log-Sobolev & Mass Gap at weak coupling (viXra [44]–[53])

| Internal | viXra | Title | Role |
|---|---|---|---|
| P76 | [53] | Cross-Scale Derivative Bounds — Closing the Log-Sobolev Gap | 🔵 Closes the LSI gap |
| P75 | [52] | Large-Field Suppression: Balaban RG to Conditional Concentration | 🔵 Large-field suppression |
| P74 | [51] | Unconditional Uniform Log-Sobolev Inequality for SU(Nc) | 🟢 Unconditional LSI |
| P73 | [50] | From Uniform Log-Sobolev to Mass Gap at Weak Coupling | 🟢 LSI → mass gap |
| P72 | [49] | DLR-Uniform Log-Sobolev and Unconditional Mass Gap | 🟢 DLR + LSI → unconditional mass gap |
| P71 | [48] | Interface Lemmas for the Multiscale Proof | 🔵 Interface lemmas |
| P70 | [47] | Uniform Coercivity and Unconditional Closure at Weak Coupling | 🟢 Unconditional closure |
| P69 | [46] | Ricci Curvature of the Orbit Space and Single-Scale LSI | 🔵 Geometric foundation for LSI |
| P68 | [45] | Uniform Log-Sobolev Inequality and Mass Gap | 🔵 Core LSI paper |
| P67 | [44] | Uniform Poincaré Inequality via Multiscale Martingale Decomposition | 🔵 Poincaré → LSI |

### 🌿 BRANCH C — Earlier proofs & geometric methods (viXra [38]–[43])

| Internal | viXra | Title | Role |
|---|---|---|---|
| P66 | [43] | Mass Gap for the Gribov-Zwanziger Lattice Measure | 🔵 Non-perturbative GZ proof |
| P65 | [42] | Geodesic Convexity and Structural Limits of Curvature Methods | ⚪ Identifies limits of curvature approach |
| P64 | [41] | Morse–Bott Spectral Reduction and the YM Mass Gap | 🔵 Morse–Bott reduction |
| P63 | [40] | The YM Mass Gap on the Lattice: a Self-Contained Proof | 🔵 Earlier self-contained proof |
| P62 | [39] | YM Mass Gap via Witten Laplacian and Constructive Renormalization | 🔵 Witten Laplacian approach |
| P61 | [38] | YM Existence and Mass Gap: Anomaly Algebra, Gradient-Flow, QI | 🔵 Framework paper |

### ⚪ CONTEXT — AQFT, Quantum Information, Decoherence, Gravity (viXra [1]–[37])

<details>
<summary>Expand context papers [1]–[37]</summary>

These papers provide background, motivation, and structural context for the
programme but are not on the unconditional closure path of ClayYangMillsTheorem.
Full list available at https://ai.vixra.org/author/lluis_eriksson

</details>

---

## P8 Physical Gap — Architecture (v0.8.51)

```
SUN_StateConstruction ──→ SUN_DirichletCore ──→ SUN_LiebRobin
        ↑                         │                    │
   SUN_Compact              LSIDefinitions    SpatialLocalityFramework
                                                        │
                                               MarkovSemigroupDef
```

**Key results proved (0 sorrys):**
- `isCompact_specialUnitaryGroup` — SU(N) is compact
- `dynamic_covariance_at_optimalTime` — exponential covariance decay
- `locality_to_static_covariance_v2` — abstract Lieb-Robinson bound
- `sun_locality_to_covariance` — concrete SU(N) covariance decay
- `entropy_perturbation_limit_proved` — `(1+t²c)log(1+t²c)/t² → 2c`
- `sz_covariance_bridge` — Cauchy-Schwarz + variance decay
- `kpOnGamma_implies_compatibleFamilyMajorant` — **KP induction closed** ✅

---

## Experimental Sandbox: LieSUN (v0.8.48)

| File | Status | Key content |
|---|---|---|
| LieDerivativeDef.lean | ✅ 0 axioms, 0 sorrys | `lieDerivativeVia` + linearity from `deriv_add` |
| LieExpCurve.lean | ✅ 0 errors, 1 sorry | `matExp`, unitarity proved, `lieExpCurve` on SU(N) |
| LieDerivativeBridge.lean | ✅ 0 errors, 0 sorrys | `lieDerivExp` + 3 abstract theorems |

Key result: `matExp_skewHerm_unitary` — `Xᴴ=-X → (matExp X)ᴴ·matExp X=1` —
proved without axioms.

---

## Milestone Log

| Version | Achievement | Axioms |
|---|---|---|
| v0.8.58 | **Layer 8A — PhysicalRGRates: 4 quantitative targets (0 sorrys)** | 8 |
| v0.8.57 | Layer 7 complete — all BalabanRGPackage fields formally satisfiable | 8 |
| v0.8.56 | Layer 6 — BalabanRG decomposition: monolith → 4 targets (0 sorrys) | 8 |
| v0.8.56 | **Layer 6 — BalabanRG decomposition: monolith → 4 targets (0 sorrys)** | 8 |
| v0.8.55 | Layer 4C — PolymerLogLowerBound: two-sided log Z (0 sorrys) | 8 |
| v0.8.54 | Layer 4B — PolymerLogBound: positivity + log Z (0 sorrys) | 8 |
| v0.8.53 | Layer 4A — KPConsequences: |Z-1|, positivity, log Z (0 sorrys) | 8 |
| v0.8.52 | Layer 3B sealed — KP induction fully mechanized, 0 errors | 8 |
| v0.8.51 | kpOnGamma_implies_compatibleFamilyMajorant — Layer 3B complete | 8 |
| v0.8.50 | Soundness refactor: unsound → 8 honest axioms | 8 |
| v0.8.49 | sunDirichletForm_subadditive THEOREM | 7 |
| v0.8.48 | LieDerivReg package: 10 → 8 axioms | 8 |
| v0.8.47 | Lie derivative spike: measurability gap identified | 10 |
| v0.8.45 | instFintypeLieGenIndex eliminated: 11 → 10 axioms | 10 |
| v0.8.43 | Phantom axiom eliminated: 12 → 11 axioms | 11 |
| v0.8.41 | StroockZegarlinski 0 errors | 11 |
| v0.8.40 | PoincareCovarianceRoadmap import cycle broken | 11 |
| v0.8.39 | EntropyPerturbation 0 sorrys | 11 |
| v0.8.32 | SpatialLocalityFramework: 0 sorrys, 0 axioms | 11 |
| v0.8.21 | LieSUN sandbox: matExp unitarity, lieExpCurve | 8 |
| v0.8.20 | sun_haar_lsi THEOREM | 7 |
| v0.8.19 | sun_gibbs_dlr_lsi THEOREM — Clay monolith decomposed | 6 |
| v0.8.17 | sz_lsi_to_clustering ELIMINATED | 6 |

---

## Reproducible Build

```bash
git clone https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME
cd THE-ERIKSSON-PROGRAMME
lake build
```

Lean toolchain: `leanprover/lean4:v4.29.0-rc6` · Mathlib · 8250+ compiled jobs
· 0 errors · 0 sorrys

---

## Author

**Lluis Eriksson** — independent researcher · March 2026 · v0.8.56

Finite-support full bridge control is now packaged and reaches a high-level consumer.
Finite-support full bridge now reaches `CauchyDecayFromAF` via a dedicated alias.


## v1.0.8-alpha
Pointwise singleton control now bridges both large-field and Cauchy bounds
into the full canonical geometric bridge path, and this reaches the
high-level consumer `CauchyDecayFromAF`.


## v1.0.10-alpha
A first concrete `ActivityNorm` model is now available: a finite `L¹` norm on
polymer activity families. This concretely discharges the singleton native
evaluation and Cauchy bounds with constant `1`, and exposes the resulting
high-level singleton path through `CauchyDecayFromAF`.


## v1.0.11-alpha
The concrete finite `L¹` activity norm now discharges the full finite-support
bridge bounds in the canonical full geometry. This yields a concrete packaged
finite full control and exposes the resulting high-level finite full path
through `CauchyDecayFromAF`.

## v1.0.13-alpha
The abstract polymer-weight interface is now in place, and the first genuinely nontrivial concrete weight has been instantiated:
the native polymer-size weight `w(X)=|X|`.

This validates the weighted evaluation path and the finite full bridge path through the abstract interface, and exposes the resulting
high-level finite full size-weight route in `CauchyDecayFromAF`.


v1.0.14-alpha
An exponential polymer-size weight `w_a(X)=exp(a*|X|)` is now available through the abstract polymer-weight interface. This gives a KP-shaped weighted `ActivityNorm` family, recovers the finite-full weighted bridge control path, and exposes the resulting high-level exp-size-weight route through `CauchyDecayFromAF`.


v1.0.15-alpha
The exponential polymer-size weight path is now structurally organized. We added reusable lemmas for
`w_a(X)=exp(a*|X|)` and rewrote the native KP pointwise activity bound in exp-weight language,
including the weighted smallness form `|K X| * w_a(X) ≤ a`.

## v1.0.16-alpha
The KP-side weighting architecture is now abstracted and operational.

- `KPWeightedActivityInterface`: abstract KP-side polymer weights
- `KPWeightedBudgetInterface`: weighted compatible-family majorants and induction budgets
- `KPWeightedBudgetToPartition`: weighted budgets recover native `SmallActivityBudget` and `|Z - 1| ≤ B`
- Exponential polymer-size weight is the first concrete KP-side instance
- Conservative exp-size-weight specialization is closed through explicit `w ≥ 1`

## v1.0.18-alpha

Weighted KP budgets now propagate all the way to positivity and free-energy control.
From weighted compatible-family majorants / induction budgets with `1 ≤ w(X)`, the
formal chain now yields `|Z - 1| ≤ B`, `0 < Z` for `B < 1`, `log Z ≤ B`, and
`|log Z| ≤ 2B` for `B ≤ 1/2`, with automatic specialization to the exponential
polymer-size weight.

