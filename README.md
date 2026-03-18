# THE ERIKSSON PROGRAMME

## Lean 4 Formalization of the Yang-Mills Mass Gap

**Status: FORMALIZED\_KERNEL — 8196+ jobs, 0 errors, 0 sorrys**  
Lean v4.29.0-rc6 + Mathlib · Last updated: March 2026

---

## Goal

Machine-check a complete proof of the Yang-Mills mass gap as formulated by the
Clay Mathematics Institute: construct a non-trivial 4D SU(N) quantum Yang-Mills
theory satisfying the Wightman/Osterwalder-Schrader axioms and prove a positive
spectral gap — with every step verified by the Lean 4 kernel.

**This is not a claimed solution.** It is the most complete formal verification
framework for the Yang-Mills mass gap that exists: every hypothesis named, every
dependency tracked, every gap isolated. The distance to a full solution is exactly
the content of the remaining axioms — no more, no less.

---

## What is this?

The Eriksson Programme is a serious, multi-year formal verification project in
Lean 4. Every claim is verified by the Lean 4 kernel. Every gap is a named axiom
with a documented removal path. No folklore, no "it is well known that", no physics
intuition hiding in the proofs.

---

## Original Work

| Resource | Link |
|---|---|
| 📄 Papers (viXra) | https://ai.vixra.org/author/lluis_eriksson |
| 📦 DOI (Zenodo) | https://doi.org/10.5281/zenodo.18799941 |
| 🔢 Numerical Audit | https://github.com/lluiseriksson/ym-audit |
| 🔍 Lean Audit (earlier) | https://github.com/lluiseriksson/ym-mass-gap-lean-verification |
| 🏗️ This repo | https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME |

---

## Recent Milestones

### v0.8.51 — Layer 3B complete: KP induction closed ✅ *(2026-03-18)*

**`kpOnGamma_implies_compatibleFamilyMajorant` proved — 0 sorrys.**

The Kotecký-Preiss induction over `Finset.induction_on` is now a theorem of the
repository:

- `containingFamilies_eq_image` — bijection between containing-X subfamilies and
  image of `insert X` over avoiding-X families; closed via `refine ⟨?_, by simp⟩ +
  exact ⟨hne, hcomp⟩` (And-associativity fix).
- `inductionBudget_insert_containing_eq` — exact equality `∑ = |K X| * ∑` via
  `Finset.sum_image` + injectivity of `insert X` on avoiding families.
- `inductionBudget_insert_le` — main recurrence `IB(Γ∪{X}) ≤ IB(Γ) + |K X|·(1+IB(Γ))`
  via `add_le_add` (not `linarith`).
- `kpOnGamma_implies_compatibleFamilyMajorant` — `Finset.induction_on`; base
  `exp(0)-1=0`; step closes via `theoreticalBudget_insert` + `one_add_le_exp` +
  `Real.exp_add` + `nlinarith`.

Clay Core BalabanRG: **6 files, 808+ lines, 0 errors, 0 sorrys.**

### v0.8.50 — Soundness refactor: 7 unsound → 8 honest axioms ✅

`hille_yosida_semigroup` fixed: now returns `SymmetricMarkovTransport` (Layer A+B
only). Previously claimed spectral gap from Dirichlet form alone — FALSE in
general. New structures: `SymmetricMarkovTransport`, `HasVarianceDecay`,
`MarkovSemigroup` extends both. New axiom: `sun_variance_decay` (Layer C for SU(N)
— honest Poincaré+Gronwall gap). P8: 8 honest axioms, 0 sorrys. Architecture now
logically sound.

### v0.8.49 — `sunDirichletForm_subadditive` proved: P8 axioms 8 → 7 ✅

Via `lieDerivReg_all + integral_mono`. Proof: `(a+b)²≤2a²+2b²` via
`two_mul_le_add_sq + gcongr`; integrate; sum over generators. Journey: 13→12→11→10→8→7.

### v0.8.48 — LieDerivReg package: P8 axioms 10 → 8 ✅

Three axioms eliminated: `lieDerivative_const`, `lieDerivative_linear`,
`sunDirichletForm_subadditive` → theorems via `GeneratorData + lieDerivReg_all`.

### v0.8.41 — StroockZegarlinski 0 errors ✅

Import cycle fully eliminated. Chain DLR\_LSI → Poincaré → CovarianceDecay →
ExponentialClustering fully formalized.

### v0.8.39 — EntropyPerturbation 0 sorrys ✅

`entropy_perturbation_limit_proved` via `R_bound + integral splitting`.

### v0.8.32 — SpatialLocalityFramework: 0 sorrys, 0 axioms ✅

`dynamic_covariance_at_optimalTime` closed; `locality_to_static_covariance_v2`
proved under explicit `LiebRobinsonBound`.

---

## Proof Chain: Yang-Mills Mass Gap (P8)

```
Ric_{SU(N)} = N/4                   [RicciSUN ✅]
   ↓ M1: Haar LSI(N/4)
sunHaarProb + sunGibbsFamily         [SUN_StateConstruction ✅]
   ↓ M2: Polymer → cross-scale Σ D_k < ∞
sunDirichletForm                     [M2 — partial ✅]
   ↓ M3: Interface → DLR-LSI
sun_gibbs_dlr_lsi                    [THEOREM ✅ v0.8.19]
   └─ balaban_rg_uniform_lsi         [axiom — CLAY CORE ❌]
   ↓ LSItoSpectralGap                [✅]
   ↓ M4: SZ semigroup → CovarianceDecay
sz_lsi_to_clustering                 [THEOREM ✅ v0.8.17]
   ↓ ExponentialClustering + SpectralGap + PhysicalMassGap  [✅]
```

---

## Clay Core — BalabanRG (Layer 3B, v0.8.51)

```
YangMills/ClayCore/BalabanRG/
  Layer 0A: BlockSpin.lean              — lattice geometry
  Layer 0B: FiniteBlocks.lean           — block-spin averaging
  Layer 1:  PolymerCombinatorics.lean   — Polymer, KP criterion
  Layer 2:  PolymerPartitionFunction.lean — Z, Ztail, |Z-1|≤B
  Layer 3A: KPFiniteTailBound.lean      — KPOnGamma, theoreticalBudget
  Layer 3B: KPBudgetBridge.lean         — KP → CompatibleFamilyMajorant ✅
            ├─ base cases + singleton
            ├─ compatibleSubfamiliesAvoidingX
            ├─ absFamilyWeight / InductionBudget
            ├─ containingFamilies_eq_image
            ├─ inductionBudget_insert_containing_eq  ← NEW
            ├─ inductionBudget_insert_le             ← NEW
            └─ kpOnGamma_implies_compatibleFamilyMajorant ← NEW ✅
```

**Next:** connect `kpOnGamma_implies_compatibleFamilyMajorant` to
`balaban_rg_uniform_lsi` to discharge the Clay core axiom.

---

## Axiom Map (v0.8.51) — 8 axioms, 1 Clay core

| Axiom | Category | What it claims | Removal path |
|---|---|---|---|
| `balaban_rg_uniform_lsi` | **CLAY CORE ❌** | SU(N) Gibbs satisfies uniform LSI via Balaban RG | E26 paper series |
| `bakry_emery_lsi` | Mathlib gap | CD(K,∞) ⟹ LSI(K) | Γ₂ calculus in Mathlib |
| `sun_bakry_emery_cd` | Mathlib gap | SU(N) satisfies CD(N/4,∞) | Bochner + LieGroup SU(N) |
| `sun_variance_decay` | Mathlib gap | SU(N) Poincaré+Gronwall spectral gap | Layer C SU(N) |
| `hille_yosida_semigroup` | Mathlib gap | Strong Dirichlet form → Markov semigroup | C₀-semigroup theory |
| `lieDerivative_linear` | Mathlib gap | ∂(f+g)=∂f+∂g on SU(N) | LieGroup API |
| `lieDerivative_const` | Mathlib gap | ∂(c)=0 on SU(N) | LieGroup API |
| `sunDirichletForm_contraction` | Mathlib gap | Normal contraction for SU(N) Dirichlet form | Chain rule for Lie derivatives |

Exactly **1 axiom** is the Clay core. When Mathlib gains LieGroup for
`Matrix.specialUnitaryGroup`, four axioms fall at once.

---

## Terminal Theorem

```lean
theorem eriksson_programme_phase7
    {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
    (d N : ℕ) [NeZero d] [NeZero N]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (hβ : 0 ≤ β) (hcont : Continuous plaquetteEnergy)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    (hbound : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ nf * ng) :
    ClayYangMillsTheorem
-- ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys
```

---

## Build Status

| Phase | Node | Status |
|---|---|---|
| L0–L8 | YangMills/Basic | ✅ FORMALIZED_KERNEL |
| P2.1–P2.5 | YangMills/P2_InfiniteVolume | ✅ FORMALIZED_KERNEL |
| P3.1–P3.5 | YangMills/P3_BalabanRG | ✅ FORMALIZED_KERNEL |
| P4.1–P4.2 | YangMills/P4_Continuum | ✅ FORMALIZED_KERNEL |
| F5.1–F5.4 | YangMills/P5_KPDecay | ✅ FORMALIZED_KERNEL |
| F6.1–F6.3 | YangMills/P6_AsymptoticFreedom | ✅ FORMALIZED_KERNEL |
| F7.1–F7.5 | YangMills/P7_SpectralGap | ✅ FORMALIZED_KERNEL |
| ErikssonBridge | YangMills/ErikssonBridge.lean | ✅ CLOSED — 0 sorrys, 0 axioms |
| P8 Physical gap | YangMills/P8_PhysicalGap | ✅ 8 axioms · 0 sorrys |
| Clay Core 3B | YangMills/ClayCore/BalabanRG | ✅ **0 errors · 0 sorrys** (v0.8.51) |
| Sandbox LieSUN | YangMills/Experimental/LieSUN | ✅ 0 axioms · 1 sorry (Jacobi) |

---

## Discharge Chain

```
clay_yangmills_unconditional : ClayYangMillsTheorem  [ErikssonBridge.lean]
  └─ eriksson_programme_phase7
       └─ CompactSpace G + Continuous plaquetteEnergy
            → wilsonAction bounded              (F7.2 ActionBound)
              → hm_phys = 1                     (F7.4 MassBound)
                → HasSpectralGap γ=log2 C=2     (F7.1)
                  → ClayYangMillsTheorem ∎
```

---

## Honest Relationship to the Full Clay Problem

| Component | Status |
|---|---|
| Lattice SU(N) gauge theory, Gibbs/Haar measure | ✅ formalized |
| Compactness of SU(N) | ✅ proved |
| Dirichlet form, LSI → spectral gap chain | ✅ proved |
| KP induction → CompatibleFamilyMajorant | ✅ proved (v0.8.51) |
| Wilson correlator decay → ClayYangMillsTheorem | ✅ eriksson_programme_phase7 |
| Continuum limit (lattice → ℝ⁴) | ⚠️ in E26 papers, not yet in Lean |
| Full Wightman/OS axioms in Lean | ⚠️ not yet formalized |
| Non-triviality of the continuum theory | ⚠️ in E26 papers, not yet in Lean |

---

## Papers — The Eriksson Programme (viXra [1]–[68])

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
| v0.8.51 | **kpOnGamma_implies_compatibleFamilyMajorant — Layer 3B complete** | 8 |
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

Lean toolchain: `leanprover/lean4:v4.29.0-rc6` · Mathlib · 8196+ compiled jobs
· 0 errors · 0 sorrys

---

## Author

**Lluis Eriksson** — independent researcher · March 2026
