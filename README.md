# THE ERIKSSON PROGRAMME

Lean 4 formalization for the Yang–Mills mass gap programme

> **Current status:** honest formal reduction with the P91 weak-coupling lane cleaned through the denominator-control window, a projection-safe P81 attack packet, a uniform slot-family bridge, the small-field slot isolated, and now the large-field suppression slot isolated as its own landing zone
> **Claim level:** this repository does **not** claim a finished unconditional Clay solution
> **Build health:** all touched targets must compile green
> **Lean / Mathlib:** Lean `v4.29.0-rc6` + Mathlib
> **Current version:** v0.9.21
> **Last updated:** March 2026

---

## 1. What this repository is

The Eriksson Programme is a Lean 4 formalization of the Yang–Mills mass gap programme.

Its current posture is explicit and conservative:
unresolved mathematics is isolated rather than hidden,
theorem-side dependencies are named rather than blurred together,
and the final theorem compiles only as an honest reduction through a small number of live `sorry` and `axiom` fronts.

The repository therefore exposes both:
- a large proved infrastructure for lattice Yang–Mills / RG / LSI / clustering,
- and a precise audit of what still blocks a fully unconditional Clay-level conclusion.

---

## 2. Build and entry points

Build the project with:

```bash
lake build YangMills
```

Key entry points:

| Purpose | File |
|---|---|
| Clay theorem definition | `YangMills/L8_Terminal/ClayTheorem.lean` |
| Top-level bridge theorem | `YangMills/ErikssonBridge.lean` |
| Physical mass-gap theorem | `YangMills/P8_PhysicalGap/PhysicalMassGap.lean` |
| Live theorem-side P81 bottleneck | `YangMills/ClayCore/BalabanRG/RGCauchyP81Interface.lean` |
| Theorem-side live target | `YangMills/ClayCore/BalabanRG/RGCauchyP81LiveTarget.lean` |
| Local P81 attack packet | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81AttackSurface.lean` |
| Uniform slot-family bridge | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81SlotFamily.lean` |
| Small-field slot | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81SmallFieldSlot.lean` |
| Large-field slot | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81LargeFieldSlot.lean` |
| Current audit frontier | `AXIOM_FRONTIER.md` |

---

## 3. Architecture overview

| Layer / phase | Directory | Role |
|---|---|---|
| L0 | `L0_Lattice/` | Finite lattice geometry, gauge configurations, Wilson action, basic SU geometry |
| L1 | `L1_GibbsMeasure/` | Gibbs measure construction, expectations, correlations |
| L2 | `L2_Balaban/` | Small/large-field decomposition, RG flow scaffolding, measurability |
| L3 | `L3_RGIteration/` | Block-spin RG iteration and gauge invariance of the induced measures |
| L4 | `L4_TransferMatrix/`, `L4_LargeField/`, `L4_WilsonLoops/` | Transfer matrix, spectral gap definitions, large-field suppression, Wilson observables |
| L5 | `L5_MassGap/` | Mass-gap assembly |
| L6 | `L6_FeynmanKac/`, `L6_OS/` | Feynman–Kac bridge and Osterwalder–Schrader reconstruction |
| L7 | `L7_Continuum/` | Continuum-limit bridge |
| L8 | `L8_Terminal/` | Terminal Clay theorem layer |
| P2 | `P2_MaxEntClustering/` | Max-entropy, recovery, clustering interfaces |
| P3 | `P3_BalabanRG/` | RG contraction and multiscale decay |
| P4 | `P4_Continuum/` | Continuum bridge assembly |
| P5 | `P5_KPDecay/` | KP decay, spectral-gap-to-decay bridges |
| P6 | `P6_AsymptoticFreedom/` | β-function and asymptotic-freedom lane |
| P7 | `P7_SpectralGap/` | Transfer-matrix gap and action bounds |
| P8 | `P8_PhysicalGap/` | LSI, Poincaré, SU(N) Dirichlet forms, semigroups, Ricci/Haar/physical mass-gap route |
| ClayCore | `ClayCore/BalabanRG/` | Polymer expansion, KP infrastructure, P80/P81/P91 machinery, quantitative theorem-side coherence surfaces |
| Experimental | `Experimental/` | Sandbox and non-imported future work |

---

## 4. Current mathematical position

This repository still does **not** claim a finished unconditional Clay solution.

What is already structurally rigid or mathematically substantial:

- the public SU compactness / Haar lane,
- a large zero-`sorry` lattice / Gibbs / RG / KP infrastructure,
- the theorem-side P81 coherence corridor and its public live-target surfaces,
- the P91 weak-coupling window in multiplicative form,
- the denominator-control bridge for that window,
- the rerouted P91 downstream and core consumers,
- the local `RGIncrementDecayP81AttackSurface`,
- the explicit `RGIncrementDecayP81SlotFamily` bridge,
- the dedicated `RGIncrementDecayP81SmallFieldSlot` landing zone,
- and now the dedicated `RGIncrementDecayP81LargeFieldSlot` landing zone for the second live P81 ingredient.

What remains live mathematically:

- the actual proof of `rg_increment_decay_P81`,
- therefore the actual proof of `RGCauchyP81LiveTarget`,
- therefore the actual package-level Balaban-RG uniform-LSI closure,
- and therefore the full unconditional Clay conclusion.

---

## 5. Sorry audit — live mathematical gaps

These are the mathematically live `sorry` fronts that still matter for unconditionality.

| Location | Name | Content |
|---|---|---|
| `RGCauchyP81Interface.lean` | `rg_increment_decay_P81` | Single-scale increment decay for the Bałaban RG map (the main bottleneck) |
| `LargeFieldSuppressionEstimate.lean` | `large_field_remainder_bound_P80` | Large-field remainder suppression |
| `BalabanCouplingRecursion.lean` | `asymptotic_freedom_implies_beta_growth` | P91 β-growth from asymptotic freedom |
| `P91DenominatorControl.lean` | `denominator_pos` | Denominator positivity in the old route |
| `P91OnestepDriftSkeleton.lean` | `uniform_drift_lower_bound_P91` | Uniform one-step drift lower bound |
| `RGContractiveEstimate.lean` | `large_field_suppression_bound` | P80 large-field suppression interface |
| `RGContractiveEstimate.lean` | `rg_cauchy_summability_bound` | P81/P82 Cauchy summability interface |

---

## 6. Axiom audit — known mathematics vs. physical inputs

The repository also contains `axiom` declarations. These are not all of the same kind.

| Category | Typical content | Examples |
|---|---|---|
| Mathlib gap | Standard mathematics missing from the current Lean ecosystem | `hille_yosida_semigroup`, `instIsTopologicalGroupSUN`, `sunDirichletForm_contraction`, `poincare_to_covariance_decay` |
| Physical input still to formalize | Yang–Mills / semigroup / Lieb–Robinson inputs not yet internalized | `sun_variance_decay`, `sun_lieb_robinson_bound`, curvature/LSI assumptions around the SU(N) lane |
| Live theorem-side bottleneck | Actual open front inside the present proof strategy | `rg_increment_decay_P81` and the P80/P91 fronts listed above |

---

## 7. Critical dependency path

The current critical path is:

```text
rg_increment_decay_P81
    ↓
RGCauchyP81LiveTarget
    ↓
theorem-side P81 frontier / coherence / audit corridor
    ↓
BalabanRG uniform-LSI package
    ↓
DLR-LSI / clustering / physical-mass-gap route
    ↓
ClayYangMillsTheorem
```

The theorem-side entrypoint now factors as:

```text
RGIncrementDecayP81SmallFieldSlot
    + RGIncrementDecayP81LargeFieldSlot
    + cluster-expansion-with-holes slot
        ↓
RGIncrementDecayP81SlotFamily
    ↓
RGIncrementDecayP81AttackSurface
    ↓
RGIncrementDecayP81UniformAttackSurface
    ↓
RGCauchyP81LiveTarget
    ↓
same downstream chain
```

---

## 8. The live P81 attack surface

The file `RGIncrementDecayP81AttackSurface.lean` packages the three paper-side ingredients singled out by the current strategy:

- small-field random-walk decay,
- large-field polymer suppression,
- cluster expansion / gluing with holes.

The file `RGIncrementDecayP81SlotFamily.lean` turns β-indexed theorem families for those three ingredients into the current live target and its public theorem-side consumers.

The file `RGIncrementDecayP81SmallFieldSlot.lean` isolates the first of those three ingredients.
The new file `RGIncrementDecayP81LargeFieldSlot.lean` isolates the second:
it records a dedicated family for large-field polymer suppression, ties it to the existing large-field threshold/norm surface, and provides the constructor that injects the first two slots plus the remaining cluster-expansion slot into the full slot-family bridge.

This does **not** prove P81.
It isolates the exact landing zone for the second genuinely live Bałaban ingredient.

---

## 9. Unconditionality audit

| Component | Status | Meaning |
|---|---|---|
| SU compactness route | Closed locally | Public topological front is compiled and exported |
| P91 weak-coupling window | Closed in corrected multiplicative form | Analytic front is no longer tied to the older denominator route |
| P91 denominator-control window | Closed | Clean positivity / unit-interval bridge in the multiplicative window |
| P91 downstream/core reroutes | Closed as infrastructure | Consumers now follow the corrected analytic lane |
| `RGIncrementDecayP81AttackSurface` | Closed as infrastructure | Projection-safe theorem-side packet exists |
| `RGIncrementDecayP81SlotFamily` | Closed as infrastructure | Uniform slot-family bridge into the live target exists |
| `RGIncrementDecayP81SmallFieldSlot` | Closed as infrastructure | First live P81 slot has a dedicated landing zone |
| `RGIncrementDecayP81LargeFieldSlot` | Closed as infrastructure | Second live P81 slot has a dedicated landing zone |
| `rg_increment_decay_P81` | Live mathematical gap | Main theorem-side bottleneck remains open |
| `RGCauchyP81LiveTarget` | Live mathematical surface | Waiting for actual P81 input rather than more architecture |
| Balaban-RG uniform-LSI closure | Live mathematical surface | Depends on the theorem-side bottleneck |
| Terminal Clay conclusion | Not yet unconditional | Still inherits the live theorem/axiom fronts |

---

## 10. Repository snapshot

| Item | Current state |
|---|---|
| Build posture | green on touched frontier targets |
| Public claim | honest reduction, not finished Clay proof |
| Preferred theorem-side bottleneck | `rg_increment_decay_P81` |
| Preferred theorem-side attack files | `RGIncrementDecayP81AttackSurface.lean`, `RGIncrementDecayP81SlotFamily.lean`, `RGIncrementDecayP81SmallFieldSlot.lean`, `RGIncrementDecayP81LargeFieldSlot.lean` |
| Preferred analytic correction files | `BalabanCouplingRecursionWindow.lean`, `P91DenominatorControlWindow.lean` |
| Current audit file | `AXIOM_FRONTIER.md` |
| Current version | v0.9.21 |

---

## Complete Paper Corpus

**68 publicly timestamped papers** — [ai.vixra.org/author/lluis_eriksson](https://ai.vixra.org/author/lluis_eriksson)  
Date range: 2025-12-16 → 2026-02-27 · DOI: [10.5281/zenodo.18799942](https://doi.org/10.5281/zenodo.18799942) · SHA-256 hashes: [`ym-audit`](https://github.com/lluiseriksson/ym-audit)

| # | Date | ai.viXra ID | Title |
|--:|------|-------------|-------|
| 1 | 2025-12-17 | [2512.0060](https://ai.vixra.org/abs/2512.0060) | Clustering, Recovery, and Locality in Algebraic Quantum Field Theory: Quantitative Bounds via Split Inclusions and Modular Theory |
| 2 | 2025-12-16 | [2512.0061](https://ai.vixra.org/abs/2512.0061) | The Conditional Maintenance Work Theorem: Operational Power Lower Bounds from Energy Pinching and a Split-Inclusion Blueprint for Type III AQFT |
| 3 | 2025-12-17 | [2512.0064](https://ai.vixra.org/abs/2512.0064) | The Heisenberg Cut as a Resource Boundary: An Operational Outlook from Coherence Maintenance Costs |
| 4 | 2025-12-19 | [2512.0070](https://ai.vixra.org/abs/2512.0070) | Stress Testing the Rate Inheritance Principle: Spectral Decoherence Rates and an Operational Resource Horizon |
| 5 | 2025-12-19 | [2512.0071](https://ai.vixra.org/abs/2512.0071) | Operational Coherence Maintenance: Proven Results, Conditional Interfaces, and Open Dynamical Gaps |
| 6 | 2025-12-19 | [2512.0072](https://ai.vixra.org/abs/2512.0072) | The Rate Inheritance Principle: From Static Correlations to Dynamical Decoherence Rates |
| 7 | 2025-12-19 | [2512.0073](https://ai.vixra.org/abs/2512.0073) | Finite-Dimensional Davies Interface Lemmas and TFIM Witness Tests for the Heisenberg Cut as a Resource Boundary |
| 8 | 2025-12-23 | [2512.0081](https://ai.vixra.org/abs/2512.0081) | Operational Coherence Maintenance and the Quantum–Classical Boundary: Formal Definitions, Falsifiable Protocols, and an Outlook for Cognitive Systems |
| 9 | 2025-12-24 | [2512.0084](https://ai.vixra.org/abs/2512.0084) | The Maintenance Constraint: How Resource Boundaries Shape Cognitive Availability |
| 10 | 2025-12-24 | [2512.0085](https://ai.vixra.org/abs/2512.0085) | Geometry, Membranes, and Life as a Resource Boundary: A Correct-by-Construction Operational Pipeline from Static Suppression to Maintenance Costs |
| 11 | 2025-12-27 | [2512.0091](https://ai.vixra.org/abs/2512.0091) | Technical Appendix: Heat Kernel, Fermions, and the Sign of Induced Gravity (Sign Conventions Fixed; Laplacian/Lichnerowicz Hinge Made Explicit) |
| 12 | 2025-12-31 | [2512.0101](https://ai.vixra.org/abs/2512.0101) | Beyond Gaussianity: Extending the Clustering–Recovery Bridge |
| 13 | 2025-12-31 | [2512.0102](https://ai.vixra.org/abs/2512.0102) | Heat Kernel Methods and the Sign of Induced Gravity: Resolving Conventions via the Laplacian–Lichnerowicz Identity |
| 14 | 2025-12-31 | [2512.0105](https://ai.vixra.org/abs/2512.0105) | Prefix-Path Bell Transport on IBM Quantum Hardware: High-Resolution Replication, Comparative Geometry Dependence, and Stress Tests of a Static–Dynamic Link |
| 15 | 2026-01-02 | [2601.0007](https://ai.vixra.org/abs/2601.0007) | Quantitative Recovery Bounds from Vacuum Clustering in Finite-Mode Gaussian States (A Regularized CCR Blueprint Motivated by Split Inclusions) |
| 16 | 2026-01-08 | [2601.0020](https://ai.vixra.org/abs/2601.0020) | Geometric Markov Bounds and Rate Inheritance Modulo Fixed Points: A Scalar Entropic Interface from Static Locality to Davies Dynamics |
| 17 | 2026-01-08 | [2601.0022](https://ai.vixra.org/abs/2601.0022) | The Rate Inheritance Principle: Operational Decoherence-Rate Envelopes and Stress Tests in Gapped Lattice Surrogates |
| 18 | 2026-01-08 | [2601.0023](https://ai.vixra.org/abs/2601.0023) | Finite-Dimensional Davies Interface Lemmas and TFIM Witness Tests for Separation-Dependent Decoherence Rate Envelopes |
| 19 | 2026-01-10 | [2601.0031](https://ai.vixra.org/abs/2601.0031) | From Static Recoverability to Maintenance Power: A Typed Pipeline with ω=0 Obstructions |
| 20 | 2026-01-11 | [2601.0034](https://ai.vixra.org/abs/2601.0034) | Modular Recovery from Split Inclusions: B-Minimal Bridge from QFT Collar Geometry to Approximate State Reconstruction |
| 21 | 2026-01-11 | [2601.0035](https://ai.vixra.org/abs/2601.0035) | A Non-Gaussian Clustering–Recovery Bridge via Conditional Mutual Information |
| 22 | 2026-01-12 | [2601.0038](https://ai.vixra.org/abs/2601.0038) | Operational Signatures of Criticality from Petz Recovery: Collar-Length Requirements in TFIM Exact Diagonalization |
| 23 | 2026-01-12 | [2601.0040](https://ai.vixra.org/abs/2601.0040) | Finite-Size Scaling of Petz Recovery Length in the TFIM: Threshold-Dependent Operational Exponents from Exact Diagonalization |
| 24 | 2026-01-11 | [2601.0042](https://ai.vixra.org/abs/2601.0042) | Emergent Information Distance from Petz Recovery: Temperature and Perturbation Dependence in TFIM Exact Diagonalization |
| 25 | 2026-01-13 | [2601.0043](https://ai.vixra.org/abs/2601.0043) | Recoverability Geometry: Distances and Embeddings from Quantum Markov Data |
| 26 | 2026-01-13 | [2601.0044](https://ai.vixra.org/abs/2601.0044) | Recoverability Length Scales and Wilson Loops in Lattice Gauge Theories: Protocol, Definitions, and Conjectural Links to Confinement Diagnostics |
| 27 | 2026-01-13 | [2601.0046](https://ai.vixra.org/abs/2601.0046) | Petz Recoverability in AQFT Via Conditional Expectations: a Framework and a Conditional Exponential Recovery Bound |
| 28 | 2026-01-13 | [2601.0047](https://ai.vixra.org/abs/2601.0047) | Petz Recoverability Versus Wilson-Loop Diagnostics in Z₂ Lattice Gauge Theory (2+1D) |
| 29 | 2026-01-14 | [2601.0050](https://ai.vixra.org/abs/2601.0050) | CMI-Based Recoverability Versus Wilson-Loop Diagnostics in Z₂ Lattice Gauge Theory (2+1D): Exact Diagonalization Benchmark on Small Open Lattices |
| 30 | 2026-01-14 | [2601.0051](https://ai.vixra.org/abs/2601.0051) | Petz Recoverability Versus Wilson-Loop Diagnostics in Z₂ Lattice Gauge Theory (2+1D): Benchmarks by Exact Diagonalization and Tensor-Network Ladders |
| 31 | 2026-01-17 | [2601.0064](https://ai.vixra.org/abs/2601.0064) | RIP-U and the ω=0 Obstruction in Davies Dynamics: Upper Envelopes, Witness Floors, and Falsification Protocols for Separation-Dependent Decoherence Rates |
| 32 | 2026-01-17 | [2601.0065](https://ai.vixra.org/abs/2601.0065) | Split-Regularized Recoverability in Type III AQFT: Conditional Expectations, Split-Dependent CMI, and an Audit-Friendly Contract |
| 33 | 2026-01-17 | [2601.0066](https://ai.vixra.org/abs/2601.0066) | Typed Pipeline for Recoverability–Rate–Power Links: A Contract Paper with a Closed Recoverability Lane and Falsification Criteria |
| 34 | 2026-01-24 | [2601.0099](https://ai.vixra.org/abs/2601.0099) | Program A: Semi-Infinite Conditional Mutual Information in the 1D Transverse-Field Ising Model (iMPS) |
| 35 | 2026-01-27 | [2601.0111](https://ai.vixra.org/abs/2601.0111) | Conditional Mutual Information and Petz Recovery in a Z₂ Lattice Gauge Ground State |
| 36 | 2026-01-28 | [2601.0115](https://ai.vixra.org/abs/2601.0115) | Algebraic Entropy and Conditional Mutual Information in a Tiny Gauge-Invariant Truncated Hilbert Space: A Reproducible Toy-Model Study with Effective Mixing Hamiltonians |
| 37 | 2026-02-07 | [2602.0020](https://ai.vixra.org/abs/2602.0020) | Gradient Flow Monotonicity and the Yang-Mills Mass Gap: A Conditional Reduction via Spectral Methods |
| 38 | 2026-02-07 | [2602.0021](https://ai.vixra.org/abs/2602.0021) | Yang-Mills Existence and Mass Gap: A Framework via Anomaly Algebra, Gradient-Flow Spectral Methods, and Quantum Information |
| 39 | 2026-02-08 | [2602.0032](https://ai.vixra.org/abs/2602.0032) | The Yang–Mills Mass Gap on the Lattice: a Self-Contained Proof Via Witten Laplacian and Constructive Renormalization |
| 40 | 2026-02-08 | [2602.0033](https://ai.vixra.org/abs/2602.0033) | The Yang–Mills Mass Gap on the Lattice: a Self-Contained Proof |
| 41 | 2026-02-08 | [2602.0035](https://ai.vixra.org/abs/2602.0035) | Morse–Bott Spectral Reduction and the Yang–Mills Mass Gap on the Lattice |
| 42 | 2026-02-08 | [2602.0036](https://ai.vixra.org/abs/2602.0036) | Geodesic Convexity and Structural Limits of Curvature Methods for the Yang-Mills Mass Gap on the Lattice |
| 43 | 2026-02-08 | [2602.0038](https://ai.vixra.org/abs/2602.0038) | Mass Gap for the Gribov-Zwanziger Lattice Measure: A Non-Perturbative Proof |
| 44 | 2026-02-08 | [2602.0040](https://ai.vixra.org/abs/2602.0040) | Uniform Poincaré Inequality for Lattice Yang-Mills Theory Via Multiscale Martingale Decomposition |
| 45 | 2026-02-12 | [2602.0041](https://ai.vixra.org/abs/2602.0041) | Uniform Log-Sobolev Inequality and Mass Gap for Lattice Yang–Mills Theory |
| 46 | 2026-02-12 | [2602.0046](https://ai.vixra.org/abs/2602.0046) | Ricci Curvature of the Orbit Space of Lattice Gauge Theory and Single-Scale Log-Sobolev Inequalities |
| 47 | 2026-02-12 | [2602.0051](https://ai.vixra.org/abs/2602.0051) | Uniform Coercivity, Pointwise Large-Field Suppression, and Unconditional Closure of the Lattice Yang-Mills Mass Gap at Weak Coupling in d=4 |
| 48 | 2026-02-12 | [2602.0052](https://ai.vixra.org/abs/2602.0052) | Interface Lemmas for the Multiscale Proof of the Lattice Yang-Mills Mass Gap |
| 49 | 2026-02-12 | [2602.0053](https://ai.vixra.org/abs/2602.0053) | DLR-Uniform Log-Sobolev Inequality and Unconditional Mass Gap for Lattice Yang-Mills at Weak Coupling |
| 50 | 2026-02-12 | [2602.0054](https://ai.vixra.org/abs/2602.0054) | From Uniform Log-Sobolev Inequality to Mass Gap for Lattice Yang-Mills at Weak Coupling |
| 51 | 2026-02-12 | [2602.0055](https://ai.vixra.org/abs/2602.0055) | Unconditional Uniform Log-Sobolev Inequality for SU(Nc) Lattice Yang-Mills at Weak Coupling |
| 52 | 2026-02-12 | [2602.0056](https://ai.vixra.org/abs/2602.0056) | Large-Field Suppression for Lattice Gauge Theories: from Balaban's Renormalization Group to Conditional Concentration |
| 53 | 2026-02-12 | [2602.0057](https://ai.vixra.org/abs/2602.0057) | Integrated Cross-Scale Derivative Bounds for Wilson Lattice Gauge Theory: Closing the Log-Sobolev Gap |
| 54 | 2026-02-14 | [2602.0063](https://ai.vixra.org/abs/2602.0063) | Conditional Continuum Limit of 4D SU(Nc) Yang-Mills Theory via Two-Layer Architecture, RG-Cauchy Uniqueness, and Step-Scaling Confinement |
| 55 | 2026-02-14 | [2602.0069](https://ai.vixra.org/abs/2602.0069) | The Balaban–Dimock Structural Package: Derivation of Polymer Representation, Oscillation Bounds, and Large-Field Suppression for Lattice Yang–Mills Theory from Primary Sources |
| 56 | 2026-02-14 | [2602.0070](https://ai.vixra.org/abs/2602.0070) | Doob Influence Bounds for Polymer Remainders in 4D Lattice Yang-Mills Renormalization |
| 57 | 2026-02-14 | [2602.0072](https://ai.vixra.org/abs/2602.0072) | Influence Bounds for Polymer Remainders in Balaban's Renormalization Group: Closing Assumption (B6) for the RG-Cauchy Programme in 4D Lattice Yang-Mills |
| 58 | 2026-02-14 | [2602.0073](https://ai.vixra.org/abs/2602.0073) | RG–Cauchy Summability for Blocked Observables in 4D Lattice Yang–Mills Theory via Balaban's Renormalization Group |
| 59 | 2026-02-15 | [2602.0077](https://ai.vixra.org/abs/2602.0077) | Ultraviolet Stability for Four-Dimensional Lattice Yang–Mills Theory Under a Quantitative Blocking Hypothesis |
| 60 | 2026-02-17 | [2602.0084](https://ai.vixra.org/abs/2602.0084) | Almost Reflection Positivity for Gradient-Flow Observables via Gaussian Localization in Lattice Yang-Mills Theory |
| 61 | 2026-02-17 | [2602.0085](https://ai.vixra.org/abs/2602.0085) | Ultraviolet Stability of Wilson-Loop Expectations in 4D Lattice Yang–Mills Theory Via Multiscale Gradient-Flow Smoothing |
| 62 | 2026-02-19 | [2602.0087](https://ai.vixra.org/abs/2602.0087) | Irrelevant Operators, Anisotropy Bounds, and Operator Insertions in Balaban's Renormalization Group for Four-Dimensional SU(N) Lattice Yang–Mills Theory |
| 63 | 2026-02-18 | [2602.0088](https://ai.vixra.org/abs/2602.0088) | Exponential Clustering and Mass Gap for Four-Dimensional SU(N) Lattice Yang–Mills Theory Via Balaban's Renormalization Group and Multiscale Correlator Decoupling |
| 64 | 2026-02-18 | [2602.0089](https://ai.vixra.org/abs/2602.0089) | Spectral Gap and Thermodynamic Limit for SU(N) Lattice Yang–Mills Theory via Log-Sobolev Inequalities and Complete Analyticity |
| 65 | 2026-02-19 | [2602.0091](https://ai.vixra.org/abs/2602.0091) | Closing the Last Gap in the 4D SU(N) Yang–Mills Construction: A Verified Terminal KP Bound and an Explicit Clay Checklist |
| 66 | 2026-02-19 | [2602.0092](https://ai.vixra.org/abs/2602.0092) | Rotational Symmetry Restoration and the Wightman Axioms for Four-Dimensional SU(N) Yang–Mills Theory |
| 67 | 2026-02-20 | [2602.0096](https://ai.vixra.org/abs/2602.0096) | The Master Map: An Audit-First, Attack-Resistant Navigation Guide to the Unconditional Solution of the 4D SU(N) Yang-Mills Existence and Mass Gap Problem |
| 68 | 2026-02-27 | [2602.0117](https://ai.vixra.org/abs/2602.0117) | Mechanical Audit Experiments and Reproducibility Appendix for a Companion-Paper Programme on 4D SU(N) Yang–Mills Existence and Mass Gap |

---

## 14. Author

**Lluis Eriksson** Independent researcher  
March 2026

## v1.0.26-alpha

Topological unconditionality phase started.

This milestone opens the first genuine axiom-elimination task in the repository:
formalizing compactness of the special unitary gauge group inside Lean, rather
than leaving it as external mathematical background.

No unconditional Clay claim is made at this stage. The repository remains an
honest reduction program until all terminal transfers and structural axioms are
discharged internally.

## v1.0.28-alpha

Topological assault on `SU(n)` advanced through the honest compactness reduction:
the entrywise-bounded half is now discharged by a direct Mathlib argument using
`Matrix.specialUnitaryGroup_le_unitaryGroup` together with
`entry_norm_bound_of_unitary`.

So the remaining ambient compactness gap is isolated to the closedness of the
special-unitary range.

## v1.0.29-alpha

The local special-unitary compactness assault now includes an honest closedness
layer. The ambient `SU(m)` range is identified with the closed cut
`{A | A ∈ unitaryGroup ∧ det A = 1}`, and together with the existing
entrywise-bounded witness this closes the local compactness target used by the
topological reduction.

## v1.0.30-alpha

The local special-unitary compactness transfer is now targeted as an internal
finite-dimensional theorem: closedness plus entrywise boundedness should imply
compactness of the ambient `SU(m)` range without any external transfer input.

<!-- SU_UNCONDITIONALITY_START -->
## Special-unitary compactness: unconditional status

The local special-unitary compactness block is now closed **unconditionally** inside the repository.

### Public API

Import:

- `YangMills.ClayCore.BalabanRG.SpecialUnitaryCompact`

Public theorems:

- `specialUnitary_compact_range_target`
- `specialUnitary_topology_gap_closed`

### Internal decomposition

The proof path is split into the following layers:

- `SpecialUnitaryCompactCore`
- `SpecialUnitaryCompactReduction`
- `SpecialUnitaryEntrywiseBounded`
- `SpecialUnitaryClosed`
- `SpecialUnitaryClosedEntrywiseBoundedToCompact`
- `SpecialUnitaryCompactUnconditional`

### Internal unconditional closure

Internal unconditional closure is provided by:

- `specialUnitary_compact_unconditional`
- `specialUnitary_topology_package_unconditional`

This means the local compactness route for the ambient special-unitary range is no longer left as an external transfer-only gap: the closedness step, boundedness step, and the closed+bounded ⇒ compact transfer are now all discharged inside the repository.

### Current status

- SU block build: green
- Public API stabilized
- Temporary recon/smoke files removed
- Final sanity build without warnings
<!-- SU_UNCONDITIONALITY_END -->

---

##


## Last-mile package

`BalabanRGUniformLSILastMileOutput` is the canonical packaged output of the current last mile: if the unique live target is discharged, the scale target, Haar-LSI target, and frontier package follow at once.


## Closure package

`BalabanRGUniformLSIClosurePackage` is the canonical public structured output of the current last mile. It replaces a bare conjunction by named fields for the scale target, Haar target, and frontier package.
