# THE ERIKSSON PROGRAMME

Lean 4 formalization for the Yang–Mills mass gap programme.

> **Version:** v0.9.31  
> **Repository state summarized at commit:** pending this commit  
> **Lean / Mathlib:** Lean `v4.29.0-rc6` + Mathlib  
> **Build command:** `lake build YangMills`  
> **Claim level:** this repository does **not** claim a finished unconditional Clay solution

---

## 1. What this repository is

The Eriksson Programme is a large Lean 4 formalization of the Yang–Mills mass gap programme. It packages lattice geometry, Gibbs measures, renormalization, polymer expansions, logarithmic Sobolev input, clustering, and terminal mass-gap assembly into a single proof-oriented codebase.

This repository should be read as an **honest reduction** and audit trail. It explicitly distinguishes:
- what is already proved in Lean,
- what is only discharged under current placeholder semantics,
- what remains live mathematically,
- what remains live because of Mathlib or physical-input axioms.

---

## 2. Critical semantic note

The theorem-side interface `rg_increment_decay_P81` is no longer a `sorry`.  
However, that discharge is still obtained under the **current placeholder RG semantics**, where `RGBlockingMap` is the zero map.

So the P80/P81 theorem corridor is green **in the current repository semantics**, but this is not yet the final intended Bałaban theorem. The decisive future step remains:

1. replace `RGBlockingMap := 0` by the explicit Bałaban blocking map,
2. rebuild the same contraction corridor under nontrivial RG dynamics,
3. keep the corrected multiplicative-window P91 lane as the only public coupling surface.

---

## 3. Quick start

### Build

```bash
lake build YangMills
```

### Main entry files

| Purpose                          | File                                                                 |
| -------------------------------- | -------------------------------------------------------------------- |
| Terminal Clay theorem definition | `YangMills/L8_Terminal/ClayTheorem.lean`                             |
| Top-level bridge theorem         | `YangMills/ErikssonBridge.lean`                                      |
| Physical mass-gap route          | `YangMills/P8_PhysicalGap/PhysicalMassGap.lean`                      |
| P81 interface                    | `YangMills/ClayCore/BalabanRG/RGCauchyP81Interface.lean`             |
| Corrected public P91 shim        | `YangMills/ClayCore/BalabanRG/P91CorrectedWindowPublicShim.lean`     |
| Corrected P91 consumer packet    | `YangMills/ClayCore/BalabanRG/P91CorrectedWindowConsumerPacket.lean` |
| Placeholder RG map               | `YangMills/ClayCore/BalabanRG/BalabanBlockingMap.lean`               |
| Frontier audit                   | `AXIOM_FRONTIER.md`                                                  |

---

## 4. Architecture

### Layer structure

| Layer | Directory                                                 | Role                                                                            |
| ----- | --------------------------------------------------------- | ------------------------------------------------------------------------------- |
| L0    | `L0_Lattice/`                                             | Finite lattice geometry, gauge configurations, Wilson action, basic SU geometry |
| L1    | `L1_GibbsMeasure/`                                        | Gibbs measures, expectations, correlations                                      |
| L2    | `L2_Balaban/`                                             | Small/large-field decomposition, RG scaffolding, measurability                  |
| L3    | `L3_RGIteration/`                                         | Block-spin RG iteration and gauge invariance                                    |
| L4    | `L4_TransferMatrix/`, `L4_LargeField/`, `L4_WilsonLoops/` | Transfer matrix, large-field suppression, Wilson observables                    |
| L5    | `L5_MassGap/`                                             | Mass-gap assembly                                                               |
| L6    | `L6_FeynmanKac/`, `L6_OS/`                                | Feynman–Kac bridge and Osterwalder–Schrader reconstruction                      |
| L7    | `L7_Continuum/`                                           | Continuum-limit bridge                                                          |
| L8    | `L8_Terminal/`                                            | Terminal Clay theorem layer                                                     |

### Phase structure

| Phase | Directory               | Role                                                                 |
| ----- | ----------------------- | -------------------------------------------------------------------- |
| P2    | `P2_MaxEntClustering/`  | Max-entropy and clustering interfaces                                |
| P3    | `P3_BalabanRG/`         | RG contraction and multiscale decay                                  |
| P4    | `P4_Continuum/`         | Continuum assembly                                                   |
| P5    | `P5_KPDecay/`           | KP decay and spectral-gap-to-decay bridges                           |
| P6    | `P6_AsymptoticFreedom/` | Beta function and asymptotic-freedom lane                            |
| P7    | `P7_SpectralGap/`       | Transfer-matrix gap and action bounds                                |
| P8    | `P8_PhysicalGap/`       | LSI, Poincaré, Dirichlet forms, Haar, Ricci, physical mass-gap route |

### Core infrastructure

| Component    | Directory             | Role                                                |
| ------------ | --------------------- | --------------------------------------------------- |
| ClayCore     | `ClayCore/BalabanRG/` | Main Balaban / polymer / KP / P80-P81-P91 machinery |
| Experimental | `Experimental/`       | Sandbox and non-imported future work                |

---

## 5. Current mathematical position

### Green and load-bearing under current semantics

* the full P80/P81 theorem corridor is green under the current zero-map RG semantics,
* all three Lemma 6.2 slots are isolated and populated,
* `rg_increment_decay_P81` is discharged,
* the corrected multiplicative-window P91 public surface is green,
* drift and divergence on that public surface are direct and no longer borrowed from the old lane,
* the legacy P91 route is formally certified as too weak.

### Still live in the intended final mathematical sense

* `RGBlockingMap := 0` still has to be replaced by the explicit Bałaban blocking map,
* theorem consumers should keep migrating onto the corrected-window packet/shim,
* legacy P91 `sorry`s still exist as deprecated residue,
* the axiom fronts in the physical and Mathlib layers remain explicit.

---

## 6. Connection to the companion paper (Bloque 4)

| Paper section | Content                                       | Lean correspondence                                    |
| ------------- | --------------------------------------------- | ------------------------------------------------------ |
| §2            | Lattice setup, scales, observables            | `L0_Lattice/`, `L1_GibbsMeasure/`                      |
| §3            | Balaban RG framework                          | `ClayCore/BalabanRG/` infrastructure                   |
| §4            | Coupling control                              | `BalabanCouplingRecursion*`, `P91*` files              |
| §5            | Terminal cluster expansion                    | `PolymerPartitionFunction.lean`, `KPBudgetBridge.lean` |
| §6            | Single-scale UV error / multiscale decoupling | P81 slot machinery                                     |
| §7            | Final mass-gap assembly                       | `PhysicalMassGap.lean` and terminal layers             |
| §8            | OS reconstruction                             | `L6_OS/OsterwalderSchrader.lean`                       |

### Lemma 6.2 decomposition in Lean

| Paper mechanism                    | Lean slot                      | Current state                       |
| ---------------------------------- | ------------------------------ | ----------------------------------- |
| Small-field random-walk decay      | `smallFieldRandomWalkDecay`    | populated                           |
| Large-field polymer suppression    | `largeFieldPolymerSuppression` | populated                           |
| Cluster expansion with holes       | `clusterExpansionWithHoles`    | populated                           |
| Glue into `rg_increment_decay_P81` | `RGCauchyP81Interface.lean`    | discharged under zero-map semantics |

---

## 7. P81 slot system

### Slot files

| Role                   | File                                                                        |
| ---------------------- | --------------------------------------------------------------------------- |
| Attack surface         | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81AttackSurface.lean`        |
| Slot family            | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81SlotFamily.lean`           |
| Small-field slot       | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81SmallFieldSlot.lean`       |
| Large-field slot       | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81LargeFieldSlot.lean`       |
| Cluster-expansion slot | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81ClusterExpansionSlot.lean` |

### Witness files

| Witness             | File                                                                           | Current semantic source    |
| ------------------- | ------------------------------------------------------------------------------ | -------------------------- |
| Small-field witness | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81SmallFieldWitness.lean`       | field-split / RG semantics |
| Large-field witness | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81LargeFieldWitness.lean`       | P80 skeleton route         |
| Cluster witness     | `YangMills/ClayCore/BalabanRG/RGIncrementDecayP81ClusterExpansionWitness.lean` | hole-split semantics       |

This means the P81 corridor is no longer blocked by theorem-side packaging. The remaining issue is semantic: it must eventually be rebuilt once the placeholder RG map is replaced.

---

## 8. Corrected P91 public lane

The corrected theorem-side public surface for P91 is the multiplicative window

```text
β · (3 · b₀) < 2
```

and not the weaker legacy condition

```text
β < 2 / b₀.
```

### Public corrected files

| Role                                 | File                                                                 |
| ------------------------------------ | -------------------------------------------------------------------- |
| Corrected AF / window lane           | `YangMills/ClayCore/BalabanRG/BalabanCouplingRecursionWindow.lean`   |
| Corrected denominator control        | `YangMills/ClayCore/BalabanRG/P91DenominatorControlWindow.lean`      |
| Corrected public shim                | `YangMills/ClayCore/BalabanRG/P91CorrectedWindowPublicShim.lean`     |
| Direct corrected drift / divergence  | `YangMills/ClayCore/BalabanRG/P91UniformDriftWindowDirect.lean`      |
| Stable corrected consumer packet     | `YangMills/ClayCore/BalabanRG/P91CorrectedWindowConsumerPacket.lean` |
| Legacy-route audit by counterexample | `YangMills/ClayCore/BalabanRG/P91LegacyRouteCounterexample.lean`     |

### Interpretation at v0.9.31

The public surface now has:

* corrected-window AF / growth,
* corrected-window denominator control,
* direct corrected-window drift,
* direct corrected-window divergence,
* a stable theorem-side consumer packet for migration away from legacy imports.

---

## 9. Sorry audit

### Discharged theorem-side placeholders

| Name                              | Status                              |
| --------------------------------- | ----------------------------------- |
| `rg_increment_decay_P81`          | discharged under zero-map semantics |
| `large_field_remainder_bound_P80` | discharged                          |
| `large_field_suppression_bound`   | discharged                          |
| `rg_cauchy_summability_bound`     | discharged                          |

### Remaining live `sorry`s in main load-bearing files

| Location                        | Name                                     | Interpretation                 |
| ------------------------------- | ---------------------------------------- | ------------------------------ |
| `BalabanCouplingRecursion.lean` | `asymptotic_freedom_implies_beta_growth` | deprecated legacy P91 artifact |
| `P91DenominatorControl.lean`    | `denominator_pos`                        | deprecated legacy P91 artifact |
| `P91OnestepDriftSkeleton.lean`  | `uniform_drift_lower_bound_P91`          | deprecated legacy P91 artifact |

These should not be read as the active frontier of the preferred public lane. They remain on the old P91 route, which is deprecated and formally audited as too weak.

### Experimental `sorry`s

Three additional `sorry`s remain in `Experimental/`, but those files are non-load-bearing.

---

## 10. Axiom audit

### Category A — Mathlib gaps

* `hille_yosida_semigroup`
* `instIsTopologicalGroupSUN`
* `sunDirichletForm_contraction`
* `poincare_to_covariance_decay`

### Category B — physical inputs still axiomatized

* `sun_variance_decay`
* `sun_lieb_robinson_bound`
* `sun_bakry_emery_cd`
* `sun_haar_lsi`

### Category C — deprecated theorem residue

The three remaining old-route P91 `sorry`s above belong here pragmatically: they still exist in files, but they are no longer the preferred public theorem-side lane.

---

## 11. What is already proved

Major green results already present include:

* SU(N) compactness,
* Haar probability measure,
* Ricci curvature computations,
* LSI → Poincaré,
* Stroock–Zegarlinski clustering bridges,
* locality / covariance decay bridges,
* Wilson action gauge invariance,
* block-spin mechanics,
* corrected-window P91 theorem-side routes,
* large KP / polymer infrastructure in `ClayCore/BalabanRG/`.

---

## 12. Dependency picture

### Current theorem-side corridor

```text
rg_increment_decay_P81   -- discharged under current zero-map semantics
    ↓
RGCauchyP81LiveTarget
    ↓
P81 frontier / coherence corridor
    ↓
BalabanRG uniform-LSI package
    ↓
DLR-LSI / clustering / physical mass gap
    ↓
ClayYangMillsTheorem
```

### Important qualifier

This corridor is theorem-side green in the current semantics, but the intended final mathematical version still requires rebuilding it after replacing the placeholder `RGBlockingMap := 0` by the explicit Bałaban map.

---

## 13. Current frontier

### Cleanup frontier

* migrate any remaining theorem consumers off legacy P91 files,
* keep the corrected public shim / packet as the unique public theorem-side P91 surface,
* retire old-route residue once it is not load-bearing anywhere.

### Real semantic frontier

* replace the placeholder zero RG map with the explicit Bałaban blocking map,
* rebuild the P80/P81 corridor with nontrivial RG dynamics,
* retain the corrected multiplicative-window P91 lane as the coupling interface for that rebuild.

The second frontier is the mathematically decisive one.

---

## 14. Version trajectory

| Version | Commit              | Milestone                                                    |
| ------- | ------------------- | ------------------------------------------------------------ |
| v0.9.18 | `1762d76`           | fixed uniform attack surface with `Nonempty` packet          |
| v0.9.19 | `35c3b1a`           | slot-family bridge                                           |
| v0.9.20 | `b3e1d12`           | isolated small-field slot                                    |
| v0.9.21 | `cd8213a`           | isolated large-field slot                                    |
| v0.9.22 | `b010a18`           | isolated cluster-expansion slot                              |
| v0.9.23 | `f0db363`           | populated large-field witness                                |
| v0.9.24 | `14d5bb8`           | populated small-field witness                                |
| v0.9.25 | `c289474`           | populated cluster witness                                    |
| v0.9.26 | `dfb1ff3`           | discharged `rg_increment_decay_P81` under zero-map semantics |
| v0.9.27 | `1ca5eb2`           | cleared semantic-echo P80/P81 wrapper `sorry`s               |
| v0.9.28 | `b703afa`           | certified legacy P91 route as too weak                       |
| v0.9.29 | `271f421`           | corrected multiplicative-window public shim                  |
| v0.9.30 | `27b95b0`           | direct multiplicative-window drift/divergence                |
| v0.9.31 | pending this commit | stable corrected-window consumer packet                      |

---

## 15. Repository snapshot

| Topic                           | Status                                                     |
| ------------------------------- | ---------------------------------------------------------- |
| Main build posture              | green on touched targets                                   |
| P80/P81 corridor                | green under current zero-map semantics                     |
| Corrected public P91 surface    | direct in multiplicative window                            |
| Legacy P91 route                | deprecated and audited as too weak                         |
| Remaining main-file `sorry`s    | 3, all on deprecated legacy P91 route                      |
| Remaining experimental `sorry`s | 3, non-load-bearing                                        |
| Terminal claim                  | not yet unconditional in the intended final semantic sense |

---

## 16. Reading guide for reviewers

Recommended hostile-review order:

1. `AXIOM_FRONTIER.md`
2. `YangMills/ClayCore/BalabanRG/P91LegacyRouteCounterexample.lean`
3. `YangMills/ClayCore/BalabanRG/P91CorrectedWindowPublicShim.lean`
4. `YangMills/ClayCore/BalabanRG/P91CorrectedWindowConsumerPacket.lean`
5. `YangMills/ClayCore/BalabanRG/RGCauchyP81Interface.lean`
6. `YangMills/ClayCore/BalabanRG/BalabanBlockingMap.lean`
7. `YangMills/P8_PhysicalGap/PhysicalMassGap.lean`
8. `YangMills/L8_Terminal/ClayTheorem.lean`

---

## 17. Signature

Roadmap signature: **March 22, 2026**

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
