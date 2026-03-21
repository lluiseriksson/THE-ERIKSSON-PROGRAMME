# THE ERIKSSON PROGRAMME
Lean 4 formalization for the Yang–Mills mass gap programme

> **Current status:** Formal reduction & interface isolation  
> **Claim level:** This repository does **not** claim a finished Clay solution.  
> **Build health:** 8270+ jobs, 0 errors, 0 `sorry`s  
> **Lean / Mathlib:** Lean `v4.29.0-rc6` + Mathlib  
> **Last updated:** March 2026

---

## 1. What this repository is

The Eriksson Programme is a long-horizon formal verification project in Lean 4.

Its purpose is to formalize an **honest reduction programme** for the Clay Yang–Mills and Mass Gap problem: every bridge is named, every dependency is exposed, and every unresolved ingredient is isolated explicitly rather than hidden behind folklore or informal “standard arguments”.

This repository therefore aims at a **fully verified structural pipeline** in which the terminal theorem `ClayYangMillsTheorem` is connected to explicit formal interfaces. The programme should be considered **finished** only when the remaining terminal interfaces are discharged **inconditionally inside Lean 4**, without external witness packages or transfer assumptions.

---

## 2. Mathematical goal

Formalize a complete proof architecture for the Yang–Mills mass gap in Lean 4:

- construct a non-trivial 4D `SU(N)` quantum Yang–Mills theory,
- satisfy the Osterwalder–Schrader / Wightman interface expected by the Clay formulation,
- prove a positive spectral gap / mass gap,
- and verify every formal step in Lean.

---

## 4. Repository snapshot

| Item | Current state |
|---|---|
| Build health | **8270+ jobs, 0 errors, 0 `sorry`s** |
| Clay core | 1 Clay core axiom |
| Named axioms | 8 |
| BalabanRG status | decomposed into independent targets with concrete discharged subpaths |
| Current bridge status | singleton, finite full, concrete `L¹`, weighted `L¹`, direct-budget, native-target, and final-gap lanes all registered |

---

## 5. Unconditionality audit

| Component | Type | State | Meaning |
|---|---|---:|---|
| P91 finite-full small-constants packaging | Honest reduction | 🟢 | The finite-full constants `A_large`, `A_cauchy` are cleanly isolated |
| Direct-budget lane | Honest reduction | 🟢 | The terminal budget route is packaged |
| Native-target lane | Honest reduction | 🟢 | The native-target route is packaged |
| **SmallConstants -> DirectBudget** | **Real mathematical gap** | 🔴 | Need unconditional proof for global weighted budget |
| **SmallConstants -> NativeTarget** | **Real mathematical gap** | 🔴 | Need unconditional proof reaching native target |

---

## 7. Original work and audit trail

| Resource | Link |
|---|---|
| Papers — The Eriksson Programme (viXra [1]–[68]) | Papers organised as a closure tree |
| Full author page | https://ai.vixra.org/author/lluis_eriksson |
| Repository | https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME |

---


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

## Complete Paper Corpus

**68 publicly timestamped papers** — full list at [ai.vixra.org/author/lluis_eriksson](https://ai.vixra.org/author/lluis_eriksson).  
Date range: December 16 2025 — February 27 2026.  
SHA-256 hashes: [`ym-audit` repo](https://github.com/lluiseriksson/ym-audit).

| # | Date | ai.viXra ID | Title |
|---|------|-------------|-------|
| 1 | — | [2602.0117](https://ai.vixra.org/abs/2602.0117) |  |
| 2 | — | [2602.0096](https://ai.vixra.org/abs/2602.0096) |  |
| 3 | — | [2602.0092](https://ai.vixra.org/abs/2602.0092) |  |
| 4 | — | [2602.0091](https://ai.vixra.org/abs/2602.0091) |  |
| 5 | — | [2602.0089](https://ai.vixra.org/abs/2602.0089) |  |
| 6 | — | [2602.0088](https://ai.vixra.org/abs/2602.0088) |  |
| 7 | — | [2602.0087](https://ai.vixra.org/abs/2602.0087) |  |
| 8 | — | [2602.0085](https://ai.vixra.org/abs/2602.0085) |  |
| 9 | — | [2602.0084](https://ai.vixra.org/abs/2602.0084) |  |
| 10 | — | [2602.0077](https://ai.vixra.org/abs/2602.0077) |  |
| 11 | — | [2602.0073](https://ai.vixra.org/abs/2602.0073) |  |
| 12 | — | [2602.0072](https://ai.vixra.org/abs/2602.0072) |  |
| 13 | — | [2602.0070](https://ai.vixra.org/abs/2602.0070) |  |
| 14 | — | [2602.0069](https://ai.vixra.org/abs/2602.0069) |  |
| 15 | — | [2602.0063](https://ai.vixra.org/abs/2602.0063) |  |
| 16 | — | [2602.0057](https://ai.vixra.org/abs/2602.0057) |  |
| 17 | — | [2602.0056](https://ai.vixra.org/abs/2602.0056) |  |
| 18 | — | [2602.0055](https://ai.vixra.org/abs/2602.0055) |  |
| 19 | — | [2602.0054](https://ai.vixra.org/abs/2602.0054) |  |
| 20 | — | [2602.0053](https://ai.vixra.org/abs/2602.0053) |  |
| 21 | — | [2602.0052](https://ai.vixra.org/abs/2602.0052) |  |
| 22 | — | [2602.0051](https://ai.vixra.org/abs/2602.0051) |  |
| 23 | — | [2602.0046](https://ai.vixra.org/abs/2602.0046) |  |
| 24 | — | [2602.0041](https://ai.vixra.org/abs/2602.0041) |  |
| 25 | — | [2602.0040](https://ai.vixra.org/abs/2602.0040) |  |
| 26 | — | [2602.0038](https://ai.vixra.org/abs/2602.0038) |  |
| 27 | — | [2602.0036](https://ai.vixra.org/abs/2602.0036) |  |
| 28 | — | [2602.0035](https://ai.vixra.org/abs/2602.0035) |  |
| 29 | — | [2602.0033](https://ai.vixra.org/abs/2602.0033) |  |
| 30 | — | [2602.0032](https://ai.vixra.org/abs/2602.0032) |  |
| 31 | — | [2602.0021](https://ai.vixra.org/abs/2602.0021) |  |
| 32 | — | [2602.0020](https://ai.vixra.org/abs/2602.0020) |  |
| 33 | — | [2601.0115](https://ai.vixra.org/abs/2601.0115) |  |
| 34 | — | [2601.0111](https://ai.vixra.org/abs/2601.0111) |  |
| 35 | — | [2601.0099](https://ai.vixra.org/abs/2601.0099) |  |
| 36 | — | [2601.0066](https://ai.vixra.org/abs/2601.0066) |  |
| 37 | — | [2601.0065](https://ai.vixra.org/abs/2601.0065) |  |
| 38 | — | [2601.0064](https://ai.vixra.org/abs/2601.0064) |  |
| 39 | — | [2601.0051](https://ai.vixra.org/abs/2601.0051) |  |
| 40 | — | [2601.0050](https://ai.vixra.org/abs/2601.0050) |  |
| 41 | — | [2601.0047](https://ai.vixra.org/abs/2601.0047) |  |
| 42 | — | [2601.0046](https://ai.vixra.org/abs/2601.0046) |  |
| 43 | — | [2601.0044](https://ai.vixra.org/abs/2601.0044) |  |
| 44 | — | [2601.0043](https://ai.vixra.org/abs/2601.0043) |  |
| 45 | — | [2601.0042](https://ai.vixra.org/abs/2601.0042) |  |
| 46 | — | [2601.0040](https://ai.vixra.org/abs/2601.0040) |  |
| 47 | — | [2601.0038](https://ai.vixra.org/abs/2601.0038) |  |
| 48 | — | [2601.0035](https://ai.vixra.org/abs/2601.0035) |  |
| 49 | — | [2601.0034](https://ai.vixra.org/abs/2601.0034) |  |
| 50 | — | [2601.0031](https://ai.vixra.org/abs/2601.0031) |  |
| 51 | — | [2601.0023](https://ai.vixra.org/abs/2601.0023) |  |
| 52 | — | [2601.0022](https://ai.vixra.org/abs/2601.0022) |  |
| 53 | — | [2601.0020](https://ai.vixra.org/abs/2601.0020) |  |
| 54 | — | [2601.0007](https://ai.vixra.org/abs/2601.0007) |  |
| 55 | — | [2512.0105](https://ai.vixra.org/abs/2512.0105) |  |
| 56 | — | [2512.0102](https://ai.vixra.org/abs/2512.0102) |  |
| 57 | — | [2512.0101](https://ai.vixra.org/abs/2512.0101) |  |
| 58 | — | [2512.0091](https://ai.vixra.org/abs/2512.0091) |  |
| 59 | — | [2512.0085](https://ai.vixra.org/abs/2512.0085) |  |
| 60 | — | [2512.0084](https://ai.vixra.org/abs/2512.0084) |  |
| 61 | — | [2512.0081](https://ai.vixra.org/abs/2512.0081) |  |
| 62 | — | [2512.0073](https://ai.vixra.org/abs/2512.0073) |  |
| 63 | — | [2512.0072](https://ai.vixra.org/abs/2512.0072) |  |
| 64 | — | [2512.0071](https://ai.vixra.org/abs/2512.0071) |  |
| 65 | — | [2512.0070](https://ai.vixra.org/abs/2512.0070) |  |
| 66 | — | [2512.0064](https://ai.vixra.org/abs/2512.0064) |  |
| 67 | — | [2512.0061](https://ai.vixra.org/abs/2512.0061) |  |
| 68 | — | [2512.0060](https://ai.vixra.org/abs/2512.0060) |  |
