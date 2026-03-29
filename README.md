# THE ERIKSSON PROGRAMME

**Lean 4 formalization of the Yang–Mills mass gap programme**

[![License: AGPL v3](https://img.shields.io/badge/License-AGPL_v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)
[![Lean 4](https://img.shields.io/badge/Lean-4-orange)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-green)](https://leanprover-community.github.io/mathlib4_docs/)

> **Current milestone (2026-03-29, post-audit D1–D8):** `BalabanRGUniformLSILiveTarget` and
> `HaarLSIFrontierPackage` are unconditionally closed at the packaging layer.
> 0 `sorry` in the main proof pipeline; all gaps are explicit named `axiom`.
> 2 documented `sorry` remain in `Experimental/Semigroup/` (scratch files, non-blocking).
> Remaining honest mathematical gaps documented in `AXIOM_FRONTIER.md`.

---

## Project Overview

The Eriksson Programme is a systematic, machine-verified attempt to formalize the proof
strategy for the Yang–Mills existence and mass gap problem — one of the seven Clay
Millennium Prize Problems — using the **Lean 4** interactive theorem prover with the
**Mathlib4** mathematical library.

The programme does **not** claim to have solved the Clay problem. Instead it:

1. Formalizes the mathematical infrastructure (gauge groups, connections, curvature, Haar
   measure, Logarithmic Sobolev Inequalities, spectral theory) in a machine-checkable
   language.
2. Tracks the honest boundary between what is verified and what remains open, using
   explicit `axiom` declarations (never silent `sorry`) for every unproven gap.
3. Implements a Balaban renormalization group programme following the construction of
   Balaban (1982–1989), adapted to the rigorous functional-analytic framework of
   Glimm–Jaffe and Seiler.

### The Clay Problem (informal statement)

Prove the existence of a quantum Yang–Mills gauge theory on ℝ⁴ with compact simple gauge
group G (e.g. SU(N)), satisfying the Wightman / Osterwalder–Schrader axioms, such that
the theory has a **mass gap** Δ > 0:

    inf(spec(H_YM) \ {E₀}) ≥ Δ > 0

where H_YM is the quantum Hamiltonian and E₀ is the vacuum energy.

---

## Reference Papers

The following 68 preprints by Lluis Eriksson constitute the companion-paper programme
underlying this formalisation. All are freely available at
[viXra.org](https://vixra.org) under Mathematical Physics and Quantum Physics.

---

[1] Lluis Eriksson. *Clustering, Recovery, and Locality in Algebraic Quantum Field Theory: Quantitative Bounds via Split Inclusions and Modular Theory.* viXra:2512.0060 (Dec 2025). <https://vixra.org/abs/2512.0060>

[2] Lluis Eriksson. *The Conditional Maintenance Work Theorem: Operational Power Lower Bounds from Energy Pinching and a Split-Inclusion Blueprint for Type III AQFT.* viXra:2512.0061 (Dec 2025). <https://vixra.org/abs/2512.0061>

[3] Lluis Eriksson. *The Heisenberg Cut as a Resource Boundary: An Operational Outlook from Coherence Maintenance Costs.* viXra:2512.0064 (Dec 2025). <https://vixra.org/abs/2512.0064>

[4] Lluis Eriksson. *Stress Testing the Rate Inheritance Principle: Spectral Decoherence Rates and an Operational Resource Horizon.* viXra:2512.0070 (Dec 2025). <https://vixra.org/abs/2512.0070>

[5] Lluis Eriksson. *Operational Coherence Maintenance: Proven Results, Conditional Interfaces, and Open Dynamical Gaps.* viXra:2512.0071 (Dec 2025). <https://vixra.org/abs/2512.0071>

[6] Lluis Eriksson. *The Rate Inheritance Principle: From Static Correlations to Dynamical Decoherence Rates.* viXra:2512.0072 (Dec 2025). <https://vixra.org/abs/2512.0072>

[7] Lluis Eriksson. *Finite-Dimensional Davies Interface Lemmas and TFIM Witness Tests for the Heisenberg Cut as a Resource Boundary.* viXra:2512.0073 (Dec 2025). <https://vixra.org/abs/2512.0073>

[8] Lluis Eriksson. *Operational Coherence Maintenance and the Quantum-Classical Boundary: Formal Definitions, Falsifiable Protocols, and an Outlook for Cognitive Systems.* viXra:2512.0081 (Dec 2025). <https://vixra.org/abs/2512.0081>

[9] Lluis Eriksson. *The Maintenance Constraint: How Resource Boundaries Shape Cognitive Availability.* viXra:2512.0084 (Dec 2025). <https://vixra.org/abs/2512.0084>

[10] Lluis Eriksson. *Geometry, Membranes, and Life as a Resource Boundary: A Correct-by-Construction Operational Pipeline from Static Suppression to Maintenance Costs.* viXra:2512.0085 (Dec 2025). <https://vixra.org/abs/2512.0085>

[11] Lluis Eriksson. *Technical Appendix: Heat Kernel, Fermions, and the Sign of Induced Gravity (Sign Conventions Fixed; Laplacian/Lichnerowicz Hinge Made Explicit).* viXra:2512.0091 (Dec 2025). <https://vixra.org/abs/2512.0091>

[12] Lluis Eriksson. *Beyond Gaussianity: Extending the Clustering-Recovery Bridge.* viXra:2512.0101 (Dec 2025). <https://vixra.org/abs/2512.0101>

[13] Lluis Eriksson. *Heat Kernel Methods and the Sign of Induced Gravity: Resolving Conventions via the Laplacian-Lichnerowicz Identity.* viXra:2512.0102 (Dec 2025). <https://vixra.org/abs/2512.0102>

[14] Lluis Eriksson. *Prefix-Path Bell Transport on IBM Quantum Hardware: High-Resolution Replication, Comparative Geometry Dependence, and Stress Tests of a Static-Dynamic Link.* viXra:2512.0105 (Dec 2025). <https://vixra.org/abs/2512.0105>

[15] Lluis Eriksson. *Quantitative Recovery Bounds from Vacuum Clustering in Finite-Mode Gaussian States (A Regularized CCR Blueprint Motivated by Split Inclusions).* viXra:2601.0007 (Jan 2026). <https://vixra.org/abs/2601.0007>

[16] Lluis Eriksson. *Geometric Markov Bounds and Rate Inheritance Modulo Fixed Points: A Scalar Entropic Interface from Static Locality to Davies Dynamics.* viXra:2601.0020 (Jan 2026). <https://vixra.org/abs/2601.0020>

[17] Lluis Eriksson. *The Rate Inheritance Principle: Operational Decoherence-Rate Envelopes and Stress Tests in Gapped Lattice Surrogates.* viXra:2601.0022 (Jan 2026). <https://vixra.org/abs/2601.0022>

[18] Lluis Eriksson. *Finite-Dimensional Davies Interface Lemmas and TFIM Witness Tests for Separation-Dependent Decoherence Rate Envelopes.* viXra:2601.0023 (Jan 2026). <https://vixra.org/abs/2601.0023>

[19] Lluis Eriksson. *From Static Recoverability to Maintenance Power: A Typed Pipeline with omega=0 Obstructions.* viXra:2601.0031 (Jan 2026). <https://vixra.org/abs/2601.0031>

[20] Lluis Eriksson. *Modular Recovery from Split Inclusions: B-Minimal Bridge from QFT Collar Geometry to Approximate State Reconstruction.* viXra:2601.0034 (Jan 2026). <https://vixra.org/abs/2601.0034>

[21] Lluis Eriksson. *A Non-Gaussian Clustering-Recovery Bridge via Conditional Mutual Information.* viXra:2601.0035 (Jan 2026). <https://vixra.org/abs/2601.0035>

[22] Lluis Eriksson. *Operational Signatures of Criticality from Petz Recovery: Collar-Length Requirements in TFIM Exact Diagonalization.* viXra:2601.0038 (Jan 2026). <https://vixra.org/abs/2601.0038>

[23] Lluis Eriksson. *Finite-Size Scaling of Petz Recovery Length in the TFIM: Threshold-Dependent Operational Exponents from Exact Diagonalization.* viXra:2601.0040 (Jan 2026). <https://vixra.org/abs/2601.0040>

[24] Lluis Eriksson. *Emergent Information Distance from Petz Recovery: Temperature and Perturbation Dependence in TFIM Exact Diagonalization.* viXra:2601.0042 (Jan 2026). <https://vixra.org/abs/2601.0042>

[25] Lluis Eriksson. *Recoverability Geometry: Distances and Embeddings from Quantum Markov Data.* viXra:2601.0043 (Jan 2026). <https://vixra.org/abs/2601.0043>

[26] Lluis Eriksson. *Recoverability Length Scales and Wilson Loops in Lattice Gauge Theories: Protocol, Definitions, and Conjectural Links to Confinement Diagnostics.* viXra:2601.0044 (Jan 2026). <https://vixra.org/abs/2601.0044>

[27] Lluis Eriksson. *Petz Recoverability in AQFT Via Conditional Expectations: A Framework and a Conditional Exponential Recovery Bound.* viXra:2601.0046 (Jan 2026). <https://vixra.org/abs/2601.0046>

[28] Lluis Eriksson. *Petz Recoverability Versus Wilson-Loop Diagnostics in Z2 Lattice Gauge Theory (2+1D).* viXra:2601.0047 (Jan 2026). <https://vixra.org/abs/2601.0047>

[29] Lluis Eriksson. *CMI-Based Recoverability Versus Wilson-Loop Diagnostics in Z2 Lattice Gauge Theory (2+1D): Exact Diagonalization Benchmark on Small Open Lattices.* viXra:2601.0050 (Jan 2026). <https://vixra.org/abs/2601.0050>

[30] Lluis Eriksson. *Petz Recoverability Versus Wilson-Loop Diagnostics in Z2 Lattice Gauge Theory (2+1D): Benchmarks by Exact Diagonalization and Tensor-Network Ladders.* viXra:2601.0051 (Jan 2026). <https://vixra.org/abs/2601.0051>

[31] Lluis Eriksson. *RIP-U and the omega=0 Obstruction in Davies Dynamics: Upper Envelopes, Witness Floor, and Falsification Protocols for Separation-Dependent Decoherence Rates.* viXra:2601.0064 (Jan 2026). <https://vixra.org/abs/2601.0064>

[32] Lluis Eriksson. *Split-Regularized Recoverability in Type III AQFT: Conditional Expectations, Split-Dependent CMI, and an Audit-Friendly Contract.* viXra:2601.0065 (Jan 2026). <https://vixra.org/abs/2601.0065>

[33] Lluis Eriksson. *Typed Pipeline for Recoverability-Rate-Power Links: A Contract Paper with a Closed Recoverability Lane and Falsification Criteria.* viXra:2601.0066 (Jan 2026). <https://vixra.org/abs/2601.0066>

[34] Lluis Eriksson. *Program A: Semi-Infinite Conditional Mutual Information in the 1D Transverse-Field Ising Model (iMPS).* viXra:2601.0099 (Jan 2026). <https://vixra.org/abs/2601.0099>

[35] Lluis Eriksson. *Conditional Mutual Information and Petz Recovery in a Z_2 Lattice Gauge Ground State.* viXra:2601.0111 (Jan 2026). <https://vixra.org/abs/2601.0111>

[36] Lluis Eriksson. *Algebraic Entropy and Conditional Mutual Information in a Tiny Gauge-Invariant Truncated Hilbert Space: A Reproducible Toy-Model Study with Effective Mixing Hamiltonians.* viXra:2601.0115 (Jan 2026). <https://vixra.org/abs/2601.0115>

[37] Lluis Eriksson. *Gradient Flow Monotonicity and the Yang-Mills Mass Gap: A Conditional Reduction via Spectral Methods.* viXra:2602.0020 (Feb 2026). <https://vixra.org/abs/2602.0020>

[38] Lluis Eriksson. *Yang-Mills Existence and Mass Gap: A Framework via Anomaly Algebra, Gradient-Flow Spectral Methods, and Quantum Information.* viXra:2602.0021 (Feb 2026). <https://vixra.org/abs/2602.0021>

[39] Lluis Eriksson. *The Yang-Mills Mass Gap on the Lattice: A Self-Contained Proof Via Witten Laplacian and Constructive Renormalization.* viXra:2602.0032 (Feb 2026). <https://vixra.org/abs/2602.0032>

[40] Lluis Eriksson. *The Yang-Mills Mass Gap on the Lattice: A Self-Contained Proof.* viXra:2602.0033 (Feb 2026). <https://vixra.org/abs/2602.0033>

[41] Lluis Eriksson. *Morse-Bott Spectral Reduction and the Yang-Mills Mass Gap on the Lattice.* viXra:2602.0035 (Feb 2026). <https://vixra.org/abs/2602.0035>

[42] Lluis Eriksson. *Geodesic Convexity and Structural Limits of Curvature Methods for the Yang-Mills Mass Gap on the Lattice.* viXra:2602.0036 (Feb 2026). <https://vixra.org/abs/2602.0036>

[43] Lluis Eriksson. *Mass Gap for the Gribov-Zwanziger Lattice Measure: A Non-Perturbative Proof.* viXra:2602.0038 (Feb 2026). <https://vixra.org/abs/2602.0038>

[44] Lluis Eriksson. *Uniform Poincare Inequality for Lattice Yang-Mills Theory Via Multiscale Martingale Decomposition.* viXra:2602.0040 (Feb 2026). <https://vixra.org/abs/2602.0040>

[45] Lluis Eriksson. *Uniform Log-Sobolev Inequality and Mass Gap for Lattice Yang-Mills Theory.* viXra:2602.0041 (Feb 2026). <https://vixra.org/abs/2602.0041>

[46] Lluis Eriksson. *Ricci Curvature of the Orbit Space of Lattice Gauge Theory and Single-Scale Log-Sobolev Inequalities.* viXra:2602.0046 (Feb 2026). <https://vixra.org/abs/2602.0046>

[47] Lluis Eriksson. *Uniform Coercivity, Pointwise Large-Field Suppression, and Unconditional Closure of the Lattice Yang-Mills Mass Gap at Weak Coupling in d=4.* viXra:2602.0051 (Feb 2026). <https://vixra.org/abs/2602.0051>

[48] Lluis Eriksson. *Interface Lemmas for the Multiscale Proof of the Lattice Yang-Mills Mass Gap.* viXra:2602.0052 (Feb 2026). <https://vixra.org/abs/2602.0052>

[49] Lluis Eriksson. *DLR-Uniform Log-Sobolev Inequality and Unconditional Mass Gap for Lattice Yang-Mills at Weak Coupling.* viXra:2602.0053 (Feb 2026). <https://vixra.org/abs/2602.0053>

[50] Lluis Eriksson. *From Uniform Log-Sobolev Inequality to Mass Gap for Lattice Yang-Mills at Weak Coupling.* viXra:2602.0054 (Feb 2026). <https://vixra.org/abs/2602.0054>

[51] Lluis Eriksson. *Unconditional Uniform Log-Sobolev Inequality for SU(N) Lattice Yang-Mills at Weak Coupling.* viXra:2602.0055 (Feb 2026). <https://vixra.org/abs/2602.0055>

[52] Lluis Eriksson. *Large-Field Suppression for Lattice Gauge Theories: From Balaban Renormalization Group to Conditional Concentration.* viXra:2602.0056 (Feb 2026). <https://vixra.org/abs/2602.0056>

[53] Lluis Eriksson. *Integrated Cross-Scale Derivative Bounds for Wilson Lattice Gauge Theory: Closing the Log-Sobolev Gap.* viXra:2602.0057 (Feb 2026). <https://vixra.org/abs/2602.0057>

[54] Lluis Eriksson. *Conditional Continuum Limit of 4d SU(N) Yang-Mills Theory via Two-Layer Architecture, RG-Cauchy Uniqueness, and Step-Scaling Confinement.* viXra:2602.0063 (Feb 2026). <https://vixra.org/abs/2602.0063>

[55] Lluis Eriksson. *The Balaban-Dimock Structural Package: Derivation of Polymer Representation, Oscillation Bounds, and Large-Field Suppression for Lattice Yang-Mills Theory from Primary Sources.* viXra:2602.0069 (Feb 2026). <https://vixra.org/abs/2602.0069>

[56] Lluis Eriksson. *Doob Influence Bounds for Polymer Remainders in 4D Lattice Yang-Mills Renormalization.* viXra:2602.0070 (Feb 2026). <https://vixra.org/abs/2602.0070>

[57] Lluis Eriksson. *Influence Bounds for Polymer Remainders in Balaban Renormalization Group: Closing Assumption (B6) for the RG-Cauchy Programme in 4D Lattice Yang-Mills.* viXra:2602.0072 (Feb 2026). <https://vixra.org/abs/2602.0072>

[58] Lluis Eriksson. *RG-Cauchy Summability for Blocked Observables in 4d Lattice Yang-Mills Theory via Balaban Renormalization Group.* viXra:2602.0073 (Feb 2026). <https://vixra.org/abs/2602.0073>

[59] Lluis Eriksson. *Ultraviolet Stability for Four-Dimensional Lattice Yang-Mills Theory Under a Quantitative Blocking Hypothesis.* viXra:2602.0077 (Feb 2026). <https://vixra.org/abs/2602.0077>

[60] Lluis Eriksson. *Almost Reflection Positivity for Gradient-Flow Observables via Gaussian Localization in Lattice Yang-Mills Theory.* viXra:2602.0084 (Feb 2026). <https://vixra.org/abs/2602.0084>

[61] Lluis Eriksson. *Ultraviolet Stability of Wilson-Loop Expectations in 4D Lattice Yang-Mills Theory Via Multiscale Gradient-Flow Smoothing.* viXra:2602.0085 (Feb 2026). <https://vixra.org/abs/2602.0085>

[62] Lluis Eriksson. *Irrelevant Operators, Anisotropy Bounds, and Operator Insertions in Balaban Renormalization Group for Four-Dimensional SU(N) Lattice Yang-Mills Theory.* viXra:2602.0087 (Feb 2026). <https://vixra.org/abs/2602.0087>

[63] Lluis Eriksson. *Exponential Clustering and Mass Gap for Four-Dimensional SU(N) Lattice Yang-Mills Theory Via Balaban Renormalization Group and Multiscale Correlator Decoupling.* viXra:2602.0088 (Feb 2026). <https://vixra.org/abs/2602.0088>

[64] Lluis Eriksson. *Spectral Gap and Thermodynamic Limit for SU(N) Lattice Yang-Mills Theory via Log-Sobolev Inequalities and Complete Analyticity.* viXra:2602.0089 (Feb 2026). <https://vixra.org/abs/2602.0089>

[65] Lluis Eriksson. *Closing the Last Gap in the 4D SU(N) Yang-Mills Construction: A Verified Terminal KP Bound and an Explicit Clay Checklist.* viXra:2602.0091 (Feb 2026). <https://vixra.org/abs/2602.0091>

[66] Lluis Eriksson. *Rotational Symmetry Restoration and the Wightman Axioms for Four-Dimensional SU(N) Yang-Mills Theory.* viXra:2602.0092 (Feb 2026). <https://vixra.org/abs/2602.0092>

[67] Lluis Eriksson. *The Master Map: An Audit-First, Attack-Resistant Navigation Guide to the Unconditional Solution of the 4D SU(N) Yang-Mills Existence and Mass Gap Problem.* viXra:2602.0096 (Feb 2026). <https://vixra.org/abs/2602.0096>

[68] Lluis Eriksson. *Mechanical Audit Experiments and Reproducibility Appendix for a Companion-Paper Programme on 4D SU(N) Yang-Mills Existence and Mass Gap.* viXra:2602.0117 (Feb 2026). <https://vixra.org/abs/2602.0117>

---

*All papers are self-archived by the author on [viXra.org](https://vixra.org) and freely accessible.*

## Repository Structure

```
THE-ERIKSSON-PROGRAMME/
├── lakefile.lean              # Lake build file (auto-discovers YangMills/)
├── lake-manifest.json         # Pinned Mathlib4 commit
├── README.md                  # This file
├── AXIOM_FRONTIER.md          # Open axioms + sorry census (authoritative, census 2026-03-29)
├── Colab_Agente_YangMills.py  # Python agent for automated iteration
│
└── YangMills/
    ├── Foundations/
    │   ├── GaugeGroup.lean         # Compact Lie group typeclass, Haar measure
    │   ├── PrincipalBundle.lean    # Principal G-bundles, gauge transformations
    │   ├── Connection.lean         # Connections, gauge action
    │   └── CurvatureTensor.lean    # Curvature 2-form, Bianchi identity
    │
    ├── ClayCore/
    │   ├── YangMillsFunctional.lean  # Yang-Mills action S_YM = ∫‖F_A‖²
    │   ├── YangMillsEquations.lean   # Euler-Lagrange: D_A ★F_A = 0
    │   ├── GaugeInvariance.lean      # Gauge invariance of S_YM
    │   ├── MassGapStatement.lean     # Formal mass gap statement
    │   │
    │   └── BalabanRG/               # Balaban RG programme (~280 files)
    │       ├── BalabanRGPackage.lean
    │       ├── BalabanRGPackageWitness.lean
    │       ├── HaarLSITransferWitness.lean
    │       ├── HaarLSIDirectBridge.lean
    │       └── [~270 additional modules]
    │
    ├── P8_PhysicalGap/              # Physical mass gap programme (20 files)
    │   ├── BalabanToLSI.lean        # M1: Haar-LSI via Bakry-Émery
    │   │                            # M2: RG → uniform DLR-LSI
    │   │                            # Assembly: sun_gibbs_dlr_lsi (theorem)
    │   ├── LSIDefinitions.lean      # LogSobolevInequality, DLR_LSI, ExponentialClustering
    │   ├── SUN_StateConstruction.lean  # Concrete SU(N) state space
    │   ├── SUN_DirichletCore.lean   # SU(N) Dirichlet form
    │   ├── StroockZegarlinski.lean  # sz_lsi_to_clustering (proved theorem here)
    │   ├── MarkovSemigroupDef.lean  # hille_yosida_semigroup axiom
    │   ├── PhysicalMassGap.lean     # ClayYangMillsTheorem
    │   └── [13 additional P8 modules]
    │
    └── Experimental/LieSUN/        # Concrete Lie derivative formalization (8 files)
        ├── LieDerivReg_v4.lean      # Lie derivative regularity (main import)
        └── [7 additional LieSUN modules]
```

---

## Proving Unconditionality

### Philosophy: `axiom` over `sorry`

The project enforces a strict discipline: every unproven gap is declared as an explicit
named `axiom`, never left as a silent `sorry`. This means:

- `lake build` passes with 0 errors, 0 `sorry`
- The full dependency graph of every theorem is machine-checkable
- Any reader can audit exactly which mathematical claims are assumed

The complete, verified axiom list is in `AXIOM_FRONTIER.md`. A census of
`YangMills/P8_PhysicalGap/` and `YangMills/Experimental/LieSUN/` (28 files) was
conducted on 2026-03-29 and found **18 unique axiom names**.

### Current Axiom Inventory (summary — see `AXIOM_FRONTIER.md` for full list)

**Clay-core axioms** (genuine mathematical content, not yet formalized):

| Axiom | File | Mathematical Content |
|---|---|---|
| `sun_bakry_emery_cd` | `BalabanToLSI.lean` | SU(N) satisfies Bakry-Émery CD(N/4, ∞) |
| `balaban_rg_uniform_lsi` | `BalabanToLSI.lean` | RG promotes per-site Haar-LSI to uniform DLR-LSI |
| `sun_lieb_robinson_bound` | `SUN_LiebRobin.lean` | Lieb-Robinson bound for SU(N) lattice observables |
| `sz_lsi_to_clustering` | `BalabanToLSI.lean` | Uniform DLR-LSI → exponential clustering (abstract interface; concrete proof in `StroockZegarlinski.lean` not yet connected) |

**Selected Mathlib-gap axioms** (formalization infrastructure, not Clay-specific):

| Axiom | File | Content |
|---|---|---|
| `bakry_emery_lsi` | `BalabanToLSI.lean` | Bakry-Émery criterion implies LSI |
| `instIsTopologicalGroupSUN` | `SUN_StateConstruction.lean` | `IsTopologicalGroup` for `Matrix.specialUnitaryGroup` |
| `sunDirichletForm_contraction` | `SUN_DirichletCore.lean` | Beurling-Deny normal contraction |
| `hille_yosida_semigroup` | `MarkovSemigroupDef.lean` | Hille-Yosida: Dirichlet form → Markov semigroup |
| `instIsProbabilityMeasure_sunHaarProb` | `BalabanToLSI.lean` | Haar measure on abstract SU(N) state is a probability measure |

See `AXIOM_FRONTIER.md` for the remaining 9 Mathlib-gap axioms, structural issues
(duplicate declarations, name-clash between abstract and concrete `sz_lsi_to_clustering`),
and the discharge roadmap.

### The Direct Bridge Architecture

The proof architecture follows a four-layer funnel:

```
Layer 1 (Clay-physics):
    sun_bakry_emery_cd + bakry_emery_lsi
    ↓ sun_haar_lsi (Haar-LSI for SU(N))
    ↓ balaban_rg_uniform_lsi

Layer 2 (RG):
    sun_gibbs_dlr_lsi  ← proved theorem (BalabanToLSI.lean)
    ↓ sz_lsi_to_clustering  ← axiom (abstract); theorem proved separately in StroockZegarlinski.lean

Layer 3 (spectral):
    sun_gibbs_clustering  ← proved theorem
    ↓ clustering_to_spectralGap  ← proved theorem (StroockZegarlinski.lean)

Layer 4 (mass gap):
    ClayYangMillsTheorem (∃ m_phys > 0)
```

The packaging layer (BalabanRG modules) has been fully closed:
`BalabanRGUniformLSILiveTarget` and `HaarLSIFrontierPackage` compile at the
**packaging layer** (0 sorry, 0 errors, conditional on named `axiom` declarations
registered in `AXIOM_FRONTIER.md`). They are **not** unconditional mathematical proofs.

---

## Workflow Automation

### `Colab_Agente_YangMills.py`

An automated Python agent that runs in Google Colab and iterates on the Lean 4 proof
frontier. The agent:

1. Clones / pulls the repository
2. Counts remaining `sorry` placeholders (target: always 0)
3. Identifies the primary compilation target (`HaarLSIDirectBridge.lean`)
4. Calls an LLM (Claude Opus or GPT-4o via OpenRouter) with the full file content as context
5. Extracts the Lean 4 code from the response and writes it to the file
6. Runs `lake build` to check for errors
7. If errors: reverts the file and retries (up to `MAX_ITERATIONS = 10`)
8. Commits and pushes successful changes

**Required secrets** (set in Colab notebook secrets):
- `GITHUB_TOKEN` — personal access token with repo write access
- `OPENROUTER_API_KEY` — OpenRouter API key for LLM access

**Configuration:**
```python
MODEL = "anthropic/claude-opus-4"  # LLM model
MAX_ITERATIONS = 10                # Retry budget
LLM_TEMPERATURE = 0.1              # Low temperature for precision
TARGET_MODULE = "YangMills.ClayCore.BalabanRG.HaarLSIDirectBridge"
```

---

## Current State & Progress

### Build Status

| Scope | Status |
|---|---|
| Local full `lake build` | 0 errors · 0 sorry (last verified locally) |
| CI (`lake build YangMills.P8_PhysicalGap.BalabanToLSI`) | Checked in GitHub Actions on every push to main |

> **CI scope note**: The GitHub Actions workflow runs `lake build YangMills.P8_PhysicalGap.BalabanToLSI`
> (the narrow Phase 2 target), not a full `lake build` of all ~280 BalabanRG modules.
> A full build exceeds GitHub Actions free-tier time limits.
> The `scripts/check_consistency.py` script (which correctly handles comments) confirms
> zero `sorry` in both `YangMills/` and `Lean/` directories on every CI run.

### Milestone History

| Date | Milestone |
|---|---|
| 2026-03-28 | **Packaging layer**: `HaarLSIFrontierPackage` compiles (conditional on named axioms) |
| 2026-03-28 | **Axiom 5**: 4 P91 BalabanRG files fully verified |
| 2026-03-28 | **Axiom 4**: 16 BalabanRG modules compiled clean |
| 2026-03-28 | **Axiom 3**: `BalabanRGUniformLSIEquivalenceRegistry` clean |
| 2026-03-28 | **Axiom 2**: `HaarLSIDirectBridge` fully abstract |

### Open Frontier

The live mathematical obstructions are documented in `AXIOM_FRONTIER.md`.
The genuine Clay-problem content is isolated in three Clay-core axioms:
`sun_bakry_emery_cd`, `balaban_rg_uniform_lsi`, `sun_lieb_robinson_bound`.

---

## Building & Usage

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (tested with the Mathlib4 toolchain)
- [Lake](https://github.com/leanprover/lake) (bundled with Lean 4)
- ~8–16 GB RAM for a full local `lake build`

### Build Instructions

```bash
# Clone the repository
git clone https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git
cd THE-ERIKSSON-PROGRAMME

# Download the pre-built Mathlib4 cache (strongly recommended)
lake exe cache get

# Build the full project
lake build
# Expected output: 0 errors, 0 sorry
```

### Checking a Specific File

```bash
# Check a single module (faster than full build)
lean --run YangMills/ClayCore/BalabanRG/BalabanRGPackageWitness.lean

# Or via lake
lake build YangMills.ClayCore.BalabanRG.BalabanRGPackageWitness
```

### Searching for Axioms

```bash
# List all axioms in the project — catches indented AND attributed axioms:
grep -rn "^\s*axiom " YangMills/ --include="*.lean" | grep -v "^\s*--"

# Also check for @[instance] axiom and similar attributed declarations:
grep -rn "\baxiom\b" YangMills/ --include="*.lean" | grep -v "^\s*--"

# Confirm zero sorry (use the Python script — handles comments correctly):
python scripts/check_consistency.py
# The script correctly distinguishes `sorry` in code from `sorry` in comments.
# Do NOT use: grep -r "sorry" ... | grep -v "^\s*--"
# (that grep pipeline is broken: grep -rn output starts with file paths,
#  so the second grep -v "^\s*--" never matches and commented sorry is counted.)
```

---

## License

Copyright (C) 2024–2026 Lluís Eriksson

This program is free software: you can redistribute it and/or modify it under the terms
of the **GNU Affero General Public License** as published by the Free Software Foundation,
either version 3 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
See the [GNU Affero General Public License](https://www.gnu.org/licenses/agpl-3.0) for
more details.

SPDX-License-Identifier: AGPL-3.0-or-later
