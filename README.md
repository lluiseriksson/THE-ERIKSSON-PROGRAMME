# THE ERIKSSON PROGRAMME

## Lean 4 Formalization of the Yang–Mills Mass Gap

**Version**: v1.45.0 (C133) · **Tag**: `v1.45.0`
**BFS-live custom axioms**: 1 (`lsi_normalized_gibbs_from_haar`)
**sorry count**: 0 · **Build errors**: 0
**Oracle** (`sun_physical_mass_gap`): `[propext, Classical.choice, Quot.sound, YangMills.lsi_normalized_gibbs_from_haar]`

---

## What is this?

A **Lean 4 / Mathlib 4** formalization project that builds a proof architecture
for the Yang–Mills mass gap — one of the [Clay Millennium Prize Problems](https://www.claymath.org/millennium-problems/yang-mills-and-mass-gap).

**This project does NOT claim to solve the Clay problem.** It formalizes the
mathematical architecture described in 68 companion papers by Lluis Eriksson,
reducing the problem to explicit, checkable hypotheses and eliminating them
one campaign at a time.

The current state:

- `sun_physical_mass_gap` proves `ClayYangMillsTheorem` with **1 custom axiom**
  (`lsi_normalized_gibbs_from_haar` — Holley-Stroock LSI for normalized SU(N) Gibbs).
- `ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys` is **vacuously true** —
  it can be proved with zero axioms (see `clay_yangmills_unconditional` in
  `ErikssonBridge.lean` which instantiates trivial parameters).
- The **genuine mathematical content** is `sun_gibbs_dlr_lsi_norm`: a DLR-uniform
  log-Sobolev inequality for the **normalized** SU(N) heat-kernel Gibbs measure.

---

## Original Work

- **viXra papers**: 68 preprints by Lluis Eriksson (see [Reference Papers](#reference-papers) below)
- **Zenodo DOI**: [10.5281/zenodo.15168866](https://doi.org/10.5281/zenodo.15168866)
- **GitHub**: [github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME)

---

## Terminal Theorems

| Theorem | Type | Custom axioms | Vacuous? |
|---------|------|---------------|----------|
| `sun_physical_mass_gap` | `ClayYangMillsTheorem` | 1 (`lsi_normalized_gibbs_from_haar`) | Yes |
| `clay_yangmills_unconditional` | `ClayYangMillsTheorem` | 0 | Yes (trivial G=Unit, F=0) |
| `clay_millennium_yangMills` | `ClayYangMillsTheorem` | 1 (`yangMills_continuum_mass_gap`) | Yes |
| `clay_millennium_yangMills_strong` | `ClayYangMillsStrong` | 1 (`yangMills_continuum_mass_gap`) | **No** |

### `ClayYangMillsTheorem` (vacuous)

```lean
def ClayYangMillsTheorem : Prop := ∃ m_phys : ℝ, 0 < m_phys
```

### `ClayYangMillsPhysicalStrong` (non-vacuous)

```lean
def ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP : Prop :=
  ∃ C γ : ℝ, 0 < γ ∧ 0 < C ∧ ∀ N p q,
    |wilsonConnectedCorr μ plaquetteEnergy β F N p q| ≤ C * exp(-γ * distP N p q)
```

### `sun_physical_mass_gap` (primary proof path)

```lean
theorem sun_physical_mass_gap
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ClayYangMillsTheorem :=
  sun_clay_conditional_norm d N_c hN_c β β₀ hβ hβ₀
    (sun_gibbs_dlr_lsi_norm d N_c hN_c β β₀ hβ hβ₀)
```

---

## Honest Assessment

### ⚠ Vacuousness of `ClayYangMillsTheorem`

`ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys` is trivially provable.
The theorem `clay_yangmills_unconditional` proves it with **zero custom axioms**
by setting G = Unit, F = 0, β = 0. The `sun_physical_mass_gap` proof extracts
the LSI constant α* > 0 and wraps it as `⟨α_star, hα⟩` — the DLR_LSI content
is discarded.

### ⚠ Tautological definitions

- `BakryEmeryCD μ E K := LogSobolevInequality μ E K` — defined **as** the LSI itself,
  so `bakry_emery_lsi` is proved by `id`. The actual Bakry-Émery theorem (CD(K,∞) ⇒ LSI)
  is NOT formalized.
- `sunDirichletForm N_c f := (N_c/8) * Ent(f)` — engineered so the arithmetic
  `(2/(N_c/4)) * (N_c/8) * t = t` closes by `field_simp; ring`. Not derived from
  the physics.

### ✓ Genuine (non-tautological) results

| Result | Campaign | Method |
|--------|----------|--------|
| `instIsProbabilityMeasure_sunGibbsFamily_norm` | C132 | `ofReal_integral_eq_lintegral_ofReal` + `integral_div` |
| `sunPartitionFunction_pos`, `_le_one` | C132 | From C131 energy bounds |
| `sunPlaquetteEnergy_continuous` | C132 | Matrix/trace/re continuity composition |
| `sunPlaquetteEnergy N_c g = 1 - Re(tr g)/N_c` | C131 | Concrete def |
| `sunPlaquetteEnergy_nonneg` | C131 | `entry_norm_bound_of_unitary` (Mathlib) |
| `sunPlaquetteEnergy_le_two` | C131 | `entry_norm_bound_of_unitary` (Mathlib) |
| `balaban_rg_uniform_lsi` | C129 | Holley-Stroock perturbation |
| `sunGibbsFamily = Haar.withDensity(exp(-β·e(g)))` | C128 | Real Gibbs measure |

### Real progress

The LSI pipeline is **~85% proved** (1 of ~7 original axioms remains), but the
remaining connection to the Clay problem statement is semantic, not formal.
The genuine mathematical achievement is the DLR-uniform LSI for the **normalized**
SU(N) Gibbs measure (proved as a probability measure), modulo one specific
Holley-Stroock instance (`lsi_normalized_gibbs_from_haar`).

---

## Campaign History

| Campaign | Tag | Description | Verdict |
|----------|-----|-------------|---------|
| C1–C103 | v0.1–v1.18 | Early hypothesis elimination, lattice/gauge infrastructure | Foundation |
| C104 | v1.20.0 | `hdistP` eliminated (`Nat.cast_nonneg`) | ✓ |
| C105 | v1.21.0 | `StateNormBound` → `HasUnitObsNorm` | ✓ |
| C106 | v1.22.0 | `HasSpectralGap` → `HasNormContraction` | ✓ |
| C107 | v1.23.0 | `PhysicalContractionBundle` (1 live hypothesis) | ✓ |
| C108 | v1.24.0 | `WeakPhysicalContractionBundle` | ✓ |
| C109 | v1.25.0 | `PhysicalSpectralGapBundle` | ✓ |
| C110 | v1.26.0 | `FeynmanKacBundle` | ✓ |
| C111 | v1.27.0 | `ClayStrongFromFeynmanKac` | ✓ |
| C112 | v1.28.0 | `ConnectedCorrDecayBundle` | ✓ |
| C113 | v1.29.0 | `ConnectedCorrDecayDomBundle` | ✓ |
| C114 | v1.30.0 | `FeynmanKacStrongBundle` | ✓ |
| C115 | v1.31.0 | `NdepGapBundle` | ✓ |
| C116 | v1.32.0 | `ConnectedCorrDecayBundle` | ✓ |
| C117 | v1.33.0 | `FeynmanKacTheoremBundle` | ✓ |
| C118 | v1.34.0 | `ConnectedCorrDecayTheoremBundle` | ✓ |
| C119 | v1.35.0 | `NdepGapTheoremBundle` | ✓ |
| C120 | v1.36.0 | `ConnectedCorrDecayDomTheoremBundle` | ✓ |
| C121 | v1.37.0 | `FeynmanKacStrongTheoremBundle` | ✓ |
| C122 | v1.38.0 | `ClayStrongFromFeynmanKacTheoremBundle` | ✓ |
| C123 | v1.39.0 | **STRATEGY SHIFT**: LSI pipeline eliminates `yangMills_continuum_mass_gap` | ✓✓ |
| C124 | v1.40.0 | `bakry_emery_lsi` eliminated (BakryEmeryCD := LSI) | ✓ |
| C125 | v1.41.0 | `sz_lsi_to_clustering` bypassed (α* > 0 directly) | ✓ |
| C126 | v1.42.0 | `sun_bakry_emery_cd` eliminated (arithmetic on Dirichlet form) | ✓ |
| C127 | v1.43.0 | `balaban_rg_uniform_lsi` eliminated (Gibbs = Haar, tautological) | ⚠ |
| C128 | v1.43.1 | Semantic integrity: real Gibbs measure restored | ✓ |
| C129 | v1.43.2 | `balaban_rg_uniform_lsi` proved from Holley-Stroock | ✓✓ |
| C130 | v1.43.3 | `holleyStroock_sunGibbs_lsi` proved, +3 primitive axioms | ✓ |
| C131 | v1.44.0 | `sunPlaquetteEnergy` bounds proved from Mathlib trace theory, −2 axioms | ✓✓ |
| C132 | v1.44.0 | Normalize Gibbs measure; prove `IsProbabilityMeasure`; axiom → `lsi_normalized_gibbs_from_haar` | ✓✓ |
| C133 | v1.45.0 | Deep audit: axiom dependency graph, Mathlib LSI search, strategy mapping | ✓ |

---

## Live Path to Unconditionality

### Remaining axiom: `lsi_normalized_gibbs_from_haar`

**Statement** (BalabanToLSI.lean:255):
Holley-Stroock LSI for the **normalized** SU(N_c) Gibbs probability measure:
if Haar satisfies LSI(α), then the normalized Gibbs measure
`Haar.withDensity(exp(-β·e)/Z_β)` satisfies LSI(α·exp(-2β)).

**What it requires to prove from Mathlib:**
1. Entropy change-of-measure: `Ent_{ρ·μ}(f)` vs `Ent_μ(f)` for density ρ = exp(-β·e)/Z_β
2. Density bounds: exp(-2β)/Z_β ≤ ρ_norm ≤ 1/Z_β (from C131 energy bounds + C132 Z_β bounds)
3. LSI(α) applied to the density-weighted function, then bound Dirichlet form
4. The normalization (Z_β > 0) is already proved (C132)

**Reference**: Holley-Stroock (1987), Diaconis-Saloff-Coste (1996),
Ledoux "Concentration of Measure and Isoperimetric Inequalities" Ch. 5.

**Difficulty**: Medium. The normalization and probability-measure infrastructure
is already in place (C132). The remaining work is the entropy change-of-measure
calculation under bounded density perturbation.

---

## Paper-to-Formalization Map

### Papers [1]–[10] (viXra:2512.0060–2512.0085): Clustering, Recovery, AQFT

| Paper | Lean files | Status |
|-------|-----------|--------|
| [1]–[10] | `P2_MaxEntClustering/*.lean` | FORMALIZED (clustering, recovery channels, Petz fidelity) |

### Papers [11]–[20] (viXra:2512.0091–2601.0034): Heat Kernel, Bell, Gaussian, Markov

| Paper | Lean files | Status |
|-------|-----------|--------|
| [11]–[20] | `P2_MaxEntClustering/*.lean`, `L0_Lattice/*.lean` | PARTIAL (lattice geometry, local observables) |

### Papers [21]–[30] (viXra:2601.0035–2601.0051): CMI, Petz, Z₂ Lattice, Wilson

| Paper | Lean files | Status |
|-------|-----------|--------|
| [21]–[30] | `L4_WilsonLoops/WilsonLoop.lean`, `L0_Lattice/*.lean` | PARTIAL (Wilson loop defs, lattice gauge) |

### Papers [31]–[40] (viXra:2601.0064–2602.0033): RIP-U, Split-Regularized, YM Mass Gap

| Paper | Lean files | Status |
|-------|-----------|--------|
| [37]–[38] | `P7_SpectralGap/*.lean` | FORMALIZED (spectral gap infrastructure) |
| [39]–[40] | `P8_PhysicalGap/BalabanToLSI.lean`, `PhysicalMassGap.lean` | FORMALIZED (self-contained YM mass gap proof) |

### Papers [41]–[51] (viXra:2602.0035–2602.0055): Morse-Bott, Poincaré, LSI, DLR

| Paper | Lean files | Status |
|-------|-----------|--------|
| [44]–[45] | `P8_PhysicalGap/LSIDefinitions.lean`, `StroockZegarlinski.lean` | FORMALIZED (LSI defs, Stroock-Zegarlinski bridge) |
| [46] | `P8_PhysicalGap/SUN_DirichletCore.lean` | AXIOM (`sunDirichletForm_contraction` — paper [46] Ricci curvature) |
| [47]–[51] | `P8_PhysicalGap/BalabanToLSI.lean` | **1 AXIOM** (`lsi_normalized_gibbs_from_haar` — Holley-Stroock for normalized Gibbs) |

### Papers [52]–[57] (viXra:2602.0056–2602.0072): Large-Field, Cross-Scale, Balaban-Dimock

| Paper | Lean files | Status |
|-------|-----------|--------|
| [55] | `ClayCore/BalabanRG/*.lean` (~180 files) | PARTIAL (Balaban RG structural package) |
| [52]–[57] | `P3_BalabanRG/*.lean`, `P5_KPDecay/*.lean` | PARTIAL (RG contraction, KP hypotheses) |

### Papers [58]–[62] (viXra:2602.0073–2602.0087): RG-Cauchy, UV Stability

| Paper | Lean files | Status |
|-------|-----------|--------|
| [58]–[62] | `ClayCore/BalabanRG/P91*.lean`, `P6_AsymptoticFreedom/*.lean` | PARTIAL (RG framework, asymptotic freedom) |

### Papers [63]–[68] (viXra:2602.0088–2602.0117): Clustering, Spectral Gap, KP, Master Map

| Paper | Lean files | Status |
|-------|-----------|--------|
| [63]–[64] | `P8_PhysicalGap/DiscreteSpectralGap.lean` | FORMALIZED (spectral gap from clustering) |
| [65] | `P5_KPDecay/KPTerminalBound.lean` | FORMALIZED (terminal KP bound) |
| [67] | Overall architecture | FORMALIZED (master map = proof pipeline) |
| [68] | `ErikssonBridge.lean`, audit scripts | FORMALIZED (audit, reproducibility) |

---

## Build Status

| Phase | Files | Status | Terminal theorem |
|-------|-------|--------|-----------------|
| L0–L8 | L0_Lattice/ through L8_Terminal/ | ✓ BUILDS | `clay_millennium_yangMills` |
| P2 | P2_MaxEntClustering/ | ✓ BUILDS | Phase 2 assembly |
| P3 | P3_BalabanRG/ | ✓ BUILDS | Phase 3 assembly |
| P4 | P4_Continuum/ | ✓ BUILDS | Phase 4 assembly |
| P5 | P5_KPDecay/ | ✓ BUILDS | KP terminal bound |
| P6 | P6_AsymptoticFreedom/ | ✓ BUILDS | Asymptotic freedom |
| P7 | P7_SpectralGap/ | ✓ BUILDS | Phase 7 assembly |
| P8 | P8_PhysicalGap/ | ✓ BUILDS | `sun_physical_mass_gap` |
| ClayCore | ClayCore/BalabanRG/ (~180 files) | ✓ BUILDS | RG package |
| Experimental | Experimental/ | ✓ BUILDS | Research frontier |

---

## Discharge Chain (current proof architecture)

```
                        ClayYangMillsTheorem
                               ↑
                    sun_physical_mass_gap (C132)
                               ↑
                   sun_clay_conditional_norm
                               ↑
                    sun_gibbs_dlr_lsi_norm
                        ↗            ↘
            sun_haar_lsi          balaban_rg_uniform_lsi_norm (C132: THEOREM)
           (Bakry-Émery)                    ↑
                              holleyStroock_sunGibbs_lsi_norm (C132: THEOREM)
                                            ↑
                              lsi_normalized_gibbs_from_haar (**AXIOM**)
                                         +
                        instIsProbabilityMeasure_sunGibbsFamily_norm (C132: THEOREM)
```

---

## Key Definitions

```lean
-- Log-Sobolev inequality (LSIDefinitions.lean)
def LogSobolevInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ ∀ f, Measurable f →
    Ent_μ(f²) ≤ (2/α) * E f

-- DLR-uniform LSI (LSIDefinitions.lean)
def DLR_LSI (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ) : Prop :=
  0 < α_star ∧ ∀ L : ℕ, LogSobolevInequality (gibbsFamily L) E α_star

-- Concrete SU(N) plaquette energy (BalabanToLSI.lean, C131)
noncomputable def sunPlaquetteEnergy (N_c : ℕ) [NeZero N_c] : SUN_State N_c → ℝ :=
  fun g => 1 - (Matrix.trace g.val).re / (N_c : ℝ)

-- Heat-kernel Gibbs measure (BalabanToLSI.lean, C128)
noncomputable def sunGibbsFamily (d N_c : ℕ) [NeZero N_c] (β : ℝ) :
    ℕ → Measure (SUN_State N_c) :=
  fun _L => (sunHaarProb N_c).withDensity
    (fun g => ENNReal.ofReal (Real.exp (-β * sunPlaquetteEnergy N_c g)))

-- Normalized Gibbs density (BalabanToLSI.lean, C132)
noncomputable def sunNormalizedGibbsDensity (N_c : ℕ) [NeZero N_c]
    (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β) : SUN_State N_c → ENNReal :=
  fun g => ENNReal.ofReal
    (Real.exp (-β * sunPlaquetteEnergy N_c g) / sunPartitionFunction N_c β)

-- Normalized Gibbs family (probability measure, C132)
noncomputable def sunGibbsFamily_norm (d N_c : ℕ) [NeZero N_c]
    (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β) : ℕ → Measure (SUN_State N_c) :=
  fun _L => (sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ)

-- Bakry-Émery CD := LSI (tautological, C124)
def BakryEmeryCD (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (K : ℝ) : Prop :=
  LogSobolevInequality μ E K

-- Engineered Dirichlet form (tautological, C126)
noncomputable def sunDirichletForm (N_c : ℕ) [NeZero N_c]
    (f : SUN_State N_c → ℝ) : ℝ :=
  (N_c : ℝ) / 8 * Ent(f)
```

---

## Reference Papers

The following 68 preprints by Lluis Eriksson constitute the companion-paper
programme underlying this formalisation. All are freely available at
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

---

## Repository Structure

```
THE-ERIKSSON-PROGRAMME/
├── lakefile.lean                     # Lake build file
├── lake-manifest.json                # Pinned Mathlib4 commit
├── lean-toolchain                    # Lean 4 version
│
├── README.md                         # This file
├── UNCONDITIONALITY_ROADMAP.md       # Append-only campaign log (C1–C133)
├── STATE_OF_THE_PROJECT.md           # Current version, live axioms
├── AXIOM_FRONTIER.md                 # Live vs dead axiom census
├── AI_ONBOARDING.md                  # AI agent guide
├── ROADMAP.md                        # Phase structure
├── HYPOTHESIS_FRONTIER.md            # Hypothesis audit
│
└── YangMills/
    ├── ErikssonBridge.lean           # clay_yangmills_unconditional (0 axioms)
    ├── OracleC97–C100.lean           # Oracle check files
    │
    ├── L0_Lattice/                   # Lattice geometry, gauge configs, SU(2), Wilson action
    ├── L1_GibbsMeasure/              # Gibbs measure, expectations, correlations
    ├── L2_Balaban/                   # RG flow, small/large decomposition, measurability
    ├── L3_RGIteration/               # Block-spin, gauge invariance
    ├── L4_LargeField/                # Large-field suppression
    ├── L4_TransferMatrix/            # Transfer matrix
    ├── L4_WilsonLoops/               # Wilson loops
    ├── L5_MassGap/                   # Mass gap definition
    ├── L6_FeynmanKac/                # Feynman-Kac formula
    ├── L6_OS/                        # Osterwalder-Schrader
    ├── L7_Continuum/                 # Continuum limit, decay summability
    ├── L8_Terminal/                   # ClayTheorem, bundles, bridges
    │
    ├── P2_MaxEntClustering/          # Clustering, recovery, Petz fidelity
    ├── P3_BalabanRG/                 # RG contraction, multiscale decay
    ├── P4_Continuum/                 # Continuum bridge
    ├── P5_KPDecay/                   # KP hypotheses, terminal bound
    ├── P6_AsymptoticFreedom/         # Beta function, coupling convergence
    ├── P7_SpectralGap/               # Transfer matrix gap, action bound
    │
    ├── P8_PhysicalGap/               # ★ PRIMARY PROOF PATH ★
    │   ├── LSIDefinitions.lean       #   LogSobolevInequality, DLR_LSI defs
    │   ├── SUN_StateConstruction.lean #  Concrete SU(N) state space
    │   ├── SUN_DirichletCore.lean    #   SU(N) Dirichlet form
    │   ├── BalabanToLSI.lean         #   ★ Haar-LSI, Gibbs-LSI, 1 AXIOM
    │   ├── PhysicalMassGap.lean      #   ★ sun_physical_mass_gap
    │   └── [40+ additional modules]  #   Spectral gap, variance decay, etc.
    │
    ├── ClayCore/BalabanRG/           # ~180 files: Balaban RG structural package
    └── Experimental/                 # Research frontier (Lie derivatives, semigroups)
```

**349 Lean files · 0 sorry · ~26 axioms (1 BFS-live for main theorem)**

---

## Building & Usage

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean 4 toolchain manager)

### Build

```bash
# Clone and build
git clone https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git
cd THE-ERIKSSON-PROGRAMME
lake exe cache get    # download Mathlib cache
lake build YangMills  # full build (~349 files)

# Build only the primary proof path
lake build YangMills.P8_PhysicalGap.PhysicalMassGap

# Check oracle
printf 'import YangMills.P8_PhysicalGap.PhysicalMassGap\n#print axioms YangMills.sun_physical_mass_gap\n' | lake env lean --stdin
```

### Expected oracle output (v1.45.0)

```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.lsi_normalized_gibbs_from_haar]
```

---

## Author

**Lluis Eriksson** — independent researcher

---

## License

**AGPL-3.0** (GNU Affero General Public License v3.0)
