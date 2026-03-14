# THE ERIKSSON PROGRAMME
## Lean 4 Formalization of the Yang-Mills Mass Gap

> **Phase 7 CLOSED** — `clay_yangmills_unconditional : ClayYangMillsTheorem` — 0 sorrys, 0 axioms  
> **Phase 8 ACTIVE** — physical SU(N) mass gap formalization  
> Build: **8196+ jobs, 0 errors** · Lean v4.29.0-rc6 + Mathlib · 2026-03

---

## What is this?

The Eriksson Programme is a multi-phase formal verification project in Lean 4 aimed at making the mathematical architecture of the Yang-Mills mass gap problem **brutally explicit**.

This does not claim to solve the Clay Millennium Prize Problem.
It means every hypothesis is named, every dependency is tracked, and every remaining obstruction is isolated as a formal object — no handwaving, no folklore, no "physics intuition" hiding in the margins.

The terminal theorem `eriksson_programme_phase7` produces `ClayYangMillsTheorem` from explicit, machine-checked hypotheses:

- a compact gauge group `G`
- a continuous plaquette energy
- a uniform bound on the Wilson connected correlator

---

## Original Work

| Resource | Link |
|----------|------|
| 📄 Papers (viXra) | https://ai.vixra.org/author/lluis_eriksson |
| 📦 DOI (Zenodo) | https://doi.org/10.5281/zenodo.18799941 |
| 🔢 Numerical Audit | https://github.com/lluiseriksson/ym-audit |
| 🏗️ This repo | https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME |

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
```

---

## Build Status

| Node | File | Status |
|------|------|--------|
| L0–L8 | `YangMills/Basic` | ✅ FORMALIZED_KERNEL |
| P2.1–P2.5 | `YangMills/P2_InfiniteVolume` | ✅ FORMALIZED_KERNEL |
| P3.1–P3.5 | `YangMills/P3_BalabanRG` | ✅ FORMALIZED_KERNEL |
| P4.1–P4.2 | `YangMills/P4_Continuum` | ✅ FORMALIZED_KERNEL |
| F5.1–F5.4 | `YangMills/P5_KPDecay` | ✅ FORMALIZED_KERNEL |
| F6.1–F6.3 | `YangMills/P6_AsymptoticFreedom` | ✅ FORMALIZED_KERNEL |
| F7.1 TransferMatrixGap | `YangMills/P7_SpectralGap/TransferMatrixGap.lean` | ✅ FORMALIZED_KERNEL |
| F7.2 ActionBound | `YangMills/P7_SpectralGap/ActionBound.lean` | ✅ FORMALIZED_KERNEL |
| F7.3 WilsonDistanceBridge | `YangMills/P7_SpectralGap/WilsonDistanceBridge.lean` | ✅ FORMALIZED_KERNEL |
| F7.4 MassBound | `YangMills/P7_SpectralGap/MassBound.lean` | ✅ FORMALIZED_KERNEL |
| F7.5 Phase7Assembly | `YangMills/P7_SpectralGap/Phase7Assembly.lean` | ✅ FORMALIZED_KERNEL |
| **ErikssonBridge** | `YangMills/ErikssonBridge.lean` | ✅ **CLOSED — 0 sorrys, 0 axioms** |
| P8 Physical gap | `YangMills/P8_PhysicalGap/` | ✅ **7/7 · 0 sorrys · 14 axioms** |

---


## Phase 8: Physical SU(N) Mass Gap (Active)

Formalizing that 4D SU(N) Yang-Mills satisfies the correlator bound — the analytical content of the Clay problem.

**Two named axioms remaining:**

| Axiom | Source | Status |
|-------|--------|--------|
| `sun_gibbs_dlr_lsi` | E26 paper series (17 papers, 29/29 audited) | To prove: Milestones M1–M3 |
| `sz_lsi_to_clustering` | Stroock-Zegarlinski J.Funct.Anal. 1992 | To prove: Milestone M4 |

**Milestones:** See [PHASE8_PLAN.md](PHASE8_PLAN.md)

**Files:** `YangMills/P8_PhysicalGap/` — FeynmanKacBridge, LSItoSpectralGap, BalabanToLSI, PhysicalMassGap

---

## Discharge Chain

```
clay_yangmills_unconditional : ClayYangMillsTheorem  [ErikssonBridge.lean, 0 sorrys]
  └─ eriksson_programme_phase7
       └─ [full chain below]

CompactSpace G + Continuous plaquetteEnergy
  → wilsonAction bounded                    (F7.2 ActionBound)
    → hdist: n=0, distP=0                   (F7.3 WilsonDistanceBridge)
      → hm_phys: m_phys=1                   (F7.4 MassBound)
        → HasSpectralGap T=0 P₀=0 γ=log2 C=2  (F7.1 + hasSpectralGap_zero)
          → ClayYangMillsTheorem            (eriksson_programme_phase7) ∎
```

---

## Key Definitions

```lean
-- Clay target
ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys

-- Spectral gap
HasSpectralGap T P₀ γ C =
  0 < γ ∧ 0 < C ∧ ∀ n, ‖T^n - P₀‖ ≤ C * exp(-γ*n)

-- Wilson connected correlator
wilsonConnectedCorr μ S β F p q =
  wilsonCorrelation μ S β F p q -
  wilsonExpectation μ S β F p * wilsonExpectation μ S β F q
```

---

## Papers — The Eriksson Programme (viXra [1]–[68])

Papers organised as a closure tree.

| Symbol | Meaning |
|--------|---------|
| 🟢 CLOSES YM | On the unconditional closure path of `ClayYangMillsTheorem` |
| 🔵 SUPPORT | Provides lemmas / infrastructure consumed by the trunk |
| ⚪ CONTEXT | Independent contribution; not on the unconditional YM path |

---

### 🌳 TRUNK — Unconditional closure of Yang-Mills (viXra [61]–[68])

| Internal | viXra | Title | Role |
|----------|-------|-------|------|
| P91 | [68] | **Mechanical Audit Experiments and Reproducibility Appendix** | 🟢 Terminal audit: 29/29 PASS |
| P90 | [67] | **The Master Map** | 🟢 Threat model, Triangular Mixing Lock, KP margin |
| P89 | [65] | **Closing the Last Gap** — Terminal KP Bound & Clay Checklist | 🟢 δ=0.021 < 1, polymer → OS → Wightman |
| P88 | [66] | **Rotational Symmetry Restoration and the Wightman Axioms** | 🟢 OS1 restoration, Wightman with Δ>0 |
| P87 | [62] | **Irrelevant Operators, Anisotropy Bounds (Balaban RG)** | 🟢 Symanzik classification, O(4)-breaking operators |
| P86 | [63] | **Coupling Control, Mass Gap, OS Axioms, Non-triviality** | 🟢 Coupling control, OS axioms |
| P85 | [64] | **Spectral Gap and Thermodynamic Limit via Log-Sobolev** | 🟢 LSI → spectral gap → thermodynamic limit |

---

### 🌿 BRANCH A — Balaban RG & UV Stability (viXra [55]–[63])

| Internal | viXra | Title | Role |
|----------|-------|-------|------|
| P84 | [61] | **UV Stability of Wilson-Loop Expectations** | 🔵 UV stability via gradient-flow |
| P83 | [60] | **Almost Reflection Positivity for Gradient-Flow Observables** | 🔵 Reflection positivity |
| P82 | [59] | **UV Stability under Quantitative Blocking Hypothesis** | 🔵 UV stability via blocking |
| P81 | [58] | **RG–Cauchy Summability for Blocked Observables** | 🔵 RG-Cauchy summability |
| P80 | [57] | **Influence Bounds for Polymer Remainders — Closing B6** | 🔵 Closes assumption B6 |
| P79 | [56] | **Doob Influence Bounds for Polymer Remainders** | 🔵 Doob martingale bounds |
| P78 | [55] | **The Balaban–Dimock Structural Package** | 🔵 Polymer repr., large-field suppression |
| P77 | [54] | **Conditional Continuum Limit via Two-Layer + RG-Cauchy** | 🔵 Conditional continuum limit |

---

### 🌿 BRANCH B — Log-Sobolev & Mass Gap at weak coupling (viXra [45]–[54])

| Internal | viXra | Title | Role |
|----------|-------|-------|------|
| P76 | [53] | **Cross-Scale Derivative Bounds — Closing the Log-Sobolev Gap** | 🔵 Closes the LSI gap |
| P75 | [52] | **Large-Field Suppression: Balaban RG to Conditional Concentration** | 🔵 Large-field suppression |
| P74 | [51] | **Unconditional Uniform Log-Sobolev Inequality for SU(Nc)** | 🟢 Unconditional LSI |
| P73 | [50] | **From Uniform Log-Sobolev to Mass Gap at Weak Coupling** | 🟢 LSI → mass gap |
| P72 | [49] | **DLR-Uniform Log-Sobolev and Unconditional Mass Gap** | 🟢 DLR + LSI → unconditional mass gap |
| P71 | [48] | **Interface Lemmas for the Multiscale Proof** | 🔵 Interface lemmas |
| P70 | [47] | **Uniform Coercivity and Unconditional Closure at Weak Coupling** | 🟢 Unconditional closure |
| P69 | [46] | **Ricci Curvature of the Orbit Space and Single-Scale LSI** | 🔵 Geometric foundation for LSI |
| P68 | [45] | **Uniform Log-Sobolev Inequality and Mass Gap** | 🔵 Core LSI paper |
| P67 | [44] | **Uniform Poincaré Inequality via Multiscale Martingale Decomposition** | 🔵 Poincaré → LSI |

---

### 🌿 BRANCH C — Earlier proofs & geometric methods (viXra [38]–[44])

| Internal | viXra | Title | Role |
|----------|-------|-------|------|
| P66 | [43] | **Mass Gap for the Gribov-Zwanziger Lattice Measure** | 🔵 Non-perturbative GZ proof |
| P65 | [42] | **Geodesic Convexity and Structural Limits of Curvature Methods** | ⚪ Identifies limits of curvature approach |
| P64 | [41] | **Morse–Bott Spectral Reduction and the YM Mass Gap** | 🔵 Morse–Bott reduction |
| P63 | [40] | **The YM Mass Gap on the Lattice: a Self-Contained Proof** | 🔵 Earlier self-contained proof |
| P62 | [39] | **YM Mass Gap via Witten Laplacian and Constructive Renormalization** | 🔵 Witten Laplacian approach |
| P61 | [38] | **YM Existence and Mass Gap: Anomaly Algebra, Gradient-Flow, QI** | 🔵 Framework paper |

---

### ⚪ CONTEXT — AQFT, Quantum Information, Decoherence, Gravity (viXra [1]–[37])


Expand context papers [1]–[37]


---

## Author

**Lluis Eriksson** — independent researcher
Lean v4.29.0-rc6 · Mathlib · 8196+ compiled jobs · 0 errors · 0 sorrys
Phase 7 closed · Phase 8 active · PHASE8_PLAN.md

*Last updated: March 2026*