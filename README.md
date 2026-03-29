# THE ERIKSSON PROGRAMME

**Lean 4 formalization of the Yang–Mills mass gap programme**

[![License: AGPL v3](https://img.shields.io/badge/License-AGPL_v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)
[![Lean 4](https://img.shields.io/badge/Lean-4-orange)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-green)](https://leanprover-community.github.io/mathlib4_docs/)

> **Current milestone (2026-03-28):** `BalabanRGUniformLSILiveTarget` and
> `HaarLSIFrontierPackage` are unconditionally closed at the packaging layer.
> 0 `sorry` across all Lean source; all gaps are explicit named `axiom`. Remaining
> honest mathematical gaps documented in `AXIOM_FRONTIER.md`.

---

## Project Overview

The Eriksson Programme is a systematic, machine-verified attempt to formalize
the proof strategy for the Yang–Mills existence and mass gap problem — one of
the seven Clay Millennium Prize Problems — using the **Lean 4** interactive
theorem prover with the **Mathlib4** mathematical library.

The programme does **not** claim to have solved the Clay problem. Instead it:

1. Formalizes the mathematical infrastructure (gauge groups, connections,
   curvature, Haar measure, Logarithmic Sobolev Inequalities, spectral theory)
   in a machine-checkable language.
2. Tracks the honest boundary between what is verified and what remains open,
   using explicit `axiom` declarations (never silent `sorry`) for every
   unproven gap.
3. Implements a Balaban renormalization group programme following the
   construction of Balaban (1982–1989), adapted to the rigorous functional-
   analytic framework of Glimm–Jaffe and Seiler.

### The Clay Problem (informal statement)

Prove the existence of a quantum Yang–Mills gauge theory on ℝ⁴ with compact
simple gauge group G (e.g. SU(N)), satisfying the Wightman / Osterwalder–
Schrader axioms, such that the theory has a **mass gap** Δ > 0:

  inf(spec(H_YM) \ {E₀}) ≥ Δ > 0

where H_YM is the quantum Hamiltonian and E₀ is the vacuum energy.

---

## Reference Papers

The following references underpin the mathematical content of this project.
PDF scans are collected in the `docs/` subdirectory.

### Foundational Clay Problem Statement
- **Jaffe–Witten**, "Yang–Mills Existence and Mass Gap"
  (Clay Mathematics Institute Official Problem Statement, 2000)
  — `Clay-YangMills-Statement.pdf`

### Balaban Renormalization Group
- **Balaban, T.**, "Renormalization Group Approach to Lattice Gauge Field Theories I"
  *Commun. Math. Phys.* 109 (1987) — `YangMills-Bloque1.pdf`
- **Balaban, T.**, "Renormalization Group Methods in Non-Abelian Gauge Theories"
  Harvard preprint — `YangMills-Bloque2.pdf`
- **Balaban, T.**, "Ultraviolet Stability of Three-Dimensional Lattice Pure Gauge Field Theories"
  *Commun. Math. Phys.* 102 (1985) — `YangMills-Bloque3.pdf`
- **Balaban, T.**, "Averaging Operations for Lattice Gauge Theories"
  *Commun. Math. Phys.* 98 (1985) — `YangMills-Bloque4.pdf`
- **Balaban, T.**, "The Large Field Renormalization Operation for Classical N-Vector Models"
  *Commun. Math. Phys.* 109 (1987) — `YangMills-Bloque5.pdf`
- **Balaban, T.**, "Convergent Renormalization Expansions for Lattice Gauge Theories"
  *Commun. Math. Phys.* 119 (1988) — `YangMills-Bloque6.pdf`

### Logarithmic Sobolev Inequalities
- **Gross, L.**, "Logarithmic Sobolev Inequalities"
  *Amer. J. Math.* 97 (1975), 1061–1083
- **Bakry, D. & Émery, M.**, "Diffusions Hypercontractives"
  *Séminaire de Probabilités XIX* (1985)
- **Ledoux, M.**, "The Geometry of Markov Diffusion Generators" (1998)

### Constructive Quantum Field Theory
- **Glimm, J. & Jaffe, A.**, "Quantum Physics: A Functional Integral Point of View"
  Springer, 2nd ed. (1987)
- **Seiler, E.**, "Gauge Theories as a Problem of Constructive Quantum Field Theory"
  *Lecture Notes in Physics* 159, Springer (1982)
- **Brydges, D., Fröhlich, J. & Seiler, E.**,
  "On the Construction of Quantized Gauge Fields I–III"
  *Ann. Phys.* 121 (1979), *Commun. Math. Phys.* 71 (1980), 79 (1981)

### Spectral Theory and Hypercontractivity
- **Nelson, E.**, "The free Markoff field" *J. Funct. Anal.* 12 (1973)
- **Gross, L.**, "Hypercontractivity and logarithmic Sobolev inequalities
  for the Clifford-Dirichlet form" *Duke Math. J.* 42 (1975)

---

## Repository Structure

```
THE-ERIKSSON-PROGRAMME/
├── lakefile.lean                    # Lake build file (auto-discovers YangMills/)
├── lake-manifest.json               # Pinned Mathlib4 commit
├── README.md                        # This file
├── AXIOM_FRONTIER.md                # Volatile frontier: axioms, gaps, milestones
├── SORRY_FRONTIER.md                # Confirms 0 sorry (all gaps = explicit axioms)
├── Colab_Agente_YangMills.py        # Python agent for automated iteration
│
└── YangMills/
    ├── Foundations/
    │   ├── GaugeGroup.lean          # Compact Lie group typeclass, Haar measure
    │   ├── PrincipalBundle.lean     # Principal G-bundles, gauge transformations
    │   ├── Connection.lean          # Connections, gauge action
    │   └── CurvatureTensor.lean     # Curvature 2-form, Bianchi identity
    │
    ├── ClayCore/
    │   ├── YangMillsFunctional.lean # Yang-Mills action S_YM = ∫‖F_A‖²
    │   ├── YangMillsEquations.lean  # Euler-Lagrange: D_A ★F_A = 0
    │   ├── GaugeInvariance.lean     # Gauge invariance of S_YM
    │   ├── MassGapStatement.lean    # Formal mass gap statement
    │   │
    │   └── BalabanRG/               # Balaban RG programme (~280 files)
    │       ├── BalabanRGPackage.lean           # 3-pillar RG package structure
    │       ├── BalabanRGPackageWitness.lean    # ★ Explicit witness (NEW)
    │       ├── HaarLSITransferWitness.lean     # ★ Transfer witnesses (NEW)
    │       ├── HaarLSIDirectBridge.lean        # Direct bridge theorem
    │       ├── HaarLSILiveTarget.lean          # Public live target
    │       ├── BalabanRGUniformLSILiveTarget.lean  # Canonical public target
    │       ├── HaarLSIBridge.lean              # Uniform→Haar bridge
    │       ├── HaarLSIFrontier.lean            # Frontier package
    │       ├── HaarLSIReduction.lean           # Haar-LSI ← Ricci bound
    │       ├── HaarLSIAnalyticTarget.lean      # Analytic LSI target
    │       ├── UniformLSITransfer.lean         # Package → uniform LSI
    │       └── [~270 additional modules]       # Activity fields, blocking maps,
    │                                           # coupling recursion, norm bounds…
    │
    └── P8_PhysicalGap/              # Physical mass gap programme
        ├── BalabanToLSI.lean        # M1: Haar-LSI via Bakry-Émery
        │                            # M2: RG → uniform DLR-LSI
        │                            # Assembly: sun_gibbs_dlr_lsi
        ├── LSIDefinitions.lean      # LogSobolevInequality, DLR_LSI, ExponentialClustering
        ├── SUN_StateConstruction.lean  # Concrete SU(N) state space
        ├── SUN_DirichletCore.lean   # SU(N) Dirichlet form
        ├── PhysicalMassGap.lean     # ClayYangMillsTheorem
        └── [additional P8 modules]
```

---

## Proving Unconditionality

### Philosophy: `axiom` over `sorry`

The project enforces a strict discipline: every unproven gap is declared
as an explicit named `axiom`, never left as a silent `sorry`. This means:

- `lake build` passes locally with 0 errors, 0 warnings, 0 `sorry`
- The full dependency graph of every theorem is machine-checkable
- Any reader can audit exactly which mathematical claims are assumed
  (see `AXIOM_FRONTIER.md`)

### Current Axiom Inventory

**Clay-core axioms** (genuine mathematical content, not yet formalized):

| Axiom | Mathematical Content |
|---|---|
| `sun_bakry_emery_cd` | SU(N) satisfies Bakry-Émery CD(N/4, ∞) |
| `bakry_emery_lsi` | Bakry-Émery criterion implies LSI (Mathlib gap) |
| `balaban_rg_uniform_lsi` | RG promotes per-site Haar-LSI to uniform DLR-LSI |
| `sz_lsi_to_clustering` | Stroock-Zegarlinski: uniform DLR-LSI → exponential clustering |
| `clustering_to_spectralGap` | Exponential clustering → spectral gap |

**Mathlib gap axioms** (formalization infrastructure, not Clay-specific):

| Axiom | Content |
|---|---|
| `instIsTopologicalGroupSUN` | `IsTopologicalGroup` for `Matrix.specialUnitaryGroup` |
| `sunDirichletForm_contraction` | Beurling-Deny normal contraction |
| `hille_yosida` | Hille-Yosida theorem for Markov semigroups |

### The Direct Bridge Architecture

The proof architecture follows a four-layer funnel:

```
Layer 1 (Clay-physics):     sun_bakry_emery_cd + bakry_emery_lsi
                                     ↓
                           sun_haar_lsi (Haar-LSI for SU(N))
                                     ↓ balaban_rg_uniform_lsi
Layer 2 (RG):              sun_gibbs_dlr_lsi (uniform DLR-LSI)
                                     ↓ sz_lsi_to_clustering
Layer 3 (spectral):        sun_gibbs_clustering (exponential clustering)
                                     ↓ clustering_to_spectralGap
Layer 4 (mass gap):        ClayYangMillsTheorem (∃ m_phys > 0)
```

The packaging layer (BalabanRG modules) has been fully closed:
`BalabanRGUniformLSILiveTarget` and `HaarLSIFrontierPackage` are
proved unconditionally, reducing the open frontier to exactly the
axioms listed above.

---

## Workflow Automation

### `Colab_Agente_YangMills.py`

An automated Python agent that runs in Google Colab and iterates on the
Lean 4 proof frontier. The agent:

1. Clones / pulls the repository
2. Counts remaining `sorry` placeholders (target: always 0)
3. Identifies the primary compilation target (`HaarLSIDirectBridge.lean`)
4. Calls an LLM (Claude Opus or GPT-4o via OpenRouter) with the
   full file content as context
5. Extracts the Lean 4 code from the response and writes it to the file
6. Runs `lake build` to check for errors
7. If errors: reverts the file and retries (up to `MAX_ITERATIONS = 10`)
8. Commits and pushes successful changes

**Required secrets** (set in Colab notebook secrets):
- `GITHUB_TOKEN` — personal access token with repo write access
- `OPENROUTER_API_KEY` — OpenRouter API key for LLM access

**Configuration:**
```python
MODEL           = "anthropic/claude-opus-4"   # LLM model
MAX_ITERATIONS  = 10                           # Retry budget
LLM_TEMPERATURE = 0.1                         # Low temperature for precision
TARGET_MODULE   = "YangMills.ClayCore.BalabanRG.HaarLSIDirectBridge"
```

---

## Current State & Progress

### Build Status

```
lake build (local): 0 errors · 0 warnings · 0 sorry
```

### Milestone History

| Date | Milestone |
|---|---|
| 2026-03-28 | **Axiom 6**: `HaarLSIFrontierPackage` closed unconditionally |
| 2026-03-28 | **Axiom 5**: 4 P91 BalabanRG files fully verified (P91DenominatorControl, P91AsymptoticFreedomSkeleton, BalabanCouplingRecursion, P91OnestepDriftSkeleton) |
| 2026-03-28 | **Axiom 4**: 16 BalabanRG modules compiled clean (unused variable cleanup) |
| 2026-03-28 | **Axiom 3**: `BalabanRGUniformLSIEquivalenceRegistry` clean |
| 2026-03-28 | **Axiom 2**: `HaarLSIDirectBridge` fully abstract |

### Open Frontier

The live mathematical obstructions are documented in `AXIOM_FRONTIER.md`:
- The genuine Clay-problem content is isolated in three axioms in
  `BalabanToLSI.lean`: `sun_bakry_emery_cd`, `balaban_rg_uniform_lsi`,
  `sz_lsi_to_clustering`
- All infrastructure, packaging, and architectural layers are clean

---

## Building & Usage

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (tested with
  the Mathlib4 toolchain)
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

# Expected output: 0 errors, 0 warnings, 0 sorry
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
# List all axioms in the project (these are the honest gaps)
grep -r "^axiom " YangMills/ --include="*.lean"

# Confirm zero sorry
grep -r "sorry" YangMills/ --include="*.lean" | grep -v "^--" | grep -v "^\s*--"
```

---

## License

Copyright (C) 2024–2026 Lluís Eriksson

This program is free software: you can redistribute it and/or modify
it under the terms of the **GNU Affero General Public License** as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
[GNU Affero General Public License](https://www.gnu.org/licenses/agpl-3.0)
for more details.

SPDX-License-Identifier: AGPL-3.0-or-later
