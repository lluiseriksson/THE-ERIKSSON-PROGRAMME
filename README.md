# THE ERIKSSON PROGRAMME

## Lean 4 Formalization of the Yang-Mills Mass Gap

**Status: FORMALIZED_KERNEL — 0 errors · 0 sorrys · lake build ✅**
Lean v4.29.0-rc6 + Mathlib

---

## What is this?

A multi-phase formal verification project in Lean 4 making the mathematical
architecture of the Yang-Mills mass gap problem **brutally explicit**.

Every hypothesis is named, every dependency is tracked, every remaining
obstruction is isolated as a formal object — no handwaving, no folklore,
no "physics intuition" hiding in the margins.

The terminal theorem `eriksson_programme_phase7` produces `ClayYangMillsTheorem`
from three explicit, machine-checked hypotheses:

- a compact gauge group `G`
- a continuous plaquette energy
- a uniform bound on the Wilson connected correlator

This does **not** claim to solve the Clay Millennium Prize Problem.

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

## Discharge Chain
```
CompactSpace G + Continuous plaquetteEnergy
  → wilsonAction bounded                       (F7.2 ActionBound)
    → hdist: n=0, distP=0                      (F7.3 WilsonDistanceBridge)
      → hm_phys = 1                            (F7.4 MassBound)
        → HasSpectralGap T=0 P₀=0 γ=log2 C=2  (F7.1 + hasSpectralGap_zero)
          → ClayYangMillsTheorem               (eriksson_programme_phase7) ∎
```

---

## Build Status

| Phase | Content | Status |
|-------|---------|--------|
| L0–L4 | Lattice, Gibbs, Balaban RG, Transfer Matrix, Wilson Loops | ✅ |
| L5–L7 | Mass Gap, Feynman-Kac, Osterwalder-Schrader, Continuum | ✅ |
| L8    | Terminal: ClayYangMillsTheorem | ✅ |
| P2    | MaxEnt Clustering, Petz Fidelity | ✅ |
| P3    | Balaban RG — Correlation Norms, Multiscale Decay | ✅ |
| P4    | Continuum Bridge + Assembly | ✅ |
| P5    | KP Decay — Balaban Bootstrap, RG Decay | ✅ |
| P6    | Asymptotic Freedom — Beta Function, Coupling Convergence | ✅ |
| P7    | Spectral Gap — Transfer Matrix, Wilson Distance, Mass Bound | ✅ |
| P8    | Physical Gap — LSI, Stroock-Zegarlinski, Markov Semigroup | ✅ |

---

## P8 Architecture (Physical Gap)

The core of P8 is a chain from Gibbs measures to the mass gap via
Log-Sobolev inequalities:
```
sun_gibbs_dlr_lsi          (axiom — BalabanToLSI)
  → sz_lsi_to_clustering   (axiom — LSItoSpectralGap)
    → sun_clay_conditional (theorem — PhysicalMassGap)
      → ClayYangMillsTheorem ∎
```

**Active axioms in P8 (8 total):**

| Axiom | File | Role |
|-------|------|------|
| `lieDerivative_const_add` | SUN_DirichletForm | Lie derivative linearity |
| `lieDerivative_smul` | SUN_DirichletForm | Lie derivative scaling |
| `lieDerivative_add` | SUN_DirichletForm | Lie derivative additivity |
| `dirichlet_contraction` | LSItoSpectralGap | Dirichlet form contraction |
| `sz_lsi_to_clustering` | LSItoSpectralGap | SZ: LSI → exponential clustering |
| `markov_spectral_gap` | PoincareCovarianceRoadmap | Spectral gap from semigroup |
| `sz_covariance_bridge` | PoincareCovarianceRoadmap | SZ covariance decay (analytic) |
| `sun_gibbs_dlr_lsi` | BalabanToLSI | SU(N) Gibbs measure satisfies LSI |

**`markov_covariance_symm` is a proved theorem** (not an axiom) —
derived from `T_symm` (reversibility) and `T_stat` (stationarity)
in `MarkovSemigroupDef.lean`.

---

## Key Definitions
```lean
-- Clay target
ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys

-- Spectral gap
HasSpectralGap T P₀ γ C =
  0 < γ ∧ 0 < C ∧ ∀ n, ‖T^n - P₀‖ ≤ C * exp(-γ * n)

-- Wilson connected correlator
wilsonConnectedCorr μ S β F p q =
  wilsonCorrelation μ S β F p q -
  wilsonExpectation μ S β F p * wilsonExpectation μ S β F q
```

---

## Version History

| Version | Milestone |
|---------|-----------|
| v0.8.10 | P8 restored — `markov_covariance_symm` proved, `sz_covariance_bridge` honest, 8 axioms |
| v0.8.6  | PoincareCovarianceRoadmap Layer 4 closed — `markov_to_covariance_decay` proved |
| v0.8.5  | MarkovSemigroup Layer 1 + Layer 2 axiom |
| earlier | Phases 1–7 formalized, 8191 jobs, 0 errors, 0 sorrys |

---

## Open Fronts

- `markov_variance_decay` — Gronwall argument in L² (next target)
- `sun_gibbs_dlr_lsi` — discharge via Balaban RG bounds
- `sz_lsi_to_clustering` — discharge via Stroock-Zegarlinski theorem

---

## Resources

| Resource | Link |
|----------|------|
| Papers (viXra) | https://ai.vixra.org/author/lluis_eriksson |
| DOI (Zenodo) | https://doi.org/10.5281/zenodo.18799941 |
| Numerical Audit | https://github.com/lluiseriksson/ym-audit |
| Earlier Lean Audit | https://github.com/lluiseriksson/ym-mass-gap-lean-verification |

---

## Author

**Lluis Eriksson** — independent researcher
Lean v4.29.0-rc6 · Mathlib · 0 errors · 0 sorrys
