# AXIOM_FRONTIER.md — v0.8.49

## P8 is proof-clean: 0 real sorrys.
## Frontier: 7 axioms.
## Journey: 13 → 12 → 11 → 10 → 8 → 7

Last updated: v0.8.49 (2026-03-18)
Build: 0 errors, 0 sorrys

---

## P8 Axiom Classification (7 total)

### Clay Core (1)
| Axiom | File | What it claims |
|-------|------|----------------|
| `balaban_rg_uniform_lsi` | BalabanToLSI | SU(N) Gibbs satisfies uniform LSI via Balaban RG |

### Physics Bridge (1)
| Axiom | File | What it claims |
|-------|------|----------------|
| `poincare_to_covariance_decay` | StroockZegarlinski | Poincaré λ → HasCovarianceDecay μ 2 (1/λ) |

### Physics Hypothesis (1)
| Axiom | File | What it claims |
|-------|------|----------------|
| `sun_lieb_robinson_bound` | SUN_LiebRobin | Lieb-Robinson velocity bound for SU(N) lattice |

### Mathlib Infrastructure Gaps (4)
| Axiom | File | Difficulty | Notes |
|-------|------|------------|-------|
| `bakry_emery_lsi` | BalabanToLSI | HIGH | CD(K,∞)⟹LSI(K) — Γ₂ calculus |
| `sun_bakry_emery_cd` | BalabanToLSI | HIGH | SU(N) satisfies CD(N/4,∞) |
| `hille_yosida_semigroup` | MarkovSemigroupDef | HIGH | Bundles 9 fields incl. spectral gap |

**Soundness note:** This axiom gives spectral gap for free from any strong Dirichlet form —
false in general (Brownian motion on ℝᵈ counterexample). Honest split exists in
`HilleYosidaDecomposition.lean`: hille_yosida_core (A+B) + poincare_to_variance_decay (C).
Decomposition is axiom-neutral. P8 unchanged pending Mathlib C₀-semigroup theory.
| `sunDirichletForm_contraction` | SUN_DirichletCore | MEDIUM | Truncation contraction — Lipschitz/weak derivative needed |

---

## Eliminated Axiom History (13 → 7)

| Axiom | Version | How |
|-------|---------|-----|
| `sz_lsi_to_clustering` (phantom) | v0.8.17 | Proved downstream |
| `lsi_implies_poincare_strong` (phantom) | v0.8.43 | Import cycle broken |
| `instFintypeLieGenIndex` | v0.8.45 | LieGenIndex := Fin (N_c^2-1) |
| `lieDerivative_const` | v0.8.48 | lieD'_const via lieDerivExp_const |
| `lieDerivative_linear` | v0.8.48 | lieD'_add + lieD'_smul via lieDerivExp |
| `sunDirichletForm_subadditive` | v0.8.49 | lieDerivReg_all + integral_mono + two_mul_le_add_sq |

---

## Next Target: sunDirichletForm_contraction

**Strategy:** Experimental spike first (never directly to P8).
**Challenge:** Truncation `min/max` breaks `DifferentiableAt` — needs Lipschitz or weak derivative.
**Alternative pivot:** `hille_yosida_semigroup` if contraction spike looks poor.

---

## Support Axioms (Experimental/LieSUN, not in P8 count)
| Axiom | File | Notes |
|-------|------|-------|
| `sunGeneratorData` | LieDerivReg_v4 | su(N) generator basis exists |
| `lieDerivReg_all` | LieDerivReg_v4 | All SU(N) functions satisfy LieDerivReg |
| `matExp_traceless_det_one` | LieExpCurve | det(exp(tX))=1, traceless X (Jacobi/Liouville) |

---

## Build Status
```
P8 axioms: 7 | P8 sorrys: 0 | Full build: OK
```
