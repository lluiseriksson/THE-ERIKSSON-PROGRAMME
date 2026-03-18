# AXIOM_FRONTIER.md — v0.8.48

## P8 is proof-clean: 0 real sorrys.
## Frontier: 8 axioms (was 12 at start of session).
## Journey: 13 → 12 → 11 → 10 → 8

Last updated: v0.8.48 (2026-03-18)
Build: 0 errors, 0 sorrys

---

## Axiom Classification — P8 (8 total)

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

### Mathlib Infrastructure Gaps (5)
| Axiom | File | Difficulty | Notes |
|-------|------|------------|-------|
| `bakry_emery_lsi` | BalabanToLSI | HIGH | CD(K,∞)⟹LSI(K) — Γ₂ calculus |
| `sun_bakry_emery_cd` | BalabanToLSI | HIGH | SU(N) satisfies CD(N/4,∞) |
| `hille_yosida_semigroup` | MarkovSemigroupDef | HIGH | Bundles 9 fields incl. spectral gap |
| `sunDirichletForm_contraction` | SUN_DirichletCore | MEDIUM | Normal contraction — lieDerivative chain rule |
| `lieDerivReg_all` | (via LieDerivReg_v4) | MEDIUM | All SU(N) functions satisfy LieDerivReg |

Note: `sunGeneratorData` lives in Experimental/LieSUN and is used by lieDerivReg package.

---

## Eliminated Axiom History

| Axiom | Version | How |
|-------|---------|-----|
| `sz_lsi_to_clustering` (phantom) | v0.8.17 | Proved downstream |
| `lsi_implies_poincare_strong` (phantom) | v0.8.43 | Import cycle broken |
| `instFintypeLieGenIndex` | v0.8.45 | LieGenIndex := Fin (N_c^2-1) |
| `lieDerivative_const` | v0.8.48 | lieD'_const via lieDerivExp_const |
| `lieDerivative_linear` | v0.8.48 | lieD'_add + lieD'_smul via lieDerivExp |
| `sunDirichletForm_subadditive` | v0.8.48 | dirichletForm''_subadditive |

---

## Support Axioms (Experimental, not in P8 count)
| Axiom | File | Notes |
|-------|------|-------|
| `sunGeneratorData` | LieDerivReg_v4 | su(N) generator basis exists |
| `matExp_traceless_det_one` | LieExpCurve | det(exp(tX))=1, traceless X |

---

## Build
```
P8 axioms: 8 | P8 sorrys: 0 | Full build: OK
```
