# AXIOM_FRONTIER.md — v0.8.47

## P8 is proof-clean: 0 real sorrys.
## The remaining frontier is axiomatic, not incomplete proof scripts.
## The only mathematically essential open input is `balaban_rg_uniform_lsi`.
## Frontier is stable at 10 axioms after spike analysis.

Last updated: v0.8.47 (2026-03-18)
Build: 0 errors, 0 sorrys

---

## Axiom Classification

### Clay Core (1)
| Axiom | File | What it claims |
|-------|------|----------------|
| `balaban_rg_uniform_lsi` | BalabanToLSI | SU(N) Gibbs satisfies uniform LSI via Balaban RG |

**Removal path:** E26 paper series (17 papers, 29/29 audited). This is the Yang-Mills mass gap.

---

### Physics Bridge Axioms (1)
| Axiom | File | What it claims |
|-------|------|----------------|
| `poincare_to_covariance_decay` | StroockZegarlinski | Poincaré λ → HasCovarianceDecay μ 2 (1/λ) |

**Why genuine:** SZ 1992 spectral gap theorem. Connects Poincaré constant to static covariance decay.
Not derivable from `markov_to_covariance_decay` (dynamic, not static).

---

### Physics Hypotheses (1)
| Axiom | File | What it claims |
|-------|------|----------------|
| `sun_lieb_robinson_bound` | SUN_LiebRobin | Lieb-Robinson velocity bound for SU(N) lattice |

**Removal path:** Formalize Hastings-Koma theorem for SU(N) gauge theory.

---

### Mathlib Infrastructure Gaps (7)
| Axiom | File | Difficulty | Removal path |
|-------|------|------------|--------------|
| `bakry_emery_lsi` | BalabanToLSI | HIGH | CD(K,∞)⟹LSI(K) — Γ₂ calculus in Mathlib |
| `sun_bakry_emery_cd` | BalabanToLSI | HIGH | SU(N) satisfies CD(N/4,∞) — Bochner + LieGroup |
| `hille_yosida_semigroup` | MarkovSemigroupDef | HIGH* | MarkovSemigroup has 9 fields incl. spectral gap |
| `lieDerivative_linear` | SUN_DirichletCore | BLOCKED | Needs SU(N) smooth manifold + fun_prop measurability |
| `lieDerivative_const` | SUN_DirichletCore | BLOCKED | Same — lieDerivExp measurability not auto-provable |
| `sunDirichletForm_subadditive` | SUN_DirichletCore | BLOCKED | Depends on lieDerivative_linear |
| `sunDirichletForm_contraction` | SUN_DirichletCore | BLOCKED | Depends on lieDerivative properties |

**Note on hille_yosida_semigroup:** Initially classified MEDIUM. After audit, it bundles
existience + Markov properties + integrability + T_symm + spectral gap. Reclassified HIGH.

**Note on lieDerivative_* axioms:** Spike v3 (DirichletConcrete.lean) proved subadditivity
holds analytically under IsDiffAlong, but `fun_prop` cannot prove
`Measurable (fun U => lieDerivExp X hX htr f U)` automatically.
This requires SU(N) as a smooth manifold in Mathlib. Blocked until then.

---

## Eliminated Axioms (journey from 13 → 10)
| Axiom | Version | How |
|-------|---------|-----|
| `sz_lsi_to_clustering` (phantom) | v0.8.17 | Was proved downstream |
| `lsi_implies_poincare_strong` (phantom) | v0.8.43 | Was proved in LSItoSpectralGap L441; import cycle broken |
| `instFintypeLieGenIndex` | v0.8.45 | `LieGenIndex := Fin (N_c^2-1)` → `inferInstance` |

---

## Build Status
```
lake build           →  0 errors, 0 sorrys
grep ^axiom P8       →  10 axioms (see table above)
grep sorry P8        →  0 real sorrys
```

## Import Graph (cycle-free since v0.8.40)
```
StroockZegarlinski → LSItoSpectralGap → LSIDefinitions
                   → PoincareCovarianceRoadmap → MarkovVarianceDecay
BalabanToLSI → LSItoSpectralGap
SUN_DirichletCore → SUN_StateConstruction → SUN_Compact
```

## Spike Analysis (v0.8.47)
Experimental file: `YangMills/Experimental/LieSUN/DirichletConcrete.lean`

Proved (0 sorrys, 0 axioms beyond 2 generator axioms):
- `lieDeriv_const`: unconditional via `lieDerivExp_const`
- `lieDeriv_add`: under `IsDiffAlong` predicate
- `lieDeriv_smul`: under `IsDiffAlong` predicate
- `dirichletForm_subadditive`: with explicit integrability hypothesis

Blocker identified: `fun_prop` cannot prove `Measurable (fun U => lieDerivExp X hX htr f U)`
This requires SU(N) smooth manifold structure (not yet in Mathlib).
Eliminating the 4 `lieDerivative_*`/`sunDirichletForm_*` axioms requires net ≥ 0 new axioms.
Decision: keep 10-axiom frontier, do not integrate spike into P8.
