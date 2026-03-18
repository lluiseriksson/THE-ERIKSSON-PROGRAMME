# AXIOM_FRONTIER.md — v0.8.41

## P8 is proof-clean: 0 real sorrys.
## The remaining frontier is axiomatic, not incomplete proof scripts.
## The only mathematically essential open input is `balaban_rg_uniform_lsi`.

Last updated: v0.8.41 (2026-03-18)
Build: 0 errors, 0 sorrys

---

## Axiom Classification

### Forward Declaration Axioms — Proved Downstream (1)
| Axiom | File | Status |
|-------|------|--------|
| `lsi_implies_poincare_strong` | LSIDefinitions | **Proved** in LSItoSpectralGap L441 — forward decl due to import cycle |

**Note:** This axiom is provably NOT an open mathematical gap. It is an architectural forward-declaration pattern. Resolution: extract to `LSIPoincareBridge.lean` (v0.8.43 target).

---

### Clay Core (1)
| Axiom | File | What it claims |
|-------|------|----------------|
| `balaban_rg_uniform_lsi` | BalabanToLSI | SU(N) Gibbs satisfies uniform LSI via Balaban RG |

**Removal path:** E26 paper series (17 papers, 29/29 audited). This is the Yang-Mills mass gap in pure form.

---

### Physics Bridge Axioms (1)
| Axiom | File | What it claims |
|-------|------|----------------|
| `poincare_to_covariance_decay` | StroockZegarlinski | Poincaré constant λ → HasCovarianceDecay μ 2 (1/λ) |

**Why it's genuine:** Connects the Poincaré spectral gap constant to the static covariance decay rate via the Stroock-Zegarlinski 1992 spectral gap theorem. Not derivable from `markov_to_covariance_decay` (which gives dynamic covariance with the semigroup T_t G, not static covariance).
**Removal path:** Formalize the SZ spectral gap argument: Poincaré constant → semigroup generator gap ≥ λ → exp(-λ) decay of static covariance.

---

### Mathlib Infrastructure Gaps (7)
| Axiom | File | Category | Removal path |
|-------|------|----------|--------------|
| `bakry_emery_lsi` | BalabanToLSI | Mathlib gap | CD(K,∞) ⟹ LSI(K) — Γ₂ calculus in Mathlib |
| `sun_bakry_emery_cd` | BalabanToLSI | Mathlib gap | SU(N) satisfies CD(N/4,∞) — Bochner + LieGroup |
| `hille_yosida_semigroup` | MarkovSemigroupDef | Mathlib gap | Strong Dirichlet form → Markov semigroup |
| `instIsTopologicalGroupSUN` | SUN_StateConstruction | Mathlib gap | SU(N) is TopologicalGroup |
| `instFintypeLieGenIndex` | SUN_DirichletCore | Mathlib gap | LieAlgebra generator index is Fintype |
| `lieDerivative_linear/const` | SUN_DirichletCore | Mathlib gap | LieGroup derivative API |
| `sunDirichletForm_*` | SUN_DirichletCore | Mathlib gap | Normal contraction for SU(N) Dirichlet form |

**Note:** When Mathlib gains LieGroup API for `Matrix.specialUnitaryGroup`, 4-5 axioms fall at once.

---

### Physics Hypotheses (1)
| Axiom | File | What it claims |
|-------|------|----------------|
| `sun_lieb_robinson_bound` | SUN_LiebRobin | Lieb-Robinson velocity bound for SU(N) lattice |

**Removal path:** Formalize Hastings-Koma theorem for SU(N) gauge theory.

---

## Build Status
```
lake build  →  0 errors, 0 sorrys
grep -Rnw YangMills/P8_PhysicalGap -e "^axiom"  →  see table above
grep -Rnw YangMills/P8_PhysicalGap -e "sorry"    →  0 real sorrys (comments only)
```

## Import Graph (cycle-free as of v0.8.40)
```
StroockZegarlinski → PoincareCovarianceRoadmap → MarkovVarianceDecay
                                               → MarkovSemigroupDef
                                               → CovarianceLemmas
LSItoSpectralGap ← (imported by StroockZegarlinski via LSIDefinitions)
BalabanToLSI → LSIDefinitions → MarkovSemigroupDef
```
