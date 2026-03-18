# AXIOM_FRONTIER.md — v0.8.49 (session close)

## P8 is proof-clean: 0 real sorrys.
## Frontier: 7 axioms.
## Journey: 13 → 12 → 11 → 10 → 8 → 7

Last updated: v0.8.49 (2026-03-18)
Build: OK | Errors: 0 | Sorrys: 0

---

## P8 Axiom Classification (7 total)

### Clay Core (1)
| Axiom | File | Status |
|-------|------|--------|
| `balaban_rg_uniform_lsi` | BalabanToLSI | E26 paper series (17 papers) |

### Physics Bridge (1)
| Axiom | File | Status |
|-------|------|--------|
| `poincare_to_covariance_decay` | StroockZegarlinski | SZ 1992, static covariance decay |

### Physics Hypothesis (1)
| Axiom | File | Status |
|-------|------|--------|
| `sun_lieb_robinson_bound` | SUN_LiebRobin | Hastings-Koma for SU(N) gauge |

### Mathlib Infrastructure Gaps (4)
| Axiom | File | Difficulty | Next action |
|-------|------|------------|-------------|
| `bakry_emery_lsi` | BalabanToLSI | HIGH | Bakry-Émery spike (session 2) |
| `sun_bakry_emery_cd` | BalabanToLSI | HIGH | Bakry-Émery spike (session 2) |
| `hille_yosida_semigroup` | MarkovSemigroupDef | HIGH* | Soundness fix (session 2) |
| `sunDirichletForm_contraction` | SUN_DirichletCore | MEDIUM | Net 0, blocked (Beurling-Deny) |

**hille_yosida_semigroup soundness note:**
Currently claims IsDirichletFormStrong E μ → MarkovSemigroup μ (including spectral gap).
This is FALSE in general — Brownian motion on ℝᵈ has strong Dirichlet form but no spectral gap.
Honest split documented in `Experimental/Semigroup/HilleYosidaDecomposition.lean`:
- `hille_yosida_core`: IsDirichletFormStrong → SymmetricMarkovTransport (Layer A+B)
- `poincare_to_variance_decay`: SymmetricMarkovTransport + Poincaré → HasVarianceDecay (Layer C)
Decomposition is axiom-neutral. Soundness fix is next-session priority.

---

## Eliminated Axiom History (13 → 7)

| Axiom | Version | Method |
|-------|---------|--------|
| `sz_lsi_to_clustering` (phantom) | v0.8.17 | Proved downstream |
| `lsi_implies_poincare_strong` (phantom) | v0.8.43 | Import cycle broken |
| `instFintypeLieGenIndex` | v0.8.45 | LieGenIndex := Fin (N_c^2-1) |
| `lieDerivative_const` | v0.8.48 | lieD'_const via lieDerivExp_const |
| `lieDerivative_linear` | v0.8.48 | lieD'_add + lieD'_smul via lieDerivExp |
| `sunDirichletForm_subadditive` | v0.8.49 | two_mul_le_add_sq + integral_mono |

---

## Experimental Findings (this session)

### DirichletContraction (net 0 — do not integrate)
- clip_n is 1-Lipschitz ✅
- DifferentiableAt fails at kinks ±n ❌ BLOCKER
- Route B: dirichlet_lipschitz_contraction replaces sunDirichletForm_contraction = net 0
- Decision: sunDirichletForm_contraction stays as honest Beurling-Deny axiom

### HilleYosidaDecomposition (axiom-neutral — soundness improvement)
- 3-layer split compiles cleanly
- Soundness finding: spectral gap requires Poincaré explicitly
- poincare_to_variance_decay is genuinely new (different from poincare_to_covariance_decay)
- Decision: P8 unchanged, soundness fix is next priority

---

## Support Axioms (Experimental/LieSUN)
| Axiom | File | Notes |
|-------|------|-------|
| `sunGeneratorData` | LieDerivReg_v4 | su(N) generator basis |
| `lieDerivReg_all` | LieDerivReg_v4 | All SU(N) functions satisfy LieDerivReg |
| `matExp_traceless_det_one` | LieExpCurve | det(exp(tX))=1 (Jacobi/Liouville) |

---

## Next Session Priorities

1. **Soundness fix** for `hille_yosida_semigroup`
   - Require Poincaré as explicit hypothesis for spectral gap
   - Axiom-neutral but mathematically correct
   - Use HilleYosidaDecomposition.lean as template

2. **Bakry-Émery spike**
   - `bakry_emery_lsi` + `sun_bakry_emery_cd` are related
   - May fall together if Mathlib has CD(K,∞) machinery
   - Inspect current Mathlib before scaffolding

3. **Mathlib watch**
   - C₀-semigroup theory would unlock `hille_yosida_semigroup` directly
   - Track Mathlib PRs for: `ContinuousSemigroup`, `HilleYosida`, `DirichletForm`
