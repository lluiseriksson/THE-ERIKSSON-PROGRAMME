# AXIOM_FRONTIER.md — v0.8.50

## P8 is proof-clean: 0 real sorrys.
## Frontier: 8 axioms (honest). Previous: 7 axioms (1 was logically unsound).
## Journey: 13 → 12 → 11 → 10 → 8 → 7 → 8*

*Count went 7→8 in v0.8.50 soundness refactor: replaced 1 unsound axiom
with 2 honest ones (hille_yosida_semigroup now sound + sun_variance_decay new).

Last updated: v0.8.50 (2026-03-18)
Build: 0 errors, 0 sorrys

---

## The Soundness Fix (v0.8.50)

**Before:** `hille_yosida_semigroup : IsDirichletFormStrong E μ → MarkovSemigroup μ`
This claimed spectral gap from Dirichlet form alone. FALSE in general.
(Brownian motion on ℝᵈ: strong Dirichlet form, no spectral gap.)

**After:** Two honest axioms:
- `hille_yosida_semigroup : IsDirichletFormStrong E μ → SymmetricMarkovTransport μ`
  (Layer A+B: semigroup existence + transport. NO spectral gap.)
- `sun_variance_decay : HasVarianceDecay (sunMarkovSemigroup N_c)`
  (Layer C: spectral gap for SU(N) specifically, from Poincaré.)

**New structures:**
- `SymmetricMarkovTransport`: Layer A+B (T, algebra, stat, integrable, symm)
- `HasVarianceDecay`: Layer C (exponential variance decay, Poincaré + Gronwall)
- `MarkovSemigroup`: extends SymmetricMarkovTransport + HasVarianceDecay (unchanged API)

---

## P8 Axiom Classification (8 total)

### Clay Core (1)
| Axiom | File | Status |
|-------|------|--------|
| `balaban_rg_uniform_lsi` | BalabanToLSI | E26 paper series |

### Physics Bridge (1)
| Axiom | File | Status |
|-------|------|--------|
| `poincare_to_covariance_decay` | StroockZegarlinski | SZ 1992 |

### Physics Hypotheses (2)
| Axiom | File | Status |
|-------|------|--------|
| `sun_lieb_robinson_bound` | SUN_LiebRobin | Hastings-Koma for SU(N) |
| `sun_variance_decay` | SUN_LiebRobin | Poincaré→Gronwall→gap for SU(N) |

### Mathlib Infrastructure Gaps (4)
| Axiom | File | Difficulty | Notes |
|-------|------|------------|-------|
| `bakry_emery_lsi` | BalabanToLSI | HIGH | CD(K,∞)⟹LSI(K) |
| `sun_bakry_emery_cd` | BalabanToLSI | HIGH | SU(N) satisfies CD(N/4,∞) |
| `hille_yosida_semigroup` | MarkovSemigroupDef | HIGH | Dirichlet → SymmetricMarkovTransport |
| `sunDirichletForm_contraction` | SUN_DirichletCore | MEDIUM | Beurling-Deny, net 0 |

---

## Eliminated Axiom History (13 → 8 honest)

| Axiom | Version | Method |
|-------|---------|--------|
| `sz_lsi_to_clustering` (phantom) | v0.8.17 | Proved downstream |
| `lsi_implies_poincare_strong` (phantom) | v0.8.43 | Import cycle broken |
| `instFintypeLieGenIndex` | v0.8.45 | LieGenIndex := Fin(N²-1) |
| `lieDerivative_const` | v0.8.48 | lieD'_const via lieDerivExp |
| `lieDerivative_linear` | v0.8.48 | lieD'_add + lieD'_smul |
| `sunDirichletForm_subadditive` | v0.8.49 | two_mul_le_add_sq + integral_mono |
| `hille_yosida_semigroup` (unsound) | v0.8.50 | Replaced by sound version |

---

## Experimental Findings

### DirichletContraction (net 0 — do not integrate)
Beurling-Deny gap: DifferentiableAt fails at kinks ±n.
Route B axiom = 1 IN, 1 OUT. sunDirichletForm_contraction stays.

### HilleYosidaDecomposition (soundness fix applied to P8)
3-layer split: Core(A) + Transport(B) + HasVarianceDecay(C).
poincare_to_variance_decay is genuinely new (not same as poincare_to_covariance_decay).

---

## Next Session Priorities

1. **Bakry-Émery spike** — `bakry_emery_lsi` + `sun_bakry_emery_cd`
   - Related axioms, may fall together
   - Inspect current Mathlib for CD(K,∞) machinery

2. **sun_variance_decay removal path**
   - Formalise: LSI → Poincaré → Gronwall → HasVarianceDecay for SU(N)
   - poincare_to_covariance_decay already established — bridge exists in principle

3. **Mathlib watch**
   - C₀-semigroup theory → hille_yosida_semigroup
   - Bakry-Émery/Γ₂ calculus → bakry_emery_lsi, sun_bakry_emery_cd
