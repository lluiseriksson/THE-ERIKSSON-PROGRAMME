# AXIOM_FRONTIER.md — v0.8.50 (COMPLETE)

## Status: FRONTIER FULLY MAPPED
## P8: 8 honest axioms, 0 real sorrys, full build green.
## All analytical/functional paths exhausted.
## Remaining live target: balaban_rg_uniform_lsi (Clay Millennium Problem).
## Clay Core Progress: Layer 0 (BlockSpin+FiniteBlocks) + Layer 1 (Polymers) complete.

Last updated: v0.8.50 (2026-03-18)

---

## The Complete Picture

### What we proved (eliminated as axioms)
| Theorem | Version | Method |
|---------|---------|--------|
| `sz_lsi_to_clustering` | v0.8.17 | Proved downstream |
| `lsi_implies_poincare_strong` | v0.8.43 | Import cycle broken |
| `instFintypeLieGenIndex` | v0.8.45 | LieGenIndex := Fin(N²-1) |
| `lieDerivative_const` | v0.8.48 | lieD'_const via lieDerivExp |
| `lieDerivative_linear` | v0.8.48 | lieD'_add + lieD'_smul |
| `sunDirichletForm_subadditive` | v0.8.49 | two_mul_le_add_sq + integral_mono |
| `hille_yosida_semigroup` (unsound) | v0.8.50 | Replaced by sound version |
| `sun_haar_lsi` | v0.8.x | THEOREM from M1+M2 decomposition |

### What remains (8 axioms)

#### Clay Core (1) — the Millennium Problem
| Axiom | Notes |
|-------|-------|
| `balaban_rg_uniform_lsi` | E26 paper series. Volume-independent LSI. Open mathematics. |

#### External Physics / Literature inputs (2) — requires external proofs
| Axiom | Notes |
|-------|-------|
| `poincare_to_covariance_decay` | SZ 1992 — static covariance decay from Poincaré |
| `sun_lieb_robinson_bound` | Hastings-Koma for SU(N) gauge theory |

#### Frozen — Functional Analysis infrastructure (5)
| Axiom | Blocker |
|-------|-------|
| `bakry_emery_lsi` | Γ₂/CD(K,∞) calculus not in Mathlib |
| `sun_bakry_emery_cd` | Bochner-Weitzenböck on Lie groups not in Mathlib |
| `hille_yosida_semigroup` | C₀-semigroup + generator domain theory not in Mathlib |
| `sunDirichletForm_contraction` | Beurling-Deny / weak derivative chain rule, net 0 |
| `sun_variance_decay` | Same C₀-semigroup gap as hille_yosida (Gronwall available but
t-differentiability of Var(T_t f) requires generator L — same blocker) |

---

## Soundness Architecture (v0.8.50)

### New structures introduced
- `SymmetricMarkovTransport`: Layer A+B — semigroup algebra + transport
- `HasVarianceDecay`: Layer C — spectral gap (Poincaré + Gronwall + generator)
- `MarkovSemigroup`: extends SymmetricMarkovTransport + HasVarianceDecay

### Fixed unsoundness
- `hille_yosida_semigroup` previously gave spectral gap for free from Dirichlet form
- This is FALSE: Brownian motion on ℝᵈ counterexample
- Fixed: now returns `SymmetricMarkovTransport` only (sound)

---

## Experimental Spikes (all documented)

| File | Verdict | Finding |
|------|---------|---------|
| `DirichletContraction` | NO-GO (net 0) | Beurling-Deny needs weak derivatives |
| `HilleYosidaDecomposition` | Soundness fix applied | 3-layer split |
| `BakryEmerySpike` | FROZEN | Mathlib has no Γ₂/CD |
| `VarianceDecayFromPoincare` | FROZEN | Gronwall available but t-diff needs generator L |

---

## Mathlib Watch List
Track these PRs/issues for future unblocking:
- `Mathlib.Analysis.Semigroup.C0Semigroup` — would unlock hille_yosida + sun_variance_decay
- `Mathlib.Geometry.Riemannian.BakryEmery` — would unlock bakry_emery_lsi + sun_bakry_emery_cd
- `Mathlib.Analysis.DirichletForm` — would connect Dirichlet forms to generators
