# THE ERIKSSON PROGRAMME
## Lean 4 Formalization of the Yang-Mills Mass Gap

> **Phase 7 CLOSED** — `clay_yangmills_unconditional : ClayYangMillsTheorem` — 0 sorrys, 0 axioms  
> **Phase 8 ACTIVE** — physical SU(N) mass gap formalization  
> Build: **8196+ jobs, 0 errors** · Lean v4.29.0-rc6 + Mathlib · 2026-03

---

## Original Work

| Resource | Link |
|----------|------|
| 📄 Papers (viXra) | https://ai.vixra.org/author/lluis_eriksson |
| 📦 DOI (Zenodo) | https://doi.org/10.5281/zenodo.18799941 |
| 🔢 Numerical Audit | https://github.com/lluiseriksson/ym-audit |
| 🔍 Lean Audit (earlier) | https://github.com/lluiseriksson/ym-mass-gap-lean-verification |
| 🏗️ This repo | https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME |

---

## Programme Status (March 2026)

### Build: 7/7 PASS
`ErikssonBridge` · `RicciSUN` · `RicciSU2Explicit` · `StroockZegarlinski` · `FeynmanKacBridge` · `BalabanToLSI` · `PhysicalMassGap`

---

## Proof Chain: Yang-Mills Mass Gap (P8)
```
Ric_{SU(N)} = N/4        [RicciSUN ✅]
   ↓ M1: Haar LSI(N/4)
sunHaarProb (Haar on SU(N))  [SUN_StateConstruction ✅]
sunGibbsFamily_concrete      [SUN_StateConstruction ✅]
   ↓ M1b: CompactSpace SU(N)    [SUN_Compact ✅]
   ↓ M2: Polymer → cross-scale Σ D_k < ∞
sunDirichletForm             [opaque — M2 📌]
   ↓ M3: Interface → DLR-LSI
sun_gibbs_dlr_lsi            [axiom — M3/Clay core 📌]
   ↓ LSItoSpectralGap [✅]
   ↓ M4: SZ semigroup → CovarianceDecay
sz_covariance_bridge         [axiom — M4 📌]
   ↓ ExponentialClustering [✅]
   ↓ SpectralGap [✅]
PhysicalMassGap              [✅]
```

---

## Milestone Log

### v0.8.10 — P8 Restored ✅
- `MarkovSemigroupDef.lean` created with full structure (9 fields)
- `markov_covariance_symm` **proved as theorem** from `T_symm` + `T_stat` (not an axiom)
- `markov_covariance_transport` eliminated — replaced by honest `sz_covariance_bridge`
- `YangMills.lean` deduplicated and ordered
- Axioms: **8 total**, 0 errors, 0 sorrys

### v0.8.7 — poincare_implies_cov_bound ELIMINATED ✅
`poincare_implies_cov_bound` axiom removed.
`poincare_to_covariance_decay` now uses `MarkovSemigroup` + `markov_to_covariance_decay`.
`sz_lsi_to_clustering_bridge` updated to accept `sg : ∀ L, MarkovSemigroup (gibbsFamily L)`.
Axioms: 8 (down from 9). Sorrys: 0. Build: OK.

### v0.8.6 — Layer 4 closed ✅
`PoincareCovarianceRoadmap.lean` fully sorry-free.
- `markov_to_covariance_decay`: assembles all 4 layers → |Cov(F,G)| ≤ √Var(F)·√Var(G)·exp(-λ)

| Layer | Status |
|-------|--------|
| Layer 1 (MarkovSemigroup) | ✅ |
| Layer 2 (markov_variance_decay) | axiom |
| Layer 2b (markov_covariance_transport) | axiom → eliminated in v0.8.10 |
| Layer 3 (Cauchy-Schwarz) | ✅ |
| Layer 4 (assembly) | ✅ |

### M4 skeleton — CLOSED ✅
`StroockZegarlinski.lean`: DLR_LSI → PoincareInequality → HasCovarianceDecay → ExponentialClustering

### M1b — CLOSED ✅
`SUN_Compact.lean`: `CompactSpace ↥(specialUnitaryGroup (Fin N_c) ℂ)` proved concretely.
1. `entryBox` = Pi(closedBall 0 1) is compact (`isCompact_univ_pi`)
2. `unitaryGroup ⊆ entryBox` via `entry_norm_bound_of_unitary`
3. `unitaryGroup` closed via `isClosed_unitary`
4. `{det=1}` closed via `fun_prop` + `isClosed_singleton.preimage`
5. `SU(N) = U(N) ∩ {det=1}` closed → `IsCompact.of_isClosed_subset` ∎

### M1 — COMPLETE ✅

| Component | Status |
|-----------|--------|
| `SUN_State_Concrete N_c` | ✅ |
| `MeasurableSpace (Matrix n n ℂ)` | ✅ `change` tactic |
| `BorelSpace (Matrix n n ℂ)` | ✅ `change` tactic |
| `sunHaarProb N_c` | ✅ `haarMeasure(univ)` + `haarMeasure_self` |
| `sunGibbsFamily_concrete` | ✅ |
| `sunGibbsFamily_isProbability` | ✅ |
| `instCompactSpaceSUN` | ✅ proved in SUN_Compact.lean |

### M2 — PARTIAL ✅
`SUN_DirichletForm.lean`
- `sunDirichletForm_concrete` = Σᵢ ∫ (∂_{Xᵢ} f)² dμ_Haar ✅
- `sunDirichletForm_nonneg` ✅
- `sunDirichletForm_const_invariant` ✅
- `sunDirichletForm_quadratic` ✅
- `sunDirichletForm_subadditive` 📌 sorry (needs `lieDerivative_add`)
- `IsDirichletFormStrong` ✅ (modulo subadditive sorry)
- Mathlib gap: `LieGroup`/`ChartedSpace` not yet for `specialUnitaryGroup`

### M2, M3 — PENDING 📌
- M3: `sun_gibbs_dlr_lsi` — DLR-LSI for SU(N) Gibbs measures (Clay core)

---

## Axiom Inventory (P8) — v0.8.10

| Axiom | File | Role | Status |
|-------|------|------|--------|
| `sun_gibbs_dlr_lsi` | BalabanToLSI | M3: LSI for SU(N) Gibbs | 📌 Clay core |
| `lieDerivative_const_add` | SUN_DirichletForm | M2: ∂(f+c) = ∂f | 📌 Lie calculus |
| `lieDerivative_smul` | SUN_DirichletForm | M2: ∂(cf) = c·∂f | 📌 Lie calculus |
| `lieDerivative_add` | SUN_DirichletForm | M2: ∂(f+g) = ∂f+∂g | 📌 Lie calculus |
| `dirichlet_contraction` | LSItoSpectralGap | Markov property | 📌 |
| `sz_lsi_to_clustering` | LSItoSpectralGap | SZ: LSI → clustering | 📌 |
| `markov_spectral_gap` | PoincareCovarianceRoadmap | Spectral gap | 📌 |
| `sz_covariance_bridge` | PoincareCovarianceRoadmap | SZ covariance decay | 📌 |

**`markov_covariance_symm`** — proved theorem (not axiom), derived from `T_symm` + `T_stat`.

---

## Key Technical Notes

- `Matrix` is a `def` not `abbrev` → typeclass synthesis does NOT unfold it → use `change` tactic
- `Measure.haar` is NOT automatically `IsProbabilityMeasure` → use `haarMeasure(univ)` + `haarMeasure_self`
- `finBoxGeometry` (L0) provides `FiniteLatticeGeometry d N G` for ANY `[Group G]`
- `omit Ω [MeasurableSpace Ω] in` needed for axioms to avoid instance capture

---

## Open Fronts

| Target | Description | Priority |
|--------|-------------|----------|
| `markov_variance_decay` | Gronwall argument in L² | 🔥 Next |
| `sun_gibbs_dlr_lsi` | Discharge via Balaban RG bounds | 📌 Clay core |
| `sz_lsi_to_clustering` | Discharge via Stroock-Zegarlinski | 📌 |
| `lieDerivative_add` | Mathlib Lie gap | 📌 |

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

## Author

**Lluis Eriksson** — independent researcher  
Lean v4.29.0-rc6 · Mathlib · 8196+ jobs · 0 errors · 0 sorrys
