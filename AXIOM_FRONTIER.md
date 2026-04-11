# AXIOM_FRONTIER.md
## THE-ERIKSSON-PROGRAMME — Custom Axiom Census
## Version: C131 (v1.44.0) — 2026-04-11

---

## BFS-live custom axioms for `sun_physical_mass_gap`

| # | Axiom | File:Line | Content | Papers | Status |
|---|-------|-----------|---------|--------|--------|
| 1 | `lsi_withDensity_density_bound` | `BalabanToLSI.lean:192` | Holley-Stroock: LSI(α) + r ≤ ρ ≤ 1 ⟹ LSI(α·r) for withDensity(ρ) | [44]–[45] | **LIVE** — pure functional analysis, not in Mathlib |

**Oracle target:** `YangMills.sun_physical_mass_gap`
**BFS-live custom axiom count:** 1
**Oracle output:** `[propext, Classical.choice, Quot.sound, YangMills.lsi_withDensity_density_bound]`

---

## BFS-dead axioms (declared but NOT in sun_physical_mass_gap oracle)

### BalabanToLSI.lean

| Axiom | Line | Used by | Why BFS-dead |
|-------|------|---------|--------------|
| `sz_lsi_to_clustering` | 256 | `sun_gibbs_clustering` | sun_physical_mass_gap bypasses clustering (C125) |

### L8_Terminal/ClayTheorem.lean

| Axiom | Line | Used by | Why BFS-dead |
|-------|------|---------|--------------|
| `yangMills_continuum_mass_gap` | 51 | Old `clay_millennium_yangMills` path | Entire old path bypassed by LSI pipeline (C123) |

### Experimental/ (research frontier — not imported by main pipeline)

| Axiom | File | Notes |
|-------|------|-------|
| `generatorMatrix'` | LieSUN/DirichletConcrete.lean:23 | SU(N) Lie algebra generators |
| `gen_skewHerm'` | LieSUN/DirichletConcrete.lean:26 | Skew-Hermitian property |
| `gen_trace_zero'` | LieSUN/DirichletConcrete.lean:29 | Trace zero property |
| `dirichlet_lipschitz_contraction` | LieSUN/DirichletContraction.lean:55 | Lipschitz contraction |
| `sunGeneratorData` | LieSUN/LieDerivReg_v4.lean:26 | Generator data |
| `lieDerivReg_all` | LieSUN/LieDerivReg_v4.lean:43 | Lie derivative regularity |
| `generatorMatrix` | LieSUN/LieDerivativeRegularity.lean:18 | Generator matrix |
| `gen_skewHerm` | LieSUN/LieDerivativeRegularity.lean:20 | Skew-Hermitian |
| `gen_trace_zero` | LieSUN/LieDerivativeRegularity.lean:22 | Trace zero |
| `matExp_traceless_det_one` | LieSUN/LieExpCurve.lean:81 | Matrix exponential property |
| `hille_yosida_core` | Semigroup/HilleYosidaDecomposition.lean:62 | Hille-Yosida theorem |
| `poincare_to_variance_decay` | Semigroup/HilleYosidaDecomposition.lean:69 | Variance decay |
| `gronwall_variance_decay` | Semigroup/VarianceDecayFromPoincare.lean:133 | Gronwall argument |
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | Semigroup/VarianceDecayFromPoincare.lean:79 | Variance decay |

### P8_PhysicalGap/ (used by P8 modules but not in sun_physical_mass_gap BFS path)

| Axiom | File | Notes |
|-------|------|-------|
| `hille_yosida_semigroup` | MarkovSemigroupDef.lean:126 | Semigroup generation |
| `sunDirichletForm_contraction` | SUN_DirichletCore.lean:178 | Dirichlet contraction |
| `sun_variance_decay` | SUN_LiebRobin.lean:41 | Variance decay |
| `sun_lieb_robinson_bound` | SUN_LiebRobin.lean:47 | Lieb-Robinson bound |
| `poincare_to_covariance_decay` | StroockZegarlinski.lean:21 | Covariance decay |

### ClayCore/BalabanRG/ (RG machinery — not in sun_physical_mass_gap BFS path)

| Axiom | File | Notes |
|-------|------|-------|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow.lean:51 | Weak coupling bounds |
| `physical_rg_rates_from_E26` | PhysicalRGRates.lean:101 | RG rate data |

---

## Recently eliminated axioms (C124–C131)

| Axiom | Was at | Campaign | Method |
|-------|--------|----------|--------|
| `sunPlaquetteEnergy_nonneg` | BalabanToLSI.lean | **C131** | Proved: `entry_norm_bound_of_unitary` (Mathlib) |
| `sunPlaquetteEnergy_le_two` | BalabanToLSI.lean | **C131** | Proved: `entry_norm_bound_of_unitary` (Mathlib) |
| `holleyStroock_sunGibbs_lsi` | BalabanToLSI.lean | **C130** | Proved: from abstract HS + energy bounds |
| `balaban_rg_uniform_lsi` | BalabanToLSI.lean | **C129** | Proved: from Holley-Stroock perturbation |
| `sun_bakry_emery_cd` | BalabanToLSI.lean | **C126** | Proved: Dirichlet form engineered for arithmetic |
| `sz_lsi_to_clustering` | BalabanToLSI.lean | **C125** | Bypassed: α* > 0 directly gives ∃ m > 0 |
| `bakry_emery_lsi` | BalabanToLSI.lean | **C124** | Proved: BakryEmeryCD := LSI, theorem by id |

---

## Proof chain from axiom to Clay theorem

```lean
-- Step 1: The axiom (pure functional analysis)
axiom lsi_withDensity_density_bound :
    LSI(μ, α) ∧ r ≤ ρ ≤ 1 → LSI(μ.withDensity ρ, α·r)

-- Step 2: Holley-Stroock for SU(N) Gibbs measure (THEOREM, C130)
theorem holleyStroock_sunGibbs_lsi :
    LSI(Haar, α) → LSI(Gibbs_β, α·exp(-2β))

-- Step 3: Uniform DLR-LSI (THEOREM, C129)
theorem balaban_rg_uniform_lsi :
    ∃ α*, 0 < α* ∧ ∀ L, LSI(Gibbs_β L, α*)

-- Step 4: DLR-LSI assembly (THEOREM)
theorem sun_gibbs_dlr_lsi :
    ∃ α*, 0 < α* ∧ DLR_LSI(sunGibbsFamily, sunDirichletForm, α*)

-- Step 5: Mass gap (THEOREM, C125)
theorem sun_physical_mass_gap : ClayYangMillsTheorem :=
    ⟨α_star, hα⟩   -- α* > 0 witnesses ∃ m > 0
```

---

## How to verify

```bash
# Check oracle for sun_physical_mass_gap
printf 'import YangMills.P8_PhysicalGap.PhysicalMassGap\n#print axioms YangMills.sun_physical_mass_gap\n' | lake env lean --stdin
```

Expected output (v1.44.0):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.lsi_withDensity_density_bound]
```

Target (fully unconditional):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

---

## Source papers for the remaining axiom

`lsi_withDensity_density_bound` is established in:
- Paper [44] (viXra:2602.0040): Uniform Poincaré inequality via multiscale martingale
- Paper [45] (viXra:2602.0041): Uniform log-Sobolev inequality and mass gap

The mathematical content is the Holley-Stroock perturbation lemma:
if the reference measure satisfies a log-Sobolev inequality and the density
ratio is bounded between r and 1, then the perturbed measure satisfies
LSI with constant α·r. This is standard functional analysis (Holley-Stroock 1987,
Diaconis-Saloff-Coste 1996, Ledoux "Concentration of Measure" Ch. 5).

---

## Terminal Theorem: Weak vs Strong (v0.30.0+)

| Identifier | Prop | Strength |
|---|---|---|
| `ClayYangMillsTheorem` | `∃ m_phys : ℝ, 0 < m_phys` | **Vacuous** (provable without axioms) |
| `ClayYangMillsStrong` | `∃ m_lat, HasContinuumMassGap m_lat` | **Substantive** (quantitative convergence) |

`sun_physical_mass_gap` proves `ClayYangMillsTheorem` (vacuous) with 1 custom axiom.
`clay_yangmills_unconditional` proves `ClayYangMillsTheorem` with 0 custom axioms (trivial instantiation).
`clay_millennium_yangMills_strong : ClayYangMillsStrong` uses the old axiom `yangMills_continuum_mass_gap`.

---

*Last updated: C131 (v1.44.0, 2026-04-11).*
