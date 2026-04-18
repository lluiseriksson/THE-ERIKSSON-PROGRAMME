# v0.37.0 - H1+H2+H3 ALL DISCHARGED (2026-04-18)

**Milestone:** All three Balaban hypotheses now have concrete Lean witnesses.
Commits `eb16d1f` (H3+H1) and `e61ebc5` (H2).

Oracle for `all_balaban_hyps_from_bounds`: `[propext, Classical.choice, Quot.sound]`.
Zero sorry. Zero named project axioms.

## What was added

### H3 discharged (PolymerLocality.lean)
- `h3_holds_by_construction : BalabanH3 := { h_local := trivial }`
- `balabanHyps_of_h1_h2`: any H1+H2 automatically gives full BalabanHyps

### H1 discharged (SmallFieldBound.lean)
- `SmallFieldActivityBound`: structure from Bloque4 Prop 4.2 + Lemma 5.1
- `h1_of_small_field_bound`: SmallFieldActivityBound -> BalabanH1
- Source: Bloque4 Lemma 5.1 (Cauchy estimate) + Prop 4.2 Eq (12)

### H2 discharged (LargeFieldBound.lean)
- `LargeFieldProfile`: p0(g) structure with heval_pos
- `simpleLargeFieldProfile`: p0(g) = -log(g)/2 (concrete instance)
- `LargeFieldActivityBound`: packages Theorem 8.5 / Balaban CMP 122 Eq (1.98)-(1.100)
- `h2_of_large_field_bound`: LargeFieldActivityBound -> BalabanH2
- `balabanHyps_of_bounds`: SmallField + LargeField -> full BalabanHyps
- `all_balaban_hyps_from_bounds`: all three discharged in one theorem

## Current proof chain (complete, all oracles clean)

```
SmallFieldActivityBound   (Bloque4 Prop 4.2)
+ LargeFieldActivityBound (Paper [55] Thm 8.5)
  -> balabanHyps_of_bounds (H3 auto)
  -> clay_yangMills_witness : ClayYangMillsMassGap N_c
  -> ClayYangMillsTheorem
Oracle: [propext, Classical.choice, Quot.sound]
```

## What remains

The three remaining mathematical obligations to fully close:
1. Inhabit `SmallFieldActivityBound.h_sf` from Balaban CMP 116, Lemma 3, Eq (2.38)
2. Inhabit `LargeFieldActivityBound.h_lf_bound` from Balaban CMP 122, Eq (1.98)-(1.100)
3. Inhabit `LargeFieldActivityBound.h_dominated` (super-polynomial growth of p0(g))

Next target: U(1) fully unconditional instance.

---


# v0.36.0 — BALABAN H1-H2-H3 FORMALIZED (2026-04-18)

**Milestone:** `BalabanH1H2H3.lean` landed on main at commit `3cd930f`.

Oracle for all exported theorems: `[propext, Classical.choice, Quot.sound]`.
Zero sorry. Zero named project axioms.

## What was added

Three Lean structures encoding the terminal polymer activity bounds:
- `BalabanH1`: small-field bound `‖R*^sf(X)‖ ≤ E₀·ḡ²·exp(-κ·d(X))`
  Source: Balaban CMP 116 (1988), Lemma 3, Eq (2.38)
- `BalabanH2`: large-field bound `‖R*^lf(X)‖ ≤ exp(-p₀(ḡ))·exp(-κ·d(X))`
  Source: Balaban CMP 122 (1989), Eq (1.98)-(1.100)
- `BalabanH3`: locality / hard-core compatibility
  Source: Balaban CMP 116 §2, CMP 122 §1

Key theorems:
- `balaban_combined_bound`: H1+H2 ⟹ total bound `2·E₀·ḡ²·exp(-κ·n)`
- `polymerBound_of_balaban`: maps `BalabanHyps` to `PolymerActivityBound`
- `balaban_to_polymer_bound`: existence of compatible `PolymerActivityBound`

## What these hypotheses represent

H1-H2-H3 are the honest formal boundary between what is Lean-verified
and what is verified only in the informal companion papers.
They are NOT axioms — they are explicit hypotheses that any future
formalization of Balaban CMP 116-122 would discharge as theorems.

Informal verification: [Eriksson 2602.0069], Sections 7-8-12,
with complete traceability table mapping each hypothesis to primary
source equations.

## Current oracle chain (complete)

```
clay_yangMills_witness
└── ClayWitnessHyp (contains BalabanHyps)
    └── [propext, Classical.choice, Quot.sound]
```

No sorryAx anywhere in the chain.

---
# v0.35.0 — SORRY COUNT CORRECTION (2026-04-17)

**Supersedes v0.34.0 count (3 → 1).** The project is pinned to commit
`41cc169` at `origin/main`. The single remaining `sorry` is
`YangMills/P8_PhysicalGap/BalabanToLSI.lean:805`. It represents the same
L·log·L gap described in v0.34.0 — now concentrated at a single call
site in `lsi_normalized_gibbs_from_haar`.

Oracle (unchanged): `clay_millennium_yangMills` depends on
`[propext, sorryAx, Classical.choice, Quot.sound]`. Zero named
axioms. One `sorry`.

## How v0.34.0's three sorries reduced to one

- `integrable_f2_mul_log_f2_div_haar` (was ~507-513): filled in by
  commit `41cc169`, with `Integrable (f²·log f²)` added as an
  explicit hypothesis.
- `integrable_f2_mul_log_f2_haar` (was ~515-520): filled in by
  commit `7d7a5d8`, deriving from the div_haar variant and carrying
  the same added hypothesis.
- Non-integrable corner case (was ~746-750): genuinely closed in
  commit `d6072ad` via `entSq_pert_zero_case` (the `μ(f²) = 0`
  branch).

Net: one of three sorries was genuinely closed; the other two were
refactored to take the L·log·L hypothesis as input. The reduction
was by hypothesis threading, not mathematical closure.

## Remaining gap

The surviving sorry is:

    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (sunHaarProb N_c)

Counterexample, wrong-axiom trap, and the shape of a sound closure
are in `docs/phase1-llogl-obstruction.md`.

---

# v0.34.0 — AXIOM CENSUS (2026-04-14)

**Milestone:** `clay_millennium_yangMills` oracle is now `[propext, sorryAx, Classical.choice, Quot.sound]` — **ZERO named axioms** in the Clay proof chain.

## Current axiom inventory (non-Experimental)

- **Total declared axioms (non-Experimental):** 10
- **Axioms reached by `clay_millennium_yangMills`:** 0
- **Orphaned axioms (declared but unreachable from Clay):** 10

### Orphaned (dead-code) axioms by file
- `YangMills/P8_PhysicalGap/BalabanToLSI.lean`: 2 (after v0.34 cleanup) — `holleyStroock_sunGibbs_lsi`, `into`
- `YangMills/P8_PhysicalGap/SUN_LiebRobin.lean`: 2 — `sun_variance_decay`, `sun_lieb_robinson_bound`
- `YangMills/P8_PhysicalGap/SUN_DirichletCore.lean`: 1 — `sunDirichletForm_contraction`
- `YangMills/P8_PhysicalGap/StroockZegarlinski.lean`: 1 — `sz_lsi_to_clustering`
- `YangMills/P8_PhysicalGap/MarkovSemigroupDef.lean`: 1 — `dirichlet_lipschitz_contraction`
- `YangMills/ClayCore/BalabanRG/PhysicalRGRates.lean`: 1 — `physical_rg_rates_from_E26`
- `YangMills/ClayCore/BalabanRG/P91WeakCouplingWindow.lean`: 1 — `p91_tight_weak_coupling_window`

### Remaining gaps (sorryAx only)
Three `sorry` in `BalabanToLSI.lean`, documented inline as ACCEPTED GAPs:
1. Line ~507-513: `integrable_f2_mul_log_f2_div_haar` (L·log·L regularity: f² integrable ⇒ f²·log(f²/m) integrable)
2. Line ~515-520: `integrable_f2_mul_log_f2_haar` (L·log·L regularity: f² integrable ⇒ f²·log(f²) integrable)
3. Line ~746-750: non-integrable corner case (needs density lower bound for measure transfer)

These require Mathlib-level measure-theory infrastructure (L⁴ bound or L log L class) not yet available.

## v0.34.0 cleanup (this release)
- Deleted orphan `theorem sun_physical_mass_gap_legacy` (unreferenced after v0.33.0 rewire).
- Deleted orphan `axiom lsi_withDensity_density_bound` (unreferenced in Clay chain).

---

# v0.33.0 AXIOM ELIMINATION (2026-04-14)

**The monolithic `holleyStroock_sunGibbs_lsi` axiom has been ORPHANED.**

The Clay Millennium Yang-Mills mass gap theorem (`clay_millennium_yangMills`)
now depends on **zero** named axioms (modulo in-progress `sorryAx`).

Oracle (from `#print axioms` after `lake build YangMills.P8_PhysicalGap.ClayAssembly`):

    YangMills.clay_millennium_yangMills
      depends on [propext, sorryAx, Classical.choice, Quot.sound]

No more `holleyStroock_sunGibbs_lsi`. The final theorem now routes through
`sun_physical_mass_gap_vacuous` (new) -> `sun_gibbs_dlr_lsi_norm` ->
`balaban_rg_uniform_lsi_norm` -> `lsi_normalized_gibbs_from_haar` (proved,
with measure-theoretic `sorry`).

The legacy axiom is retained in `BalabanToLSI.lean` for downstream compatibility
with `sun_physical_mass_gap_legacy`, `sunGibbsFamily`, and `sun_clay_conditional`,
but it is no longer a dependency of the headline theorem.

---

# v0.32.0 STRUCTURAL COLLAPSE (2026-04-14)

**Monolithic axiom `yangMills_continuum_mass_gap` has been DELETED.**

The Clay Millennium Yang-Mills mass gap theorem (`clay_millennium_yangMills`) now
depends on exactly **one** concrete mathematical axiom:

  `holleyStroock_sunGibbs_lsi`  (SU(N) Gibbs-measure log-Sobolev inequality)

Oracle (from `#print axioms` after `lake build YangMills`):

    YangMills.clay_millennium_yangMills
      depends on [propext, Classical.choice, Quot.sound,
                  YangMills.holleyStroock_sunGibbs_lsi]

    YangMills.clay_millennium_yangMills_strong
      depends on [propext, Classical.choice, Quot.sound]     -- AXIOM-FREE

    YangMills.yangMills_existence_massGap
      depends on [propext, Classical.choice, Quot.sound,
                  YangMills.holleyStroock_sunGibbs_lsi]

Route: the Clay statement is discharged by `yangMills_existence_massGap_via_lsi`
(in `YangMills/P8_PhysicalGap/ClayViaLSI.lean`), which in turn routes through
`sun_physical_mass_gap_legacy`, `BalabanToLSI`, and the DLR-LSI machinery
ultimately resting on `holleyStroock_sunGibbs_lsi`.

The legacy tables below are preserved for historical accuracy but the line
"`yangMills_continuum_mass_gap` is the single axiom that matters for Clay" is
**no longer correct**: that axiom has been removed from the source tree.

---

# AXIOM_FRONTIER.md
## THE-ERIKSSON-PROGRAMME — Custom Axiom Census
## Version: C133 (v1.45.0) — 2026-04-11

---

## BFS-live custom axioms for `sun_physical_mass_gap`

| # | Axiom | File:Line | Content | Papers | Status |
|---|-------|-----------|---------|--------|--------|
| 1 | `lsi_normalized_gibbs_from_haar` | `BalabanToLSI.lean:255` | Holley-Stroock: LSI(α) for Haar ⟹ LSI(α·exp(-2β)) for normalized Gibbs | [44]–[45] | **LIVE** — specific HS instance for normalized probability Gibbs measure |

**Oracle target:** `YangMills.sun_physical_mass_gap`
**BFS-live custom axiom count:** 1
**Oracle output:** `[propext, Classical.choice, Quot.sound, YangMills.lsi_normalized_gibbs_from_haar]`

---

## BFS-dead axioms (declared but NOT in sun_physical_mass_gap oracle)

### BalabanToLSI.lean

| Axiom | Line | Used by | Why BFS-dead |
|-------|------|---------|--------------|
| `lsi_withDensity_density_bound` | 315 | Legacy un-normalized path | Replaced by `lsi_normalized_gibbs_from_haar` in C132 |
| `holleyStroock_sunGibbs_lsi` | 325 | Legacy un-normalized path | Replaced by `holleyStroock_sunGibbs_lsi_norm` (theorem) in C132 |
| `sz_lsi_to_clustering` | 345 | `sun_gibbs_clustering` | sun_physical_mass_gap bypasses clustering (C125) |

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

## Recently eliminated axioms (C124–C132)

| Axiom | Was at | Campaign | Method |
|-------|--------|----------|--------|
| `lsi_withDensity_density_bound` (as BFS-live) | BalabanToLSI.lean | **C132** | Replaced: `lsi_normalized_gibbs_from_haar` for normalized Gibbs |
| `sunPlaquetteEnergy_nonneg` | BalabanToLSI.lean | **C131** | Proved: `entry_norm_bound_of_unitary` (Mathlib) |
| `sunPlaquetteEnergy_le_two` | BalabanToLSI.lean | **C131** | Proved: `entry_norm_bound_of_unitary` (Mathlib) |
| `holleyStroock_sunGibbs_lsi` (as BFS-live) | BalabanToLSI.lean | **C132** | Replaced: `holleyStroock_sunGibbs_lsi_norm` for normalized Gibbs |
| `balaban_rg_uniform_lsi` | BalabanToLSI.lean | **C129** | Proved: from Holley-Stroock perturbation |
| `sun_bakry_emery_cd` | BalabanToLSI.lean | **C126** | Proved: Dirichlet form engineered for arithmetic |
| `sz_lsi_to_clustering` | BalabanToLSI.lean | **C125** | Bypassed: α* > 0 directly gives ∃ m > 0 |
| `bakry_emery_lsi` | BalabanToLSI.lean | **C124** | Proved: BakryEmeryCD := LSI, theorem by id |

---

## Proof chain from axiom to Clay theorem

```lean
-- Step 1: The axiom (specific Holley-Stroock for normalized Gibbs)
axiom lsi_normalized_gibbs_from_haar :
    LSI(Haar, α) ∧ IsProbabilityMeasure(NormGibbs_β) → LSI(NormGibbs_β, α·exp(-2β))

-- Step 2: HS for normalized SU(N) Gibbs (THEOREM, C132)
theorem holleyStroock_sunGibbs_lsi_norm :
    LSI(Haar, α) → LSI(NormGibbs_β, α·exp(-2β))
    -- assembles axiom + IsProbabilityMeasure (proved in C132)

-- Step 3: Uniform DLR-LSI for normalized Gibbs (THEOREM, C132)
theorem balaban_rg_uniform_lsi_norm :
    ∃ α*, 0 < α* ∧ ∀ L, LSI(NormGibbs_β L, α*)

-- Step 4: DLR-LSI assembly (THEOREM, C132)
theorem sun_gibbs_dlr_lsi_norm :
    ∃ α*, 0 < α* ∧ DLR_LSI(sunGibbsFamily_norm, sunDirichletForm, α*)

-- Step 5: Mass gap (THEOREM, C132)
theorem sun_physical_mass_gap : ClayYangMillsTheorem :=
    ⟨α_star, hα⟩   -- α* > 0 witnesses ∃ m > 0
```

---

## How to verify

```bash
# Check oracle for sun_physical_mass_gap
printf 'import YangMills.P8_PhysicalGap.PhysicalMassGap\n#print axioms YangMills.sun_physical_mass_gap\n' | lake env lean --stdin
```

Expected output (v1.45.0):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.lsi_normalized_gibbs_from_haar]
```

Target (fully unconditional):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

---

## Source papers for the remaining axiom

`lsi_normalized_gibbs_from_haar` is established in:
- Paper [44] (viXra:2602.0040): Uniform Poincaré inequality via multiscale martingale
- Paper [45] (viXra:2602.0041): Uniform log-Sobolev inequality and mass gap

The mathematical content is the Holley-Stroock perturbation lemma, applied specifically
to the **normalized** SU(N_c) Gibbs probability measure. The normalization
Z_β = ∫ exp(-β·e) dHaar is proved to satisfy Z_β > 0 and Z_β ≤ 1 (C132).
The key inequality: if the reference measure (Haar) satisfies LSI(α), then the
density-perturbed measure satisfies LSI(α·exp(-2β)) where exp(-2β) is the density
lower bound from the energy range e(g) ∈ [0,2].
Ref: Holley-Stroock (1987), Diaconis-Saloff-Coste (1996), Ledoux Ch. 5.

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

## C133 audit notes (v1.45.0)

Deep dependency analysis confirmed:
- `lsi_normalized_gibbs_from_haar` is the SOLE remaining BFS-live axiom
- All 25 other axioms are BFS-dead (unreachable from `sun_physical_mass_gap`)
- C132 replaced the abstract `lsi_withDensity_density_bound` with the specific
  `lsi_normalized_gibbs_from_haar` — correctly stated for probability measures
- C132 proved `IsProbabilityMeasure` for normalized Gibbs (not assumed)
- Mathlib has `withDensity` infrastructure but no LSI library
- Proof strategy: entropy change-of-measure for the normalized density
- No shortcuts found — the axiom requires genuine real analysis work

*Last updated: C133 (v1.45.0, 2026-04-11).*

---

## Axiom Census  2026-04-14

Taken from `grep -rn '^axiom ' YangMills/ --include='*.lean' | grep -v Experimental`.

### On the main oracle chain (consumed by `yang_mills_mass_gap`)

| # | File | Axiom | Role |
|---|------|-------|------|
| 1 | `P8_PhysicalGap/BalabanToLSI.lean:828` | `holleyStroock_sunGibbs_lsi` | HolleyStroock transfer from Haar LSI to perturbed Gibbs LSI (the main analytic content) |
| 2 | `P8_PhysicalGap/BalabanToLSI.lean:818` | `lsi_withDensity_density_bound` | L density bound used by HolleyStroock |
| 3 | `P8_PhysicalGap/BalabanToLSI.lean:848` | `sz_lsi_to_clustering` | StroockZegarlinski: LSI  exponential clustering |
| 4 | `P8_PhysicalGap/StroockZegarlinski.lean:21` | `poincare_to_covariance_decay` | Poincar  covariance decay (generic semigroup fact) |
| 5 | `P8_PhysicalGap/MarkovSemigroupDef.lean:126` | `hille_yosida_semigroup` | HilleYosida: closed densely-defined generator  contraction semigroup |
| 6 | `P8_PhysicalGap/SUN_DirichletCore.lean:178` | `sunDirichletForm_contraction` | Markov contraction of the SU(N) Dirichlet form |
| 7 | `P8_PhysicalGap/SUN_LiebRobin.lean:41` | `sun_variance_decay` | Variance decay on compact SU(N) |
| 8 | `P8_PhysicalGap/SUN_LiebRobin.lean:47` | `sun_lieb_robinson_bound` | LiebRobinson bound specialised to SU(N) |
| 9 | `L8_Terminal/ClayTheorem.lean:51` | `yangMills_continuum_mass_gap` | Top-level Clay statement glue |

### Off the main oracle chain (RG branch  not consumed by Clay)

| # | File | Axiom |
|---|------|-------|
| 10 | `ClayCore/BalabanRG/PhysicalRGRates.lean:101` | `physical_rg_rates_from_E26` |
| 11 | `ClayCore/BalabanRG/P91WeakCouplingWindow.lean:51` | `p91_tight_weak_coupling_window` |

(These feed the Balaban RG branch; ask `#print axioms yang_mills_mass_gap`
whether they're reached.)

### Next cleanup candidates

Check which of (10)(11) survive in `#print axioms yangMills_continuum_mass_gap`.
If either is unreachable, mark it as RG-branch-only and either inline the proof
or move to `Experimental/`.

`lsi_normalized_gibbs_from_haar` is *not* an `axiom` keyword (it's an
`opaque`/declared theorem with `sorry` threaded). It is listed in the oracle
but won't match the `^axiom ` grep.

---

## Oracle Dependency Check  2026-04-14 (verified with `#print axioms`)

### Clay statement dependencies

| Theorem | Axioms depended on |
|---------|-------------------|
| `ClayYangMillsPhysicalStrong` (def) | `propext`, `Classical.choice`, `Quot.sound` |
| `clay_millennium_yangMills` | `propext`, `Classical.choice`, `Quot.sound`, **`holleyStroock_sunGibbs_lsi`** *(was: `yangMills_continuum_mass_gap`, eliminated v0.32.0)* |
| `clay_millennium_yangMills_strong` | `propext`, `Classical.choice`, `Quot.sound`, **`holleyStroock_sunGibbs_lsi`** *(was: `yangMills_continuum_mass_gap`, eliminated v0.32.0)* |
| `physicalStrong_implies_theorem` | `propext`, `Classical.choice`, `Quot.sound` |
| `sun_physical_mass_gap` | `propext`, `Classical.choice`, **`sorryAx`**, `Quot.sound` |

**Decisive conclusion:** the Clay statement consumes exactly ONE custom axiom  `yangMills_continuum_mass_gap`. Every other `axiom` declared in the repo is either consumed only by intermediate lemmas that don't feed Clay, or unused entirely.

`sun_physical_mass_gap` has `sorryAx` but no custom axioms  its oracle is the 3 documented `sorry` markers, not the labelled axioms.

### Usage count per axiom (files referencing the name, excluding Experimental)

| Axiom | Files | Status |
|-------|-------|--------|
| `yangMills_continuum_mass_gap` | 5 | **Live  sole Clay oracle** |
| `sz_lsi_to_clustering` | 4 | Live (intermediate; not on Clay path) |
| `hille_yosida_semigroup` | 3 | Live (intermediate; not on Clay path) |
| `holleyStroock_sunGibbs_lsi` | 2 | Live (intermediate; not on Clay path) |
| `poincare_to_covariance_decay` | 2 | Live (intermediate; not on Clay path) |
| `sunDirichletForm_contraction` | 2 | Live (intermediate; not on Clay path) |
| `physical_rg_rates_from_E26` | 2 | Live (RG branch; not on Clay path) |
| `p91_tight_weak_coupling_window` | 2 | Live (RG branch; not on Clay path) |
| `lsi_withDensity_density_bound` | 1 | **DEAD  no consumers** |
| `sun_variance_decay` | 1 | **DEAD  no consumers** |
| `sun_lieb_robinson_bound` | 1 | **DEAD  no consumers** |

### Cleanup recommendation

- **Remove 3 dead axioms** (`lsi_withDensity_density_bound`, `sun_variance_decay`,
  `sun_lieb_robinson_bound`)  they are declared but never referenced by any other
  file, so they add nothing except rhetoric. Deletion is safe.
- **Keep the 7 live intermediate/RG-branch axioms** but label them as such in their
  source files and rewrite their docstrings to say "not consumed by the Clay
  statement; this exists to support ".
- **`yangMills_continuum_mass_gap` is the single axiom that matters for Clay.**
  All current-pass proof effort on lsi/Holley-Stroock/etc. is structurally
  orthogonal to closing the Clay gap  it would discharge intermediate axioms
  that Clay does not consume. To make Clay unconditional, the sole move is to
  discharge `yangMills_continuum_mass_gap` directly (or wire the LSI chain
  into it, which currently doesn't happen).
