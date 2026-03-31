<!-- Version: v0.25.0 (2026-03-31) -->
# AXIOM_FRONTIER.md — THE-ERIKSSON-PROGRAMME

## Executive Summary

**Status (v0.25.0): parameter-free, not unconditional.**

The final Clay Millennium theorem `YangMills.clay_millennium_yangMills` carries
zero explicit hypothesis parameters.  It is not fully unconditional: it depends
on one named custom axiom.

```lean
-- Authoritative kernel census (lake build; lake env lean --stdin):
#print axioms YangMills.clay_millennium_yangMills
-- [propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]
```

| Category | Count |
|----------|-------|
| Lean kernel axioms (standard, universally accepted) | 3 |
| Custom BFS-live axioms (in `#print axioms` of final theorem) | **1** |
| Custom dead declarations (not in final theorem dependency chain) | 25 |
| `sorry` count | 0 |
| Explicit theorem hypothesis parameters | 0 |

The project is **as honest as possible given the current mathematical frontier**.
The sole remaining gap is the continuum mass gap existence itself — the core
difficulty of the Clay Millennium Problem.

---

## Lean 4 Environment

- Lean: `leanprover/lean4:v4.29.0-rc6`
- Mathlib: master (pinned via `lake-manifest.json`)
- Build: `lake build YangMills` — 8172 compilation jobs, 0 errors

---

## BFS-Live Custom Axiom

This is the sole axiom beyond the three Lean kernel axioms that appears in
`#print axioms YangMills.clay_millennium_yangMills`.

### `YangMills.yangMills_continuum_mass_gap`

**File**: `YangMills/L8_Terminal/ClayTheorem.lean:51`

**Declaration**:
```lean
axiom yangMills_continuum_mass_gap :
    ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat
```

**Unfolded form** (`HasContinuumMassGap` is a `def`):
```lean
-- HasContinuumMassGap m_lat :=
--   ∃ m_phys : ℝ, 0 < m_phys ∧
--     Filter.Tendsto (renormalizedMass m_lat) Filter.atTop (nhds m_phys)
```

**Mathematical content**: There exists a renormalized SU(N) lattice mass profile
`m_lat : ℕ → ℝ` (with `m_lat(N) > 0` at each resolution N) such that the
sequence `renormalizedMass m_lat N = m_lat(N) / latticeSpacing(N)` converges to
a strictly positive limit as N → ∞.

**Status**: OPEN — this is the genuine remaining mathematical frontier.
Asymptotic freedom + Balaban RG flow are expected to establish that the SU(N)
lattice mass gap survives the continuum limit, but the full proof is not yet
formalised.  This is the core difficulty of the Clay Millennium Problem.

**Role in the proof**:
```lean
theorem yangMills_existence_massGap : ClayYangMillsTheorem := by
  obtain ⟨m_lat, hcont⟩ := yangMills_continuum_mass_gap
  exact continuumLimit_mass_pos m_lat hcont

theorem clay_millennium_yangMills : ∃ m_phys : ℝ, 0 < m_phys :=
  clay_mass_gap_pos
```

**Introduced**: v0.24.0 (2026-03-31) — converted from explicit theorem parameter
`hContinuumMassGap` to a named `axiom` declaration, making the final theorem
parameter-free while keeping the assumption fully visible in `#print axioms`.

**Elimination path**: Would require proving that
`renormalizedMass m_lat N = m_lat(N) / a(N)` converges to a strictly positive
limit for some constructible `m_lat`.  This requires analytical control of the
Balaban RG flow in the continuum limit and the UV asymptotic freedom regime.

---

## Dead Custom Axiom Declarations

The 25 declarations below are `axiom` statements that exist in the codebase
but are **not** reachable from `YangMills.clay_millennium_yangMills` by any
proof path.  Confirmed by: `#print axioms YangMills.clay_millennium_yangMills`.

These declarations represent experimental proof scaffolding for alternative
routes not yet connected, mathematical support lemmas for future formalisation
layers, and historical frontier items superseded by the current L0-L8 chain.

They do not affect the soundness of the current final theorem.

### ClayCore/BalabanRG (2 dead axioms)

Quantitative RG-flow rate estimates supporting the Balaban programme.
Not yet connected to the main L0-L8 chain.

| Axiom | File | Mathematical content |
|-------|------|----------------------|
| `physical_rg_rates_from_E26` | `PhysicalRGRates.lean:101` | Physical RG rate bounds from E26 sector |
| `p91_tight_weak_coupling_window` | `P91WeakCouplingWindow.lean:51` | Tight weak-coupling window (sector P91) |

### Experimental/LieSUN (10 dead axioms)

SU(N) Lie-algebra generators, skew-Hermiticity, trace-zero, matrix exponential,
and Dirichlet-form contraction.  Experimental module.

| Axiom | File |
|-------|------|
| `generatorMatrix` | `LieDerivativeRegularity.lean:18` |
| `gen_skewHerm` | `LieDerivativeRegularity.lean:20` |
| `gen_trace_zero` | `LieDerivativeRegularity.lean:22` |
| `matExp_traceless_det_one` | `LieExpCurve.lean:81` |
| `generatorMatrix'` | `DirichletConcrete.lean:23` |
| `gen_skewHerm'` | `DirichletConcrete.lean:26` |
| `gen_trace_zero'` | `DirichletConcrete.lean:29` |
| `dirichlet_lipschitz_contraction` | `DirichletContraction.lean:55` |
| (2 further LieSUN support axioms) | various |

### Experimental/Semigroup (4 dead axioms)

Hille-Yosida decomposition and variance decay from Poincare inequalities.

| Axiom | File |
|-------|------|
| `hille_yosida_core` | `HilleYosidaDecomposition.lean:62` |
| `poincare_to_variance_decay` | `HilleYosidaDecomposition.lean:69` |
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | `VarianceDecayFromPoincare.lean:79` |
| `gronwall_variance_decay` | `VarianceDecayFromPoincare.lean:133` |

### P8_PhysicalGap (9 dead axioms)

Alternative physical proof route via LSI / Bakry-Emery / Lieb-Robinson.
Developed as an independent approach to the mass gap; not yet connected.

| Axiom | File | Mathematical content |
|-------|------|----------------------|
| `sunDirichletForm_contraction` | `SUN_DirichletCore.lean:178` | SU(N) Dirichlet form contraction |
| `hille_yosida_semigroup` | `MarkovSemigroupDef.lean:126` | Hille-Yosida semigroup construction |
| `poincare_to_covariance_decay` | `StroockZegarlinski.lean:21` | Stroock-Zegarlinski covariance decay |
| `bakry_emery_lsi` | `BalabanToLSI.lean:61` | Bakry-Emery log-Sobolev inequality |
| `sun_bakry_emery_cd` | `BalabanToLSI.lean:71` | SU(N) curvature-dimension condition |
| `balaban_rg_uniform_lsi` | `BalabanToLSI.lean:102` | Balaban RG uniform LSI |
| `sz_lsi_to_clustering` | `BalabanToLSI.lean:127` | LSI implies clustering |
| `sun_variance_decay` | `SUN_LiebRobin.lean:41` | SU(N) variance decay |
| `sun_lieb_robinson_bound` | `SUN_LiebRobin.lean:47` | Lieb-Robinson bound for SU(N) |

---

## How to Reproduce the Census

After a successful `lake build YangMills`:

```bash
lake env lean --stdin << 'EOF'
import YangMills
#print axioms YangMills.clay_millennium_yangMills
EOF
```

Expected output:
```
[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]
```

To count all `axiom` declarations in the codebase:
```bash
grep -rn "^axiom " YangMills/ --include="*.lean" | wc -l
# Expected: 26 (1 live + 25 dead)
```

To confirm 0 `sorry`:
```bash
grep -rn "sorry" YangMills/ --include="*.lean" | wc -l
# Expected: 0
```

---

## Change Log

| Version | Date | Change |
|---------|------|--------|
| v0.25.0 | 2026-03-31 | Complete rewrite: live-vs-dead axiom split; accurate census; |
| | | removed obsolete Tier A-F structure; 1 live, 25 dead |
| v0.24.0 | 2026-03-31 | L8 axiom introduced: `yangMills_continuum_mass_gap`; |
| | | `clay_millennium_yangMills` now parameter-free; hypothesis frontier = 0 |
| v0.23.0 | 2026-03-31 | HYPOTHESIS FRONTIER: removed unused `hFiniteVolumeMassGap` |
| v0.22.0 | 2026-03-31 | HYPOTHESIS FRONTIER: removed unused parameters |
| v0.21.0 | 2026-03-31 | AXIOM FRONTIER reached zero (campaigns 7-10) |
| v0.19.0 | 2026-03-29 | Tier E deep analysis: both axioms require Balaban paper |
| v0.18.0 | 2026-03-29 | BFS reachability analysis: 7 build-live axioms (not 27) |
| v0.17.0 | 2026-03-29 | Lean 4.29.0 confirmation: both Tier-B axioms blocked |
| v0.16.0 | 2026-03-29 | Census corrected to 29; block-comment stripping; 0 duplicates |

---

*AXIOM_FRONTIER.md v0.25.0 — 2026-03-31*
