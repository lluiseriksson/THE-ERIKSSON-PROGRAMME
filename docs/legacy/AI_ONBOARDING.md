# AI Onboarding Guide — THE-ERIKSSON-PROGRAMME

## What This Repo Is

A Lean 4 / Mathlib 4 formalization of the Yang–Mills mass gap problem (Clay Millennium Problem).
The project does NOT claim to solve the Clay problem. It formalizes the mathematical
architecture described in 68 companion papers by Lluis Eriksson.

**Current version: v1.45.0 (C133)**
**BFS-live custom axioms: 1** (`lsi_normalized_gibbs_from_haar`)

## The Primary Proof Path (LSI Pipeline)

```
sun_physical_mass_gap : ClayYangMillsTheorem
  └─ sun_clay_conditional_norm ← sun_gibbs_dlr_lsi_norm
       └─ sun_haar_lsi (THEOREM: Bakry-Émery for SU(N))
       └─ balaban_rg_uniform_lsi_norm (THEOREM: C132)
            └─ holleyStroock_sunGibbs_lsi_norm (THEOREM: C132)
                 └─ lsi_normalized_gibbs_from_haar (**AXIOM**: specific HS for normalized Gibbs)
                 └─ instIsProbabilityMeasure_sunGibbsFamily_norm (THEOREM: C132)
```

Oracle for `sun_physical_mass_gap`:
```
[propext, Classical.choice, Quot.sound, YangMills.lsi_normalized_gibbs_from_haar]
```

## ⚠ Critical Warnings for AI Agents

### 1. ClayYangMillsTheorem is VACUOUS

`ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys` — trivially true.
`clay_yangmills_unconditional` in `ErikssonBridge.lean` proves it with ZERO custom axioms
(G = Unit, F = 0, β = 0). Do NOT claim this is a substantive result.

### 2. Tautological definitions

- `BakryEmeryCD μ E K := LogSobolevInequality μ E K` — so `bakry_emery_lsi` is `id`
- `sunDirichletForm N_c f := (N_c/8) * Ent(f)` — engineered for arithmetic

### 3. The genuine content

The real mathematical achievement is `sun_gibbs_dlr_lsi_norm` — a DLR-uniform LSI
for the **normalized** SU(N) heat-kernel Gibbs probability measure, proved modulo
1 specific Holley-Stroock instance (`lsi_normalized_gibbs_from_haar`).
The normalization (`IsProbabilityMeasure`) is **proved**, not assumed (C132).

## Current State (v1.45.0)

### The 1 Remaining Axiom

**`lsi_normalized_gibbs_from_haar`** (BalabanToLSI.lean:255)
- Content: If Haar satisfies LSI(α), then normalized Gibbs satisfies LSI(α·exp(-2β))
- This is a specific instance of the Holley-Stroock perturbation lemma
- The normalization (IsProbabilityMeasure) is PROVED in C132
- Not in Mathlib; provable from entropy change-of-measure argument

### Recently Eliminated (C124–C132)

| Axiom | Campaign | Method |
|-------|----------|--------|
| `lsi_withDensity_density_bound` (BFS-live) | C132 | Replaced by `lsi_normalized_gibbs_from_haar` (correctly stated) |
| `sunPlaquetteEnergy_nonneg` | C131 | `entry_norm_bound_of_unitary` (Mathlib) |
| `sunPlaquetteEnergy_le_two` | C131 | `entry_norm_bound_of_unitary` (Mathlib) |
| `balaban_rg_uniform_lsi` | C129 | Holley-Stroock perturbation |
| `sun_bakry_emery_cd` | C126 | Dirichlet form arithmetic |
| `sz_lsi_to_clustering` | C125 | Bypassed (α* > 0 directly) |
| `bakry_emery_lsi` | C124 | BakryEmeryCD := LSI |

## Key Files

```
YangMills/P8_PhysicalGap/
  BalabanToLSI.lean         # ★ 1 AXIOM lives here (lsi_normalized_gibbs_from_haar)
  PhysicalMassGap.lean      # ★ sun_physical_mass_gap
  LSIDefinitions.lean       # LogSobolevInequality, DLR_LSI defs
  SUN_StateConstruction.lean # Concrete SU(N) state space
```

## Key Oracle Command

```bash
printf 'import YangMills.P8_PhysicalGap.PhysicalMassGap\n#print axioms YangMills.sun_physical_mass_gap\n' | lake env lean --stdin
```

Expected output (v1.45.0):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.lsi_normalized_gibbs_from_haar]
```

## Campaign Loop Protocol

1. Read current repo state (`cat BalabanToLSI.lean`, check oracle)
2. Pick highest-value target (eliminate `lsi_normalized_gibbs_from_haar`)
3. Write Lean file + build + oracle check
4. Commit + tag + push
5. Update docs (ROADMAP, README, STATE_OF_THE_PROJECT, AI_ONBOARDING)
6. GOTO 1

## Next Campaign Target

Prove `lsi_normalized_gibbs_from_haar` from Mathlib. This is the Holley-Stroock
perturbation lemma for the normalized SU(N) Gibbs probability measure:
1. The normalized density ρ_norm = exp(-β·e)/Z_β is bounded: exp(-2β)/Z_β ≤ ρ_norm ≤ 1/Z_β
2. Entropy change-of-measure: Ent_{ρ·μ}(f) relates to Ent_μ(f)
3. Apply LSI(α) for Haar to get LSI(α·exp(-2β)) for normalized Gibbs
Ref: Holley-Stroock (1987), Ledoux Ch. 5.

**C133 audit findings:** Mathlib has `withDensity`, `lintegral_withDensity_eq_lintegral_mul`,
Radon-Nikodym, but NO log-Sobolev library. Must formalize entropy change-of-measure
from scratch. Key Mathlib entry points:
- `MeasureTheory.Measure.withDensity`
- `MeasureTheory.lintegral_withDensity_eq_lintegral_mul`
- `MeasureTheory.Measure.absolutelyContinuous_withDensity`

## Build Commands

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build YangMills.P8_PhysicalGap.PhysicalMassGap  # primary target
lake build YangMills                                    # full build
```

## License

AGPL-3.0 (GNU Affero General Public License v3.0)
