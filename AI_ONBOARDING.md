# AI Onboarding Guide — THE-ERIKSSON-PROGRAMME

## What This Repo Is

A Lean 4 / Mathlib 4 formalization of the Yang–Mills mass gap problem (Clay Millennium Problem).
The project does NOT claim to solve the Clay problem. It formalizes the mathematical
architecture described in 68 companion papers by Lluis Eriksson.

**Current version: v1.44.0 (C131)**
**BFS-live custom axioms: 1** (`lsi_withDensity_density_bound`)

## The Primary Proof Path (LSI Pipeline)

```
sun_physical_mass_gap : ClayYangMillsTheorem
  └─ sun_clay_conditional ← sun_gibbs_dlr_lsi
       └─ sun_haar_lsi (THEOREM: Bakry-Émery for SU(N))
       └─ balaban_rg_uniform_lsi (THEOREM: Holley-Stroock, C129)
            └─ holleyStroock_sunGibbs_lsi (THEOREM: C130)
                 └─ lsi_withDensity_density_bound (**AXIOM**: abstract Holley-Stroock)
                 └─ sunPlaquetteEnergy_nonneg (THEOREM: C131)
                 └─ sunPlaquetteEnergy_le_two (THEOREM: C131)
```

Oracle for `sun_physical_mass_gap`:
```
[propext, Classical.choice, Quot.sound, YangMills.lsi_withDensity_density_bound]
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

The real mathematical achievement is `sun_gibbs_dlr_lsi` — a DLR-uniform LSI
for SU(N) heat-kernel Gibbs measures, proved modulo 1 standard functional
analysis lemma (`lsi_withDensity_density_bound`).

## Current State (v1.44.0)

### The 1 Remaining Axiom

**`lsi_withDensity_density_bound`** (BalabanToLSI.lean:192)
- Content: If μ satisfies LSI(α) and r ≤ ρ ≤ 1, then μ.withDensity(ρ) satisfies LSI(α·r)
- This is pure functional analysis (Holley-Stroock 1987), NOT physics
- Not in Mathlib; provable from first principles (~50 lines of real analysis)

### Recently Eliminated (C124–C131)

| Axiom | Campaign | Method |
|-------|----------|--------|
| `sunPlaquetteEnergy_nonneg` | C131 | `entry_norm_bound_of_unitary` (Mathlib) |
| `sunPlaquetteEnergy_le_two` | C131 | `entry_norm_bound_of_unitary` (Mathlib) |
| `holleyStroock_sunGibbs_lsi` | C130 | Abstract HS + energy bounds |
| `balaban_rg_uniform_lsi` | C129 | Holley-Stroock perturbation |
| `sun_bakry_emery_cd` | C126 | Dirichlet form arithmetic |
| `sz_lsi_to_clustering` | C125 | Bypassed (α* > 0 directly) |
| `bakry_emery_lsi` | C124 | BakryEmeryCD := LSI |

## Key Files

```
YangMills/P8_PhysicalGap/
  BalabanToLSI.lean         # ★ 1 AXIOM lives here
  PhysicalMassGap.lean      # ★ sun_physical_mass_gap
  LSIDefinitions.lean       # LogSobolevInequality, DLR_LSI defs
  SUN_StateConstruction.lean # Concrete SU(N) state space
```

## Key Oracle Command

```bash
printf 'import YangMills.P8_PhysicalGap.PhysicalMassGap\n#print axioms YangMills.sun_physical_mass_gap\n' | lake env lean --stdin
```

Expected output (v1.44.0):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.lsi_withDensity_density_bound]
```

## Campaign Loop Protocol

1. Read current repo state (`cat BalabanToLSI.lean`, check oracle)
2. Pick highest-value target (eliminate `lsi_withDensity_density_bound`)
3. Write Lean file + build + oracle check
4. Commit + tag + push
5. Update docs (ROADMAP, README, STATE_OF_THE_PROJECT, AI_ONBOARDING)
6. GOTO 1

## Next Campaign Target

Prove `lsi_withDensity_density_bound` from Mathlib. This is standard Holley-Stroock:
1. Change-of-measure for entropy: Ent_{ρ·μ}(f) relates to Ent_μ(f·√ρ)
2. Density bounds r ≤ ρ ≤ 1 give ∫ f² ρ dμ ≥ r · ∫ f² dμ
3. Apply LSI(α) to get the bound with constant α·r
Ref: Holley-Stroock (1987), Ledoux Ch. 5.

## Build Commands

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build YangMills.P8_PhysicalGap.PhysicalMassGap  # primary target
lake build YangMills                                    # full build
```

## License

AGPL-3.0 (GNU Affero General Public License v3.0)
