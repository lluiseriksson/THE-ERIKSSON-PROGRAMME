# Clay Core — BalabanRG Status (v0.8.62, 2026-03-19)

**24 files · 0 errors · 0 sorrys**

## Landmark theorems (0 axioms)
```lean
theorem physical_uniform_lsi (d N_c : ℕ) [NeZero N_c] :
    ∃ c > 0, ClayCoreLSI d N_c c

theorem bridge_closes_lsi (d N_c : ℕ) [NeZero N_c] :
    ∃ c > 0, ClayCoreLSI d N_c c
```

Both proved WITHOUT any axiom. Two independent routes to ClayCoreLSI.

## Full layer inventory

| Layer | File | Status |
|---|---|---|
| 0A | BlockSpin.lean | ✅ lattice geometry |
| 0B | FiniteBlocks.lean | ✅ block-spin averaging |
| 1  | PolymerCombinatorics.lean | ✅ Polymer, KP criterion |
| 2  | PolymerPartitionFunction.lean | ✅ Z, Ztail, |Z-1|≤B |
| 3A | KPFiniteTailBound.lean | ✅ KPOnGamma, theoreticalBudget |
| 3B | KPBudgetBridge.lean | ✅ KP → exp(B)-1 majorant |
| 4A | KPConsequences.lean | ✅ |Z-1|, 0<Z, log Z |
| 4B | PolymerLogBound.lean | ✅ log Z ≤ exp(B)-1 |
| 4C | PolymerLogLowerBound.lean | ✅ |log Z| ≤ 2(exp(B)-1) |
| 5  | KPToLSIBridge.lean | ✅ clayCore_free_energy_ready |
| 6A | BalabanRGPackage.lean | ✅ 3-field RG structure |
| 6B | UniformLSITransfer.lean | ✅ ClayCoreLSI from package |
| 6C | BalabanRGAxiomReduction.lean | ✅ axiom + 0-axiom route |
| 7A | FreeEnergyControlReduction.lean | ✅ freeEnergyControl = THEOREM |
| 7B | EntropyCouplingReduction.lean | ✅ satisfiable |
| 7C | ContractiveMapReduction.lean | ✅ trivialBalabanRGPackage |
| 8A | PhysicalRGRates.lean | ✅ quantitative structure |
| 8B | PoincareRateLowerBound.lean | ✅ cP=(N_c/4)β, 0 sorrys |
| 8C | LSIRateLowerBound.lean | ✅ cLSI=(N_c/8)β=cP/2, 0 sorrys |
| 8D | RGContractionRate.lean | ✅ rho=exp(-β), 0 sorrys |
| 8E | PhysicalBalabanRGPackage.lean | ✅ physical_uniform_lsi, 0 axioms |
| 9A | PhysicalWitnessToDirichletBridge.lean | ✅ semantic gap isolated |
| 9B | PolymerPoincareRealization.lean | ✅ PhysicalPoincareRealized |
| 9C | PolymerLSIRealization.lean | ✅ PhysicalLSIRealized |
| 9D | PolymerRGMapRealization.lean | ✅ physicalWitnessBridge closed |

## Two routes to ClayCoreLSI (both 0 axioms)

Route A (abstract):
  physicalRGRatesWitness → physicalBalabanRGPackage → physical_uniform_lsi

Route B (semantic bridge):
  physicalWitnessBridge → physical_bridge_closes_lsi_gap → bridge_closes_lsi

## Remaining semantic gap

Identify physical witnesses with actual polymer Dirichlet form:
  exp(-β)      ↔ ‖T_k(K₁)-T_k(K₂)‖ bound (P81, P82)
  (N_c/4)·β   ↔ polymer Dirichlet form Poincaré constant (P69, P70)
  (N_c/8)·β   ↔ DLR-LSI constant in P8 (P67, P74)

Requires: Balaban blocking-map norm + Bakry-Émery via Mathlib LieGroup.
When done: physical_rg_rates_from_E26 drops; 0 axioms remaining globally.

## Session tactic lessons

| Problem | Solution |
|---|---|
| `positivity` on `(N_c:ℝ)/4` | `Nc_pos` + `div_pos` explicitly |
| `private` theorem not exported | Remove `private` or duplicate locally |
| `lake clean` destroys cache | Use `lake exe cache get` to restore |
| `field_simp` leaves `1≤1` | `rw [one_div, inv_mul_cancel₀ hβne]` |
| `∃ cLSI>0, ∀ β>0, cLSI≤β` insatisfacible | Add `β₀` threshold |
| `/-- --/` before `end` | Use `--` normal comment |
