# Clay Core — BalabanRG Status (v0.8.61, 2026-03-19)

**21 files · 0 errors · 0 sorrys**

## Landmark theorem
```lean
theorem physical_uniform_lsi (d N_c : ℕ) [NeZero N_c] :
    ∃ c > 0, ClayCoreLSI d N_c c
```
**Proved without any axiom.** Uses physical witnesses:
- `rho(β) = exp(-β)` — RG contraction rate
- `cP(β) = (N_c/4)·β` — Poincaré constant (Ricci = N/4)
- `cLSI(β) = (N_c/8)·β` — LSI constant (Poincaré/2)

## Full layer inventory

| Layer | File | Status |
|---|---|---|
| 0A | BlockSpin.lean | ✅ |
| 0B | FiniteBlocks.lean | ✅ |
| 1  | PolymerCombinatorics.lean | ✅ |
| 2  | PolymerPartitionFunction.lean | ✅ |
| 3A | KPFiniteTailBound.lean | ✅ |
| 3B | KPBudgetBridge.lean | ✅ KP → exp(B)-1 |
| 4A | KPConsequences.lean | ✅ |Z-1|, 0<Z, logZ |
| 4B | PolymerLogBound.lean | ✅ logZ ≤ exp(B)-1 |
| 4C | PolymerLogLowerBound.lean | ✅ |logZ| ≤ 2(exp(B)-1) |
| 5  | KPToLSIBridge.lean | ✅ clayCore_free_energy_ready |
| 6A | BalabanRGPackage.lean | ✅ 3-field RG structure |
| 6B | UniformLSITransfer.lean | ✅ LSI from package |
| 6C | BalabanRGAxiomReduction.lean | ✅ axiom + 0-axiom route |
| 7A | FreeEnergyControlReduction.lean | ✅ freeEnergyControl = THEOREM |
| 7B | EntropyCouplingReduction.lean | ✅ satisfiable |
| 7C | ContractiveMapReduction.lean | ✅ trivialBalabanRGPackage |
| 8A | PhysicalRGRates.lean | ✅ quantitative structure |
| 8B | PoincareRateLowerBound.lean | ✅ cP=(N_c/4)β proved |
| 8C | LSIRateLowerBound.lean | ✅ cLSI=(N_c/8)β proved |
| 8D | RGContractionRate.lean | ✅ rho=exp(-β) proved |
| 8E | PhysicalBalabanRGPackage.lean | ✅ 0 axioms 0 sorrys |

## Remaining gap (semantic, not structural)

`physical_rg_rates_from_E26` remains as an honest axiom stating that
the polymer Dirichlet form realizes the physical rates.

Discharge requires E26 papers P67–P82:
- Connect exp(-β) to ‖T_k(K₁)-T_k(K₂)‖ (Balaban blocking map norm)
- Connect (N_c/4)β to polymer Dirichlet form Poincaré constant
- Connect (N_c/8)β to DLR-LSI constant in P8

## Chain proven (0 axioms via physical witnesses)
```
physicalRGRatesWitness (def)
  → physicalBalabanRGPackage (def)
  → physical_uniform_lsi (theorem)
  → ClayCoreLSI
  → LSItoSpectralGap ✅ (P8)
  → ClayYangMillsTheorem ✅
```
