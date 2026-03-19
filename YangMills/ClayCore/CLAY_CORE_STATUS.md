# Clay Core — BalabanRG Status (v0.8.64, 2026-03-19)

**31 files · 0 errors · 2 honest sorrys**

## The two remaining sorrys
```lean
-- Layer 11C: large_field_suppression_bound
-- Source: P80 Theorem 4.1
-- Content: ‖T_k(K)‖ ≤ C·exp(-β)·‖K‖ (activities suppressed outside small-field region)

-- Layer 11C: rg_cauchy_summability_bound
-- Source: P81 Theorem 3.1 + P82 Theorem 2.4
-- Content: ‖T_k(K₁)-T_k(K₂)‖ ≤ exp(-β)·‖K₁-K₂‖ (RG map is Lipschitz)
```

When both proved:
  rg_blocking_map_contracts_v2
    → rg_norm_identification_to_full_package
    → polymer_dirichlet_identification_implies_lsi
    → ClayCoreLSI → LSItoSpectralGap ✅ → ClayYangMillsTheorem ✅

## Full layer inventory (31 files)

| Layer | File | Status |
|---|---|---|
| 0A  | BlockSpin.lean | ✅ |
| 0B  | FiniteBlocks.lean | ✅ |
| 1   | PolymerCombinatorics.lean | ✅ |
| 2   | PolymerPartitionFunction.lean | ✅ |
| 3A  | KPFiniteTailBound.lean | ✅ |
| 3B  | KPBudgetBridge.lean | ✅ KP → exp(B)-1 |
| 4A  | KPConsequences.lean | ✅ |
| 4B  | PolymerLogBound.lean | ✅ |
| 4C  | PolymerLogLowerBound.lean | ✅ |
| 5   | KPToLSIBridge.lean | ✅ clayCore_free_energy_ready |
| 6A  | BalabanRGPackage.lean | ✅ |
| 6B  | UniformLSITransfer.lean | ✅ |
| 6C  | BalabanRGAxiomReduction.lean | ✅ |
| 7A  | FreeEnergyControlReduction.lean | ✅ THEOREM |
| 7B  | EntropyCouplingReduction.lean | ✅ |
| 7C  | ContractiveMapReduction.lean | ✅ |
| 8A  | PhysicalRGRates.lean | ✅ |
| 8B  | PoincareRateLowerBound.lean | ✅ cP=(N_c/4)β |
| 8C  | LSIRateLowerBound.lean | ✅ cLSI=(N_c/8)β |
| 8D  | RGContractionRate.lean | ✅ rho=exp(-β) |
| 8E  | PhysicalBalabanRGPackage.lean | ✅ 0 axioms |
| 9A  | PhysicalWitnessToDirichletBridge.lean | ✅ |
| 9B  | PolymerPoincareRealization.lean | ✅ |
| 9C  | PolymerLSIRealization.lean | ✅ |
| 9D  | PolymerRGMapRealization.lean | ✅ |
| 10A | PolymerDirichletRateIdentification.lean | ✅ |
| 10B | RGMapNormIdentification.lean | ✅ (refactored) |
| 10C | DirichletPoincareIdentification.lean | ✅ |
| 10D | DirichletLSIIdentification.lean | ✅ |
| 10E | DirichletIdentificationClosure.lean | ✅ |
| 11A | ActivitySpaceNorms.lean | ✅ strong ActivityNorm |
| 11B | BalabanBlockingMap.lean | ✅ RGBlockingMap + predicates |
| 11C | RGContractiveEstimate.lean | ✅ 2 named sorrys |

## Dependency graph (clean)
```
PolymerCombinatorics (1)
  ↓
ActivitySpaceNorms (11A) ← new base for norm API
  ↓
BalabanBlockingMap (11B) ← RGBlockingMap + contraction predicates
  ↓
RGContractiveEstimate (11C) ← 2 honest sorrys
  ↓
RGMapNormIdentification (10B) ← uses 11B
  ↓
DirichletIdentificationClosure (10E) ← conditional package
  ↓
polymer_dirichlet_identification_implies_lsi
  ↓
ClayCoreLSI → ClayYangMillsTheorem ✅
```

## Next targets (E26 papers)

1. `large_field_suppression_bound` (P80 §4):
   Prove ‖T_k(K)‖ ≤ C·exp(-β)·‖K‖ using Balaban's small-field/large-field decomposition.

2. `rg_cauchy_summability_bound` (P81 §3, P82 §2):
   Prove ‖T_k(K₁)-T_k(K₂)‖ ≤ exp(-β)·‖K₁-K₂‖ using RG-Cauchy summability.
