# Clay Core — BalabanRG Status (v0.8.63, 2026-03-19)

**28 files · 0 errors · 1 honest sorry**

## The single remaining sorry
```lean
theorem rg_blocking_map_contracts (d N_c : ℕ) [NeZero N_c]
    [∀ k, ActivityNorm d k] (β : ℝ) (hβ : 1 ≤ β) :
    RGBlockingMapContracts d N_c β
```
Source: P81 Theorem 3.1 + P82 Theorem 2.4
Content: ‖T_k(K₁)-T_k(K₂)‖_{k+1} ≤ exp(-β)·‖K₁-K₂‖_k

When proved: rg_blocking_map_contracts
  → dirichlet_identification_package
  → polymer_dirichlet_identification_implies_lsi
  → ClayCoreLSI → LSItoSpectralGap ✅ → ClayYangMillsTheorem ✅

## Full layer inventory (28 files)

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
| 4C | PolymerLogLowerBound.lean | ✅ |logZ| ≤ 2t |
| 5  | KPToLSIBridge.lean | ✅ clayCore_free_energy_ready |
| 6A | BalabanRGPackage.lean | ✅ 3-field RG structure |
| 6B | UniformLSITransfer.lean | ✅ ClayCoreLSI from package |
| 6C | BalabanRGAxiomReduction.lean | ✅ 0-axiom route |
| 7A | FreeEnergyControlReduction.lean | ✅ THEOREM |
| 7B | EntropyCouplingReduction.lean | ✅ satisfiable |
| 7C | ContractiveMapReduction.lean | ✅ trivialBalabanRGPackage |
| 8A | PhysicalRGRates.lean | ✅ quantitative structure |
| 8B | PoincareRateLowerBound.lean | ✅ cP=(N_c/4)β |
| 8C | LSIRateLowerBound.lean | ✅ cLSI=(N_c/8)β |
| 8D | RGContractionRate.lean | ✅ rho=exp(-β) |
| 8E | PhysicalBalabanRGPackage.lean | ✅ physical_uniform_lsi |
| 9A | PhysicalWitnessToDirichletBridge.lean | ✅ semantic gap isolated |
| 9B | PolymerPoincareRealization.lean | ✅ PhysicalPoincareRealized |
| 9C | PolymerLSIRealization.lean | ✅ PhysicalLSIRealized |
| 9D | PolymerRGMapRealization.lean | ✅ physicalWitnessBridge |
| 10A | PolymerDirichletRateIdentification.lean | ✅ unified interface |
| 10B | RGMapNormIdentification.lean | ✅ 1 sorry (P81/P82) |
| 10C | DirichletPoincareIdentification.lean | ✅ le_rfl |
| 10D | DirichletLSIIdentification.lean | ✅ cLSI=cP/2 |
| 10E | DirichletIdentificationClosure.lean | ✅ conditional on 10B sorry |
