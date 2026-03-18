# SORRY FRONTIER — THE-ERIKSSON-PROGRAMME v0.8.47

Last updated: v0.8.47

## Current sorry count: 0

All sorry-based proofs have been eliminated from the P8 physical gap module.
The remaining open items are declared as explicit axioms (see AXIOM_FRONTIER.md).

## Files with no sorrys in P8_PhysicalGap

| File | Sorrys | Status |
|------|--------|--------|
| SpatialLocalityFramework.lean | 0 | ✅ Fully proved |
| CovarianceLemmas.lean | 0 | ✅ Fully proved |
| MarkovVarianceDecay.lean | 0 | ✅ Fully proved |
| MarkovSemigroupDef.lean | 0 | ✅ (1 axiom: hille_yosida) |
| SUN_Compact.lean | 0 | ✅ Fully proved |
| SUN_DirichletCore.lean | 0 | ✅ (axioms documented) |
| SUN_StateConstruction.lean | 0 | ✅ (axiom: IsTopologicalGroup) |
| SUN_LiebRobin.lean | 0 | ✅ sun_locality_to_covariance proved |

## Philosophy

We prefer explicit axioms over sorrys because:
1. Axioms are searchable and trackable
2. Axioms document the mathematical gap precisely
3. Axioms are type-checked (the statement is verified even if the proof is not)
4. Sorrys are silent proof holes; axioms are honest declarations
