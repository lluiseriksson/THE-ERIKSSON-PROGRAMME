# SORRY FRONTIER — THE-ERIKSSON-PROGRAMME v0.50.0

Last updated: v0.50.0 (2026-04-24)

## Current sorry count: 0

Sorry count: 0. The former unrestricted
`lsi_normalized_gibbs_from_haar` placeholder is now an explicit named axiom in
`YangMills/P8_PhysicalGap/BalabanToLSI.lean`, not a theorem with a hidden
`sorry`. The Σ-path / MemLp-gated theorem
`lsi_normalized_gibbs_from_haar_memLp` remains fully proved and prints only the
canonical project oracle `[propext, Classical.choice, Quot.sound]`.

See `docs/phase1-llogl-obstruction.md` for the L·log·L obstruction history;
see `AXIOM_FRONTIER.md` v0.50.0 for the live axiom trace.

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

> ⚠️ **Policy update (2026-04-17):** The following reflects pre-v0.34 practice.
> The current project position on axioms introduced to close L·log·L-type gaps
> is in `docs/phase1-llogl-obstruction.md` §5 ("The wrong-axiom trap").
> Short version: the naive implication `Integrable f² → Integrable f²·log f²`
> is mathematically false (Bertrand counterexample); any axiom of that shape
> is unsound. Do not axiomatize L·log·L gaps.

We prefer explicit axioms over sorrys because:
1. Axioms are searchable and trackable
2. Axioms document the mathematical gap precisely
3. Axioms are type-checked (the statement is verified even if the proof is not)
4. Sorrys are silent proof holes; axioms are honest declarations
