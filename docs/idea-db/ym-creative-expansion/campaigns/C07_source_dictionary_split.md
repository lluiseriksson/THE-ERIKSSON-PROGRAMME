# C07 — Source dictionary split campaign

Goal: replace monolithic source hypotheses by records with individually auditable fields.

Targets:
- `CMP116Eq231SourceDictionary`
- `CMP116Eq237SourceDictionary`
- `AppendixFMetricDictionary`
- `PhysicalToCMP116ProjectionConstants`

Payoff:
- Builders can discharge carrier/count/orientation without pretending to prove analytic estimates.
- Reviewers can see whether an update is a true hypothesis removal or only a shape refinement.

First theorem:
```lean
theorem eq231_hmem_of_sourceDictionary
  (S : CMP116Eq231SourceDictionary PIndex gapCubes admissible) :
  ∀ Z D P, P ∈ PIndex Z D ↔
    P ⊆ gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4)) ∧ admissible Z D P = true
```
