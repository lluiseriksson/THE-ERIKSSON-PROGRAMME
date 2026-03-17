# SORRY FRONTIER — v0.8.32

## Status: 0 sorrys in P8_PhysicalGap

All sorrys in `SpatialLocalityFramework.lean` have been eliminated.

## Remaining mathematical frontier

### `LiebRobinsonBound` — explicit hypothesis in `locality_to_static_covariance_v2`
```lean
def LiebRobinsonBound {d : ℕ} ... (sg : MarkovSemigroup μ) : Prop :=
  ∀ (A B : Finset (Site d)) (F G : Ω → ℝ) ...,
    |Cov(F,G) - Cov(F, T_{t*} G)| ≤ exp(-dist(A,B)) · √VarF · √VarG
```

**Mathematical content**: Finite speed of propagation for lattice dynamics.
**Reference**: Hastings-Koma (2006), Nachtergaele-Sims (2006).
**Status**: Not a global axiom — an explicit hypothesis of the main theorem.

### `hille_yosida_semigroup` — in `MarkovSemigroupDef.lean`

Strong Dirichlet form → Markov semigroup (Beurling-Deny/Fukushima).
Mathlib gap: C₀-semigroup theory not yet in Mathlib.

## History

| Version | Event |
|---------|-------|
| v0.8.32 | 0 sorrys in SpatialLocalityFramework, LiebRobinson demoted to hypothesis |
| v0.8.31 | `dynamic_covariance_at_optimalTime` sorry closed |
| v0.8.29 | `locality_to_static_covariance_v2` assembly proved |
| v0.8.28 | SpatialLocalityFramework created with 4 sorrys |

*Last updated: v0.8.32 — March 2026*
