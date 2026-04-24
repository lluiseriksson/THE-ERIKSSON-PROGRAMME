# BALABAN_CORE_CONTRACT.md

## Status: ACTIVE FRONTIER
## Target: `balaban_rg_uniform_lsi` — the Yang-Mills mass gap

This document is the formal contract for the Clay Millennium Problem core.
It defines the decomposition strategy and formalizable subgoals.

---

## Former Axiom-Shaped Target
```lean
-- Former frontier shape, now treated as a theorem target / explicit input
-- rather than a declaration in this contract file.
theorem balaban_rg_uniform_lsi_target
    (d N_c : ℕ) (hN_c : 2 ≤ N_c)
    (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀)
    (α_haar : ℝ) (hα_haar : 0 < α_haar)
    (hHaar : LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) α_haar) :
    ∃ α_star : ℝ, 0 < α_star ∧
      ∀ L : ℕ, LogSobolevInequality
        (sunGibbsFamily d N_c β L) (sunDirichletForm N_c) α_star
```

**What it claims:**
Given single-site LSI for SU(N) Haar measure, the Balaban RG provides
a uniform (L-independent) LSI for all finite-volume Gibbs measures.
The uniformity is the mass gap.

---

## Literature Sources

The E26 paper series (2602.0046–2602.0117), 29/29 papers audited:
- **P86** (2602.0131): Block-spin transformation, scale decomposition
- **P89** (2602.0134): Polymer representation, activity bounds
- **P90** (2602.0135): Kotecký-Preiss cluster expansion, LSI preservation

Key external references:
- Balaban, CMP 85/95/96/99/102 (1982-1985): polymer expansion
- Bauerschmidt-Dagallier (2022): scalar analogue via Polchinski RG
- Kotecký-Preiss (1986): abstract cluster expansion criterion

---

## Decomposition Strategy

### Layer 0: Block-spin kinematics (pure combinatorics)
Formalizable in Lean with `Finset (Site d)`:
- Block decomposition: partition lattice into L-cubes
- Block-spin map: averaging operator from fine to coarse
- Scale hierarchy: k → k+1 renormalization step

**First formalizable target:** `BlockSpinMap.lean`
No measure theory needed. Pure combinatorics on `Finset (Fin d → ℤ)`.

### Layer 1: Polymer representation (combinatorics + algebra)
- Polymer definition: connected subsets of blocks
- Activity functional: `w : Polymer → ℝ`
- Partition function decomposition: Z = Z_free * Σ_polymers

**Key property to formalize:** Kotecký-Preiss criterion (abstract)
```
∑_{γ∋x} |w(γ)| * exp(a|γ|) ≤ a
```
This is purely combinatorial — no Yang-Mills physics needed.

### Layer 2: Small-field / large-field decomposition
- Large-field region: where gauge fields are not close to identity
- Small-field region: perturbative regime, Gaussian approximation valid
- This is where gauge theory enters — harder to formalize

### Layer 3: LSI preservation along RG flow
- The key Clay content: α_star doesn't degrade as L → ∞
- Requires all of Layers 0-2 plus gauge-invariance arguments
- Current status: open mathematics (no published proof for non-abelian case)

---

## Governance Rule
```
NO REFACTOR ACCEPTED IF:
  - P8 axioms > 8, OR
  - Any P8 sorry is introduced, OR
  - Honesty of existing axioms decreases
```

---

## Next Steps (ordered by feasibility)

1. **BlockSpin.lean** — lattice combinatorics, no measure theory
   - Define `Block`, `BlockSpinMap`, `ScaleHierarchy`
   - Prove basic properties: surjectivity, block-additivity
   - FORMALIZABLE NOW

2. **PolymerCombinatorics.lean** — abstract polymer expansion
   - Define `Polymer`, `Activity`, `PolymerPartition`
   - Formalize Kotecký-Preiss criterion abstractly
   - FORMALIZABLE NOW (no gauge theory needed)

3. **KoteckyPreiss.lean** — abstract convergence criterion
   - The KP criterion is purely combinatorial
   - Mathlib may have sufficient graph/combinatorics theory
   - INVESTIGATE

4. **GaussianBound.lean** — small-field Gaussian approximation
   - Needs: Gaussian measures on finite-dimensional lattice
   - Mathlib has: `MeasureTheory.Measure.Gaussian`
   - PARTIALLY FORMALIZABLE

5. **LSIPreservation.lean** — the hard Clay step
   - The actual mass gap argument
   - Requires: Layers 0-4 complete
   - LONG TERM

---

## Session log

| Session | Achievement |
|---------|-------------|
| v0.8.50 | P8 frontier complete: 8 honest axioms, all paths exhausted |
| v0.8.50+ | BlockSpin.lean: infinite-lattice geometry ✅ |
| v0.8.50+ | FiniteBlocks.lean: finite-volume averaging ✅ |
| v0.8.50+ | PolymerCombinatorics.lean: Polymer, KP criterion ✅ |
| v0.8.50+ | PolymerPartitionFunction.lean: Z, Z(empty)=1, Z({X})=1+K(X) ✅ |
| v0.8.50+ | Layers 2B+2C: partitionTail, Z=1+Ztail, SmallActivityBudget ✅ |
| Next | KPFiniteTailBound.lean: connect KP criterion to budget |
