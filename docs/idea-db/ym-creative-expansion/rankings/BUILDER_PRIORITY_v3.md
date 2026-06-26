# v3 builder priority — source-hypothesis removal only

## Tier 0 — immediate commit target

1. **Eq. (2.31) `source_subset_gapCarrier` via bond first-coordinate**
   - Formula card: D32
   - Lean reducer already present: `cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes`
   - Output: source theorem proving `∀ b ∈ P, b.1 ∈ gapCubes Z D`.
   - Why first: smallest source window, removes one field without full iff.

## Tier 1 — after carrier field

2. **Eq. (2.31) `mem_iff_source`**
   - Formula card: D34
   - Output: source-family extensionality theorem.

3. **Eq. (2.31) `admissible_iff_source`**
   - Formula card: D33
   - Output: non-circular boolean/source predicate theorem.

4. **Eq. (2.31) pointwise P-residual majorization**
   - Formula card: D35
   - Output: termwise residual-to-PWeight theorem.

## Tier 2 — external or analytic blockers

5. **Eq. (2.29) Cammarota threshold record**
   - Formula card: D39
   - Output: honest interface, no theorem claim until source extraction.

6. **Eq. (2.37) source index equality + fixed-Z0prime estimate**
   - Formula cards: D37-D38
   - Output: combined route, not split without source support.

7. **R-operation polymer-local to scalar Rsc bridge**
   - Formula card: D41
   - Output: exact bridge obligation from polymer-local bounds to `Rsc`.

## Tier 9 — reject or docs-only

- More wrappers around existing hypotheses.
- Any claim that v3 proves `hRpoly` or Clay.
- Any source promotion based on operational metadata alone.
