# PR: Möbius inversion on the partition lattice

**Branch suggestion**: `lluis-eriksson/partition-lattice-mobius`
**Suggested target file**: `Mathlib/Combinatorics/SetFamily/Partition/Mobius.lean`
(or extension of `Mathlib/Combinatorics/SetFamily/Partition.lean`)
**Estimated review effort**: 4–8 reviewer-hours (substantial new
content)
**Mathlib zulip ping**: #maths > combinatorics, with mention to
maintainers Bhavik Mehta, Yaël Dillies, and the partition-theory
contributors.

---

## Summary

This PR adds the Möbius function of the partition lattice and the
corresponding inversion theorem:

```lean
theorem Finpartition.mobiusFunction_singletons
    {α : Type*} [DecidableEq α] {S : Finset α} (π : Finpartition S) :
    (mobius (Finpartition S) (singletonsPartition S) π : ℤ) =
    ∏ B ∈ π.parts, ((-1) ^ (B.card - 1) * (B.card - 1).factorial)
```

stating Stanley's evaluation (Stanley *Enumerative Combinatorics*
vol. 1, Prop 3.10.4) of the Möbius function from the bottom (the
finest partition into singletons) to an arbitrary partition `π`.

Together with the inversion-theorem application, the file is
approximately 400 LOC.

## Why this matters

The partition-lattice Möbius function is one of the foundational
combinatorial objects of enumerative combinatorics. Its evaluation
appears in:

1. **Cluster expansions in statistical mechanics** (Mayer-Ursell
   truncation, Brydges-Kennedy / Battle-Federbush forest estimates).
2. **Symmetric function theory** (Schur-Weyl duality, Kostka numbers).
3. **Algebraic combinatorics** (incidence algebras, generating functions).
4. **Quantum information** (entanglement-entropy decompositions).

Mathlib has `Mathlib.Order.Mobius` (general poset Möbius function),
`Mathlib.Combinatorics.SetFamily.Partition` (the partition object),
and `Mathlib.RingTheory.PowerSeries.WellKnown` (which uses inversion
implicitly), but **the explicit evaluation of the partition-lattice
Möbius function is not formalised**. This PR fills that gap.

The downstream Yang-Mills formal verification project consumes this
inversion as the algebraic step that defines the **truncated cluster
activity** in the Brydges-Kennedy expansion. See `BLUEPRINT_F3Mayer.md`
of that project for the application.

## Statement details

The PR introduces:

1. `singletonsPartition S` — the finest partition of `S` (every
   element is its own block). May reuse an existing Mathlib name.
2. `mobiusFunction_singletons` — the explicit evaluation theorem.
3. `mobius_inversion_singletons` — the inversion theorem in the form
   most useful for cluster-expansion applications:
   ```lean
   if  f(S) = ∑ π, ∏ B ∈ π.parts, g(B)
   then g(S) = ∑ π, ∏ B ∈ π.parts, μ_B · f(B)
   where μ_B = (-1)^(|B|-1) · (|B|-1)!
   ```

## Proof outline

**`mobiusFunction_singletons`**:
By induction on the partition structure. Base case: π = singletons,
mobius = 1, RHS = ∏ over singletons of (-1)^0 · 0! = 1. ✓

Inductive step: pick a block B of π with |B| ≥ 2. Use the recursion

```
∑_{σ : ⊥ ≤ σ ≤ π} mobius ⊥ σ = δ_{⊥, π}
```

(definition of Möbius inversion) restricted to refinements of π
inside B. Solve for mobius(⊥, π) and apply the inductive hypothesis
to all proper refinements.

The classical identity needed:

```
∑_{partition of {1,...,n}} ∏_{block sizes b₁,...,bₖ} (-1)^(bᵢ-1) (bᵢ-1)!
  = (-1)^(n-1) (n-1)!
```

This is the value of the partition-lattice Möbius function at the
top, established via the exponential generating function

```
∑_{n≥1} (-1)^(n-1) (n-1)! · x^n / n!  =  log(1 + x)
```

and the multiplicative property of generating functions over
partitions.

**`mobius_inversion_singletons`**:
Directly applies the general Möbius inversion theorem
`Mathlib.Order.Mobius.mobius_inversion` (or its analogue) to the
partition lattice using the evaluation above.

## Related Mathlib infrastructure

This PR depends on:

- `Mathlib.Combinatorics.SetFamily.Partition` (`Finpartition`)
- `Mathlib.Order.Mobius` (general Möbius function)
- `Mathlib.Algebra.BigOperators.*` (sum/product manipulation)

It would benefit from:

- A clean exponential generating function API, if one is being added.
- The Cayley formula for spanning trees (related but separate;
  Mathlib gap, not addressed here).

## Backwards compatibility

This PR adds new content only. No existing API is modified.

## Tests

A short test file verifies:

- `mobiusFunction_singletons` evaluates to 1 on the singleton
  partition (consistency check).
- For `S = {0, 1, 2}` with the partition `{{0,1}, {2}}`:
  `mobius(⊥, π) = -1 · 1 = -1` (from the block of size 2 contributing
  -1·1! = -1, and the singleton contributing 1).
- The inversion theorem recovers `g({a, b, c})` correctly for a
  small explicit example.

## License

Apache 2.0, with copyright assigned to the Mathlib community as per
standard contribution policy.

## Author

Lluis Eriksson (lluiseriksson@gmail.com), as part of the Yang-Mills
formal verification project. Drafted with assistance from Anthropic
Claude (Cowork mode).

## Pre-PR checklist

- [ ] Run `lake build` and confirm zero errors.
- [ ] Confirm `#print axioms mobiusFunction_singletons` returns
      `[propext, Classical.choice, Quot.sound]`.
- [ ] Run `mathlib-update-references`.
- [ ] Verify naming aligns with current Mathlib partition theory
      conventions (the `singletonsPartition` may need renaming).
- [ ] Add docstring linking to Stanley reference and to typical
      cluster-expansion application.

## Combination with PR 1 and PR 2

Together with the previous PR drafts:

- **PR 1** (`AnimalCount.lean`): combinatorial bound on connected
  subgraph counts.
- **PR 2** (`PiDisjointFactorisation.lean`): disjoint-coordinate
  factorisation of product measures.
- **PR 3** (this PR): Möbius inversion on the partition lattice.

The three together cover most of the missing Mathlib infrastructure
needed by the cluster-expansion approach in the Yang-Mills project.
The Brydges-Kennedy estimate itself (the "analytic boss" of the
F3-Mayer chain) remains in-repo because of its size and specificity.

## Status note from the requesting project

The requesting project (`THE-ERIKSSON-PROGRAMME`) has explicitly
**deferred** this PR — its in-repo workaround uses the Brydges-Kennedy
interpolation formula directly, which bypasses Möbius inversion via
a tree-based reorganisation. So this PR is **not blocking** the
Yang-Mills project. It is offered as a clean upstream contribution
of independent value to the broader Mathlib community.

The Yang-Mills project will benefit from this PR if it lands, but
will not be blocked by its absence.

---

*PR drafted 2026-04-25 by Cowork agent (Claude) on behalf of
Lluis Eriksson.*
