# The gap-refinement challenge

## Status

This note isolates a **logical obstruction and acceptance criterion** for any
Yang--Mills mass-gap campaign. It does not prove the missing constructive-QFT
input `hRpoly`, construct the continuum Hamiltonian, remove a regulator, or
establish the Clay mass gap.

## The `N + 1` move and its spectral dual

In the children's largest-number game, a proposed maximum `N` is defeated by
`N + 1`. For a positive spectral gap, the order is reversed: a proposed lower
bound `Delta > 0` is defeated by one physical excitation satisfying

```text
0 < E < Delta.
```

Thus the spectral counterpart of the `N + 1` move is an **arbitrarily smaller
positive excitation**.

The Lean module `YangMills/Paper/GapRefinementChallenge.lean` formalizes

```text
arbitrarily small positive excitations
  -> no positive energy gap.
```

Under the premise that every declared excitation has positive energy, it also
formalizes the converse.

## The regulator quantifier trap

For a family `excitation r E` indexed by a partition, lattice spacing, volume,
or other regulator, compare

```text
forall r, exists Delta_r > 0,
  forall E, excitation r E -> Delta_r <= E
```

with

```text
exists Delta > 0, forall r E,
  excitation r E -> Delta <= E.
```

The first statement says that every fixed approximation is gapped. The second
gives one gap that survives all refinements. The first does **not** imply the
second.

The module proves an explicit counterexample. Index stages by positive real
numbers `delta`, and let the only excitation at stage `delta` have energy
`delta / 2`. Every stage has a positive gap, but a candidate uniform gap
`Delta` is defeated by choosing the stage `delta = Delta`.

## Consequence for this repository

`lattice_mass_gap_of_clustering_uniform` in
`YangMills/Paper/ClusteringToGap.lean` supplies one rate for all separations at
fixed lattice data. That is an essential lattice statement, but it is not yet
uniform in continuum and thermodynamic regulators because those limits and
the OS/Wightman reconstruction are not constructed in the repository.

The same quantifier discipline should govern the `hRpoly` campaign:

1. A bound at one scale or one finite partition is insufficient.
2. Constants that collapse to zero under refinement cannot yield a continuum
   mass gap.
3. Producer estimates must be uniform in every regulator later removed, or
   come with a theorem proving survival of the positive lower bound in the
   limiting construction.
4. A contradiction proof still needs a Yang--Mills-specific analytic theorem
   ruling out arbitrarily small gauge-invariant continuum excitations. The
   order-theoretic contradiction alone supplies no such theorem.

This makes the idea valuable as a **falsification test** for proposed proofs,
without misrepresenting it as the missing activity estimate or continuum
construction.

## Verification

After applying the patch:

```bash
lake build YangMillsCore
echo 'import YangMillsCore
#print axioms YangMills.not_hasPositiveEnergyGap_of_arbitrarilySmallPositiveExcitations
#print axioms YangMills.not_hasUniformPositiveEnergyGap_of_refinementsProduceArbitrarilySmallPositiveExcitations
#print axioms YangMills.halfScaleExcitation_stagewise_but_not_uniform' > _gap_oracle.lean
lake env lean _gap_oracle.lean
rm _gap_oracle.lean
```

Expected oracle: `[propext, Classical.choice, Quot.sound]` or purer.

## Sources

Arthur Jaffe and Edward Witten, *Quantum Yang--Mills Theory*, official Clay
problem description. It defines a mass gap by absence of Hamiltonian spectrum
in `(0, Delta)` and notes the possible role of a uniform gap for finite-volume
approximations:

<https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf>

Toby Cubitt, David Perez-Garcia, and Michael M. Wolf,
*Undecidability of the Spectral Gap*:

<https://arxiv.org/abs/1502.04573>

The latter concerns broad quantum many-body Hamiltonian families. It is not an
undecidability result for four-dimensional Yang--Mills.
