# Point-source normalization: static route, not a compiler seal

The running FULL/mixed cold gate is independent of this note. No new Lean
claim, terminal field, inverse identity or window15 attainment is recorded.

## Reusable exact inputs inspected

- `cmp99Flat_normalizedCharacterAverage_integerResidue` in
  `BalabanCMP99FlatFiniteGridAliasing` is a normalized character sum over
  `ZMod N` in each coordinate. It selects a residue class, not equality of
  two arbitrary integer lattice sites.
- `cmp89Eq245CenteredAliasIntegers_eq_Ico` in
  `BalabanCMP89Eq245CenteredAliasCycle` identifies the printed alias set
  with N consecutive integers starting at `-floor(N/2)`.
- `cmp89Eq245CenteredAliasVectorPiEquiv` in
  `BalabanCMP89Eq245CenteredAliasVectorCycle` gives the actual product of
  these scalar fibres. It does not by itself identify this product with a
  finite Fourier character convention.

## Finite remaining normalization route

1. Construct reduction modulo N as an equivalence from the actual centered
   scalar alias interval, using its length N. Lift it coordinatewise.
2. Prove the character dictionary for the literal exponential alias phase;
   do not replace that phase by a ZMod character by definition.
3. Apply character orthogonality. The unnormalized alias sum contributes
   N^d when the integer displacement is divisible by N coordinatewise,
   and zero otherwise. This only selects congruence, not a point source.
4. On the divisible branch, use the remaining normalized Brillouin integral
   with integer displacement divided by N to select equality to zero.
   This is where the residue selector becomes the infinite-lattice delta.
5. Track the resulting N^d = xi^(-d), xi=1/N, against the separately
   specified counting/density normalization. Cancel that factor exactly
   once when constructing the actual physical action.

These are proof obligations, not proofs written or compiled in this note.
In particular the existing finite-grid aliasing theorem must not stand in
for step4: a congruence-class sum is not the infinite-lattice point-source
equation. No symmetry under negation of the even half-open alias set is
needed or assumed.

The alias fibre equation must use the mass-uniform solution-domain
producer already identified in the mixed-boundary map, rather than copying
an older mass-positive convenience theorem. The real/complex action
dictionary remains a separate visible obligation.

Counters: 20/41; TermSource=0; window15 open.
