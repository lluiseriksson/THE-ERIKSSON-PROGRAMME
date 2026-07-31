# Integration note for the Paper 13 owner

## Current structural mismatch

The published `ReflectionSplitting` API cannot be instantiated by SU(2):

1. `Config N Edge` is definitionally `Edge → ZMod N`.
2. `hol` is an incidence-weighted additive sum, whereas SU(2) plaquette
   holonomy is an ordered noncommutative product.
3. The consumer theorems require `[Fintype Half]` and use `Finset.sum`;
   SU(2) is a compact infinite group and its pairing uses Haar integrals.
4. `IsCharCombo` has a finite representation index.  The exact exponential
   Wilson factor has an infinite expansion for `β > 0`.
5. `Config ≃ Half × Half` can intertwine reflection with swap only when the
   edge involution is free.  Fixed or crossing edge variables require
   `Config ≃ Half × Cross × Half`.
6. `reflConfig` is a pure edge permutation; physical oriented reflection also
   applies group inversion on reflected links.

Consequently, importing `ReflectionSplitting.lean` does not provide a typed
route to the SU(2) endpoint.  This is not a missing instance and must not be
worked around by assigning a false `Fintype SU2`.

## Requested downstream seam

The integrator can connect the owned SU(2) producer after Paper 13 exposes an
integral-valued analogue with:

- an arbitrary compact configuration group;
- ordered plaquette holonomy;
- a measure-preserving split into two halves;
- a separate crossing-variable factor, with swap on the halves and inversion
  on crossing variables;
- a direct PSD-kernel input or a dominated limit of finite rank-one
  combinations;
- an integral pairing rather than a finite sum.

No change to the finite `ZMod N` theorem is required.  A sibling theorem or a
group/measure-parametric generalization is sufficient.

The old theorem is recovered as the special case `Cross = Unit`; this task
does not claim the converse.

## Ownership

This task does not edit `YangMillsCore.lean`, `oracle_check.lean`, any global
ledger, or any Paper 13 source.  The integrator should add imports and oracle
lines only after reviewing the new modules and resolving the seam above.

## Oracle coverage

The global build/oracle does not currently see these modules.  In particular,
`YangMills/L0_Lattice/SU2Basic.lean`, a legitimate dependency of this lane, is
not imported by `YangMillsCore.lean`.  This task therefore carries its own
executable oracle at `docs/su2-os/SU2OSOracle.lean` and its exact transcript.

After integration review, the owner of the global files must:

1. import the SU(2) endpoint (or the selected lower-level modules) from the
   global import surface;
2. add the headline `#print axioms` checks to the global oracle; and
3. decide whether the Paper 13 integral seam is a sibling theorem or a
   group/measure-parametric generalization.

None of those integration steps is claimed by this branch.
