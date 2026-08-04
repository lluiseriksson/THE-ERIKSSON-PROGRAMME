> **Scope limitation — read before the title.** In the present producer,
> `Cross` is gauge-pure and does not participate in the effective weight or
> pairing; its inversion is not exercised. This note does not claim a
> physical cut or a derived lattice plaquette factorization. These geometric
> limits do not weaken Haar positivity for every continuous observable or the
> sharp `β/4` theorem.

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

The current auxiliary equality is weaker than the downstream seam described
below: `su2OnePlaquetteCutWeight` is defined in product form, and
`su2OnePlaquetteCutWeight_eq_undressedKernel` only removes its common
gauge-pure transporter. It does not establish a geometric factorization.

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

The existing finite `ReflectionSplitting` theorem is not consumed here. This
task neither proves that the proposed seam exists nor claims a converse.

## Ownership

This task does not edit `YangMillsCore.lean`, `oracle_check.lean`, any global
ledger, or any Paper 13 source.  The integrator should add imports and oracle
lines only after reviewing the new modules and resolving the seam above.

## Oracle coverage

The global build/oracle does not currently see these modules.  In particular,
`YangMills/L0_Lattice/SU2Basic.lean`, a legitimate dependency of this lane, is
not imported by `YangMillsCore.lean`.  This task therefore carries its own
executable oracle at `docs/su2-os/SU2OSOracle.lean` and its exact transcript.
Consequently, a green lane target must never be reported as a green global
core build.

After integration review, the owner of the global files must:

1. import the SU(2) endpoint (or the selected lower-level modules) from the
   global import surface;
2. add the headline `#print axioms` checks to the global oracle; and
3. decide whether the Paper 13 integral seam is a sibling theorem or a
   group/measure-parametric generalization.

None of those integration steps is claimed by this branch.
