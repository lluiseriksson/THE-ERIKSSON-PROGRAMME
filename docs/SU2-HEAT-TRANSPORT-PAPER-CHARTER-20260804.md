# SU(2) heat transport paper charter (2026-08-04)

## Frozen inputs

- Parent starting point: `e6b672dda3e41da25a22178a7ef73ab8e7f8edb7`.
- Parent branch: `codex/48-su2-heat-paper`.
- `main` was fetched and was already contained before fabrication.
- Exact two-dimensional satellite: `lean-2d-yang-mills` at
  `05c4ec316cb9aa295416670a2578b1c2e77e1c36`.
- Shared Mathlib revision:
  `07642720480157414db592fa85b626dafb71355b`.

## Published inputs, not novelty claims

The satellite already proves the concrete normalized-Haar SU(2) character
convolution law, the infinite heat-kernel convolution semigroup, Migdal
two-face merging, and the exact finite-cellulation simple-loop Casimir law.
The parent already proves the abstract measure-decay-to-operator-gap theorem
`YangMills.OS.Dobrushin.abstract_uniform_gap` and the exact finite SU(2)-inhabited
witness `YangMills.OS.Dobrushin.SU2Transport.exact_transport_witness`.

The paper must cite these results as inputs.  Re-exporting or renaming them is
not a contribution.

## New theorem lane

The deliverable will prove, without a project-local axiom or transported
conclusion hypothesis:

1. The concrete infinite SU(2) heat kernel acts diagonally on every actual
   Chebyshev character under normalized Haar convolution.
2. The eigenvalue is the exact Casimir factor
   `exp (-t * n * (n + 2) / 4)`.
3. Outside the vacuum label `n = 0`, the fundamental label `n = 1` is the
   sharp slowest mode for every `t > 0`, with rate `exp (-3t/4)`.
4. The already-frozen two-holonomy Dobrushin witness uses exactly this imported
   continuous heat eigenvalue, so the finite endpoint is a faithful sharp-mode
   quotient rather than an arbitrary rate-labelled Markov chain.

The load-bearing non-vacuity attacks are: the fundamental character is not the
zero function, the projected finite-witness operator is not zero, the two SU(2)
holonomies remain distinct, and the desired decay/gap is never assumed.

## Scope boundary

The paper will not claim:

- a construction of four-dimensional continuum Yang--Mills;
- a new proof of the satellite's exact area law or heat semigroup;
- Peter--Weyl completeness in Mathlib;
- an operator-norm theorem on the completed full Haar `L^2` class space unless
  that completion is actually implemented and checked;
- a thermodynamic limit or a new interacting infinite-volume state.

The two-holonomy finite witness is an exact sharp-mode quotient/interface, not
a claim that the compact group is finite or that the full completed Haar
operator has been truncated in operator norm.  The paper's headline and
abstract must say this explicitly.

## Verification gates

1. `lake update` resolves the satellite to the frozen SHA.
2. The new bridge target builds in Colab Pro+ CPU/high-RAM, no GPU.
3. `YangMillsCore` builds with a materialized `.olean` for the bridge.
4. `#print axioms` for every decisive theorem contains no project-local axiom
   and no `sorryAx`.
5. The manuscript compiles without undefined citations/references.
6. Every page of the final PDF is rendered and visually inspected.
7. The final branch, source, oracle, TeX and PDF are frozen with byte counts and
   LF/CRLF hashes before external audit.

The fabrication task does not issue its own terminal novelty or correctness
verdict.
