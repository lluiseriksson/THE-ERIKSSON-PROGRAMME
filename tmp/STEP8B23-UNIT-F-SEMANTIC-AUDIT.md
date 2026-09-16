# Step 8b.23 Unit F — static semantic audit

Status: **STATIC ONLY — NOT COMPILER-VERIFIED**.

Scope:

- `BalabanCMP89CenteredPeriodicL1ResidueSum.draft.lean`
- `BalabanCMP99CenteredPeriodicEndpointDictionary.draft.lean`
- `BalabanCMP99PhysicalGreenZeroResidueBound.draft.lean`
- `BalabanCMP99DiagonalFiniteGreenOwnerBound.draft.lean`

## Gate F1 — periodic residue sum retains centered decay

**PASS (static).**

For a representative satisfying `2*abs(u) <= P`, the one-dimensional bound
keeps `exp(-delta*abs(u))` and pays one transparent factor
`2/(1-exp(-delta*P))`. Reflection handles the negative half without assuming
signed equality at the antipodal seam. Finite-dimensional factorization is
exact, so no volume factor enters.

At physical values `P = K*N` and `delta = rho/K`, the geometric ratio is
`exp(-rho*N)`. The uniform form uses only `N >= 1` and retains fine decay at
rate `rho/K`.

## Gate F2 — centering and residue-zero reindexing are exact

**PASS (static).**

- The canonical representative uses the signed centered-alias convention
  appropriate to the residue of `u`, not `-u`.
- The integer carry and affine decomposition are explicit.
- At an even antipodal residue, only equality of magnitudes with
  `ZMod.valMinAbs` is claimed; signed equality is deliberately avoided.
- Translation by the carry is an explicit equivalence of `Z^d`.
- The zero finite-grid residue subtype is shown equivalent to `Z^d` by exact
  coordinate divisibility, not cardinality counting.
- The selected Step-8b.22 fibre is reindexed exactly into the centered
  periodic fibre before any estimate is applied.

## Gate F3 — the physical Green supplies the generic coefficient bound

**PASS (static).**

`norm_cmp89Eq248PhysicalZeroMassGreen_le_signedLatticeWeight_draft`
specializes the literal normalized Green bound to zero mass. That theorem is
then supplied to the generic periodic-residue estimate; the physical Green
identity is not accepted as an abstract coefficient premise at the public
endpoint.

The resulting norm bound retains the centered representative and contains no
`N^4` factor. The norm of the actual complex tsum follows from summability of
the full literal Green coefficient family.

## Gate F4 — diagonal owner transport is explicit and limited

**PASS (static, with an essential scope boundary).**

- The periodic displacement is the literal coordinatewise shortest signed
  torus displacement.
- Re-centering preserves its exact `l1` length, including antipodal sign
  changes.
- The fine-to-owner comparison exposes the boundary term `2*(K-1)`.
- Exponential transport pays the exact scale-free boundary factor
  `exp(2*rho)`.
- The final theorem bounds the actual residue-zero physical Green coefficient
  sum by an explicit amplitude, geometric factor, boundary factor and owner
  exponential decay.

The theorem is intentionally **diagonal**: Green scale and owner-block side
are both `K` on `FinBox 4 (K*N)`. It does not identify this owner with the
final CMP99 source-localization owner at independent scales `(L,Klarge)`.

## Delimitation

Unit F closes item 4 of the post-Gate-7 route only. The separated-scale owner
dictionary, regional `B0`, the complete physical operator identification,
window-15 attainment and terminal fields remain open. Treating the diagonal
bound as the regional bound would be a false scale identification.

## Static verdict

All four Unit-F gates pass statically, with the diagonal/separated-scale
boundary explicit in the public theorem and docstring. Promotion remains
blocked on Lean elaboration and axiom audit in the sanctioned remote
validation path.

