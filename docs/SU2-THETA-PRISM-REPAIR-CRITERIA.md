# (16) Repair criteria for PR #43

Status: **PRE-REGISTERED BEFORE REPAIR BUILDS, ORACLES, AND MUTATION RUNS**

This is a manufacturer repair record for the adversarial failure of the
SU(2) theta-prism artefact.  It is not an audit verdict and cannot certify the
repair.  The source branch was verified at
`0ac9b18c98cf12b305611fd74087816a3b5f1e32`; the audited base is
`26306b8f30e826b0bcb7c4caf6a5a42473ab5fd8`.

## Fixed acceptance criteria

1. Define the Borel measurable space on `CellConfiguration` and a normalized
   eight-coordinate product of the concrete SU(2) Haar probability measure.
   Prove mass one and finiteness.  Keep ordinary product-measure Fubini
   separate from Haar-invariant coordinate changes.
2. Replace the arbitrary `TwiceSpin -> SU2 -> Real` family at the public
   endpoint by explicitly indexed, representation-backed SU(2) character
   data.  State exactly which spins are constructed.
3. Classify each original field (`traceReality`, `characterBound`,
   `haarSchur`, `fubiniCoordinates`, `normMoments`, `coefficientSeries`, and
   `weightMeasurability`) as proved, genuinely loaded, or open.  Exhibit a
   concrete `ManufacturingTechnicalInputs` value at `beta = 1`; do not claim a
   uniform endpoint unless a value is constructed for every `BetaDomain`.
4. Provide a front-door theorem that supplies the concrete cell Haar measure
   and concrete character data itself.  Preserve the established
   combinatorics, witness, singlet `1/2`, and formal arithmetic unless a
   connection proof requires a localized edit.
5. Replace Python `assert` checks by explicit nonzero-exit checks.  Mutation
   tests must reject both `1/2 -> 1/3` and an attempted all-beta domain under
   ordinary Python and `python -O`.  The syntactic validator must reject
   headline-bearing fields, including spacing/name variants of
   `witnessNormSq = 3/4` and `CompleteUOrthogonality`; it will be described as
   a syntactic guard, not semantic honesty.
6. Build every theta-prism target and `YangMillsCore`; run the complete axiom
   oracle; require no project axioms, `sorry`, `admit`, or `sorryAx`, and allow
   only `propext`, `Classical.choice`, and `Quot.sound` in oracle headlines.
   Record exact commands, measured jobs, stdout/stderr, toolchain, EOL policy,
   source hashes, binary hashes, and all measured failures.
7. Re-run validation from a fresh checkout of the published refs.  Keep PR #43
   draft, update only its existing remote branch by explicit fast-forward,
   and stop for a new blind external audit.  No merge, paper claim, programme
   Gate 7 claim, or manufacturer self-certification is permitted.

## Evidence labels

- **EXACTO**: proved directly by checked Lean terms over concrete definitions.
- **CERTIFICADO**: conditional on an explicitly named genuine analytic input.
- **VERIFICADO**: reproduced command/output evidence only.
- **ABIERTO**: not discharged by the published artefact.

Campaign results may not alter the constants `1/2`, `3/4`, `1/16`, or
`1/512`, weaken the three-branch witness, or enlarge the beta domain.  Every
measured failure remains in the final transcript or repair log.
