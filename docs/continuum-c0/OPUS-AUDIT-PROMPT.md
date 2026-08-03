# CONTINUUM-C0 final external-audit prompt

Read every file under `YangMills/Continuum/` and
`docs/continuum-c0/`. Read imported repository definitions when needed.
This is read-only: do not edit anything and do not delegate.

Audit these hard gates:

1. no arbitrary `ContinuumState` or supplied limit functional;
2. the state sequence is definitionally produced by repository
   thermodynamic states;
3. explicit `aₙ → 0` and observable maps;
4. non-circular pointwise weak convergence plus uniqueness;
5. proved limit stability;
6. a compiled `d=4`, `SU(2)` two-point theorem whose actual constructed
   Gibbs state uses the scale-indexed coupling `β k`;
7. precisely typed tightness, compatibility, nontriviality, regime, and
   separated-correlation obligations;
8. no `sorry` or project axioms; and
9. no false continuum-Yang--Mills or Clay claim.

Adversarially test:

- `embed n F := const 0`;
- an empty positive-half family;
- identity reflection;
- confusion between thermodynamic-volume and scale indices; and
- whether deleting the scale-indexed state dependence would leave the
  claimed endpoint unchanged;
- whether the canonical-axis correlation theorem really discharges its
  inner volume geometry before taking the scale limit;
- the proof and arithmetic of the `1/8450` KP wall.

Distinguish blocking defects from honestly exposed frontiers. Return a concise
audit with verdict `PASS` or `FAIL`, blocking findings, nonblocking findings,
and exact `file:line` references.
