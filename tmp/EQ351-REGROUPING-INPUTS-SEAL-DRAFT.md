# Eq. (3.51) canonical regrouping-input seal draft

Status: evidence template only.  It does not retire PRE-VALIDATION, move
`20/41`, attain window 15 or construct a `TermSource`.

## Dependency gate

The source checkpoint must descend from a cold, selectively sealed Eq. (3.60)
regional-stencil checkpoint.  The promoter rejects the checkpoint unless all
eight source/audit files in that gate are present and contain no
`PRE-VALIDATION:` marker.

## Exact compiler scope

The gate contains three source/audit pairs and sixteen distinct axiom
readouts:

1. `BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion` — `1`;
2. `BalabanCMP99Eq351PhysicalComplexNegativeBondFactorization` — `11`;
3. `BalabanCMP99Eq351PhysicalComplexCovariantDivergence` — `4`.

It then builds a cold `YangMillsCore`.  The archive verifier accepts only
`propext`, `Classical.choice` and `Quot.sound`, rejects `sorryAx` and
`ofReduceBool`, and hashes every tracked source/audit blob against the exact
source checkpoint.

## Semantic claim

A successful seal certifies only that the following source ingredients are
constructed internally:

- the positive-bond exponential-adjoint expansion with its named nonlinear
  remainder;
- the negative-bond factorization using the canonical oriented physical
  perturbation, including the backward-stencil rewrite from the inverse
  positive link by `GaugeConfig.map_reverse`;
- the complex covariant divergence built from that same perturbation.

It accepts no caller-supplied perturbed background, oriented field, diagonal
field or factorization equality.

## Explicitly outside the seal

- `BalabanCMP99Eq351ComplexLaplacianRegrouping`;
- the literal three-species pointwise identity of (3.51)--(3.53);
- the printed `4*d`, `2*d`, `8*d` pointwise estimate (3.54);
- owner-weighted transport, the regional resolvent, window 15 and rows 23--24;
- every `PreEq136` field and every `TermSource` inhabitant.

Only a verified archive for the exact promoted SHA may authorize the
six-notice selective sealer.
