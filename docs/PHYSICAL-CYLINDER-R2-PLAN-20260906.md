# R2: a finite physical Wilson cylinder

Registered 6 September 2026 before implementation, at main
`02fdbb7bf83a9c3e6abc48e20d3982ab66b4963b`.

## Scope and acceptance

Build the R2 continuation of the [reflection campaign](PHYSICAL-REFLECTION-PLAN.md):
two spatial links on each of two time slices and two shared crossing links.
The underlying finite cylinder has four vertices, six independent positive
edges, twelve oriented edges and two plaquettes. Its Euler characteristic is
zero, so the satellite's certified disk-amplitude theorem does not apply.

The first source gate must provide:

1. Explicit endpoints, edge reversal, closed plaquette boundaries and a
   concrete `FiniteLatticeGeometry` instance.
2. An embedding of all six independent group variables into `GaugeConfig`,
   with exact plaquette holonomies and a geometric reflection on vertices,
   oriented edges and configurations.
3. The actual product of six normalized SU(2) Haar factors, an inversion/swap
   reflection that preserves that measure, and a literal two-plaquette Wilson
   density. Prove continuity, integrability and positive normalization.
4. A normalized Gibbs probability measure, reflection invariance of physical
   expectations and a product-Haar integral identity for the reflected form.
   Any kernel rewrite must retain both shared crossing variables.

These are R2 targets, not accepted results. No positivity of the reflected
form, positive centered norm, transfer construction or 4D result follows just
from positive density, reflection invariance or a nonconstant loop observable.
Those are later R3–R5 obligations. Source must remain outside `YangMillsCore`
until a separately recorded integration checkpoint.

## Prior work to reuse

- Mother: `PhysicalWilsonSquare.lean` for local boundary words;
  `GaugeConfigurations.lean` and `WilsonAction.lean` for configuration and
  gauge covariance; `SUN_StateConstruction.lean` for normalized Haar;
  `TwoTransporterHaarProjection.lean` for the concrete Wilson weight and its
  conjugation/inversion symmetry.
- Satellite at `a1fbea97cbe673d383dbb4bc5e2a2fb70dbf190a`:
  `SU2CharacterConvolution.lean` and `SU2GlobalEdgeGaugeFixing.lean` already
  derive right/inversion invariance of normalized SU(2) Haar from Mathlib's
  compact Haar uniqueness. Adapt only the short measure-instance bridge to
  the mother's `sunHaarProb`; it is reused infrastructure, not new analysis.
- Pinned Mathlib: product measure preservation, measurable equivalences,
  Fubini, compact-support integrability and exponential tilting. Do not
  replace integrability with the totalized-zero integral convention.

## Verification and publication

All Lean/Lake/oracles run in this task's own CPU/high-RAM Colab runtime.
Prepare source and commands while disconnected; preserve exact source hashes,
actual exits and complete logs, and release the runtime at the end of each
execution unit. Retain failed diagnostics separately. A source gate requires
the full unchanged core build, focused compilation and axiom readouts for
every new headline. A full global oracle replay is recorded separately;
terminal status still requires two fresh reproductions at one source SHA.

Keep this plan, the campaign table, verification ledger, news and dashboard
synchronized with observed evidence. No hRpoly source, acceptance counter,
frozen SU(2) lane, certificate hash or canonical proof-state change is part
of this task.

## Evidence log

- 2026-09-06: continuation registered. Source and measure APIs inspected;
  no new R2 source or proof run exists at this registration checkpoint.
- 2026-09-06: two source modules drafted. The first fresh Colab diagnostic
  failed in concrete geometry instance elaboration; the measure module and
  oracles were not reached. The [failure record](evidence/physical-cylinder-r2-20260906/README.md)
  preserves exact hashes, actual exit, timing and the complete notebook archive.
  A corrected draft is prepared; R2 remains unverified.
- 2026-09-06: the second fresh diagnostic reduced geometry failures to two
  plaquette index annotations. Its separate manifest and complete archive
  are retained in the same evidence directory/notebook. A third prepared
  run includes those annotations and the explicit Wilson-action dictionary;
  no R2 acceptance is claimed before its results are observed.
