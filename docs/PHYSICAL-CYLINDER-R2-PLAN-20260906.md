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

These targets were fixed at registration; the scoped R2 source milestone
now meets them (see the evidence log below). No positivity of the reflected
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

- 2026-09-06: the third diagnostic compiled the complete geometry but failed
  in the measure module. Its separate failure record is preserved. Measure
  repairs are prepared for a fresh gate; R2 is unverified.
- 2026-09-06: diagnostic 4 left one normalization rewrite error. Its full
  record is retained. An explicit integral equality replaces that rewrite
  in the next draft; 39 headline checks remain pending.
- 2026-09-06: diagnostic 5 exposed the cast/inverse identity needed by that
  calculation. The failure is retained; the next run adds the standard
  complex coercion lemma without changing the theorem's statement.
- 2026-09-06: gate 6 compiled both modules at 8171 jobs and passed all 39
  focal axiom readouts. The unchanged core passed at 8466 jobs and the full
  oracle import set at 8471 jobs. Consistency/dashboard checks passed.
  The global Lean run exited 0, but its wrapper returned FAIL after a parser
  omitted four primed theorem names. That original failure is preserved.
- 2026-09-06: a separate validation of the exact saved archive passed in
  normal and optimized modes, rejecting all 13 real field mutations in each.
  It confirms all 2854 global reports (26 axiom-free), in exact driver order,
  with only permitted standard axioms. No source or theorem changed and no
  second Lean run is claimed. The scoped R2 milestone is accepted; see
  [Addendum R2-20260906](VERIFICATION-LEDGER.md#addendum-r2-20260906--physical-wilson-cylinder-geometry-and-measure)
  and the [evidence index](evidence/physical-cylinder-r2-20260906/README.md).
  R2 is standalone, not terminally reproduced or independently audited.

## R3 reuse boundary identified during R2

Source inspection also located the existing
`YangMills.OS.su2WilsonCrossing_isHaarPSDKernel` in
`OS/SU2WilsonReflectionKernel.lean`. It proves the one-link Wilson kernel's
positive semidefinite Haar form at `beta >= 0`, using positive finite-rank
Taylor approximations. This is reusable substrate, not a new cylinder result.
The frozen module is unchanged.

For the cylinder, a later proof must connect the product kernel to the
physical integral through the upper-slice gauge average, retaining both
crossing links. It must then exhibit a strictly positive centered physical
norm, for example in a justified spatial-loop sector at `beta > 0`.
Neither the existing kernel theorem, positive density, nor reflection
invariance discharges that second obligation. No R3 proof run is claimed.
The [R3 continuation plan](PHYSICAL-CYLINDER-R3-PLAN-20260906.md) now registers
the two-sided gauge-average identity and spatial-loop centering/nonzero
requirements, with the existing sharp character analysis explicitly reused.
