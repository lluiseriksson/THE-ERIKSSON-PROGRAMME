# Exact-PDF reading and objections, 29 October 2026

Artifact reviewed: *Exact-Kernel Fourier Families Obstruct Every Penalty Factored
Through a Block Map in a Flat Lattice Gauge Form*, internal edition 1.4,
public ai.viXra 2608.0015v1 / AIRR ARR-2026-7EPM3V3DP796BBRR v1.
Exact PDF SHA-256:
`48b2b725422263a272d9862621fa723d3d82c9d186dd7151be39c6ff1e3ff2e7`.

## Model assessments and review context

This is an operational reading by the same Codex assistant consolidating the
work. The host identifies the assistant as belonging to the GPT-6 family; an
exact served model identifier and reasoning setting are not exposed in this
reading record. No different named model, independent reviewer, journal referee,
numerical score, acceptance, or publication decision is attributed to it.

Context supplied to the reader included the earlier source-scope audit, the two
fresh-clone focal reproduction reports, the existing manuscript text and the
current repository. The reader was therefore not blind to the programme or its
results. No historical score was inherited, and no assessment was repeated to
raise a score. This record is unsuitable as a substitute for an AIRR-required
named-model screening report.

## Exact-artifact visual check

The public mirror PDF was downloaded in a dedicated Colab CPU/high-RAM runtime,
its exact hash checked before rendering, and all thirteen pages rendered with
PyMuPDF 1.26.7. Four labelled contact sheets cover pages1-4,5-8,9-12,13; every
sheet was visually inspected. Rendering ran14:35:47.398234-14:35:52.598071UTC,
29October2026, followed by automatic release and an observed reconnect control.
There was no Lean build or Windows rendering computation in this unit.

The render evidence ZIP SHA-256 is
`e5d286e94e35f97e9c03db88b62a389d5ca168b5da0f897bcea54dba86cb9d02`.
All seven listed file hashes were checked after recovery. The PDF has legible
equations, continuous page numbering, bibliography and no observed black glyphs,
overlapping formulae or clipped mathematical statements at the inspected scale.
This is a visual check, not validation of every hyperlink target or PDF tag.

Layout objections to resolve in a future edition:

1. The abstract spills onto page2, splitting its final formalization/scope
   paragraph. Shorten it and keep the important scope limitation together.
2. Table1 on page10 wraps long Lean identifiers across arbitrary character
   boundaries. Replace them by short labels plus a machine-readable declaration
   map or a landscape appendix; do not silently change declaration names.
3. The reproduction commands on page11 wrap after `lake build` and `lake env
   lean`. Supply a copyable script or notebook and the full source-tree anchor.
   The merged reproduction supplement now provides those missing instructions.

## Mathematical reading and limitations

The first-mode cancellation, zero divergence, Hodge energy and quantifier
contradiction are consistent with the source stencils and the reproduced focal
endpoint. In Section5, real orthogonality follows from the root-of-unity sum.
The diagonal quadratic form also needs orthogonality of the shifted derivative
profiles, not merely the norm identity for each separate E_r. That calculation
follows by multiplying each Fourier amplitude by its frequency difference;
it should be written explicitly in a revision. This is an exposition objection,
not a counterexample found to Theorem5.1.

The finite-scale repair identity and necessary bound are formalized endpoints.
The trigonometric closed form, higher-frequency multiplicity, asymptotic liminf
and witness-line equivalence have analytic proofs; they must not be bundled
into a claim that the complete manuscript is machine checked. Likewise, the
reproduced factorized endpoint uses dimension four. The abstract's generic
formalization sentence would benefit from stating this dimensional boundary.

The PDF already distinguishes uniformity in L at fixed N' from a limit in N'
at fixed L, and necessary witness-channel repair from full-space sufficiency.
It explicitly disclaims a contradiction with restricted gauge propagators and
any continuum or physical mass-gap result. These qualifications must survive
editing and publicity.

## A repair route now closed analytically

Section10 allows that a changed block observable may lift the exhibited witness,
while leaving full-space coercivity open. The accompanying
[coarse-rank note](FLAT-COARSE-RANK-OBSTRUCTION-20261029.md) closes a specified
subcase: on this unrestricted unit-spacing flat domain, replacing Q by any
linear measurement into a fixed-dimensional coarse space cannot repair the
uniform full-space gate, even if it detects this particular witness.

The proof counts an entire low Fourier cube and intersects it with the kernels
of the measurement and any added bounded-rank fine operator. It does not use
the old Q's kernel or locality. This is a useful scope reduction, based on
classical rank-nullity and torus spectra, with no claim of a novel general
spectral principle. It should be grouped with the existing paper, not deposited
as a separate small-corollary paper. It is currently an analytic argument,
without a new Lean compilation or independent scientific assessment.

## Publication state and remaining work

The public exact-version page was checked on29October2026: it remains a
historical import, not assessed, with no supported exact-version model reports.
See the [existing public record](https://airr.science/papers/ARR-2026-7EPM3V3DP796BBRR/versions/v1/).
The new GitHub reproduction evidence does not itself change that status.

Before submitting a revised PDF, incorporate the source-tree recipe, explicit
formal/analytic boundary, author/model disclosure and the rank scope reduction;
then freeze its new hash, render it, and obtain the available authorized
exact-artifact reviews and historical-revision route. No duplicate ordinary
deposit, unsupported score, or administrative bypass is justified. No revised
PDF was submitted in this unit.
