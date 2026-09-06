# Reuse audit: the ARR two-dimensional SU(2) disk paper

**6 September 2026.** Requested by the owner before extending the physical
reflection campaign. This is a source comparison, not an independent rebuild
or a mathematical correctness certification of the satellite.

## Sources and version boundary

- [ARR record ARR-2026-2PB36YR0B89WSB71](https://arr-research.github.io/papers/ARR-2026-2PB36YR0B89WSB71/):
  *A Machine-Checked Exact Evaluation of the Two-Dimensional SU(2) Heat-Kernel
  Lattice Model on Certified Finite Combinatorial Disk Cellulations: From Haar
  Measure to Conditioned Original-Edge Amplitudes*. The mirrored manuscript is
  dated 1 August 2026; the ARR page calls this a historical import and marks
  correctness, Lean reproducibility and novelty as not assessed.
- [Manuscript text preserved by ARR](https://github.com/arr-research/arr-research.github.io/blob/main/papers/2026/07/2P/ARR-2026-2PB36YR0B89WSB71/paper.txt),
  especially sections 1, 7, 8, 10 and 11.
- [Exact public proof source cited by the manuscript](https://github.com/lluiseriksson/lean-2d-yang-mills/tree/a1fbea97cbe673d383dbb4bc5e2a2fb70dbf190a).
  The default branch inspected on this date was the older
  `05c4ec316cb9aa295416670a2578b1c2e77e1c36`; the comparison below uses
  `a1fbea97cbe673d383dbb4bc5e2a2fb70dbf190a`, fetched explicitly.
- Mother-repository baseline:
  `ff9498df9bb13050a3c663103e4a0830e793c56f`.

The manuscript separates that public commit from a companion archive adding
`SU2BoundaryExamples.lean` and ten audit entries. Its reported **177** audited
declarations must not be attributed to the public commit, whose
`AuditMigdalClosure.lean` contains **167** `#print axioms` commands. The
concrete boundary-disk examples from the companion archive were not retrieved
or reproduced in this comparison. The satellite's `RELEASE_PROVENANCE.md` at
the cited commit still describes an earlier `52e0e6f...` release; exact theorem
sources take precedence over that historical prose.

## Existing work and the campaign decision

All satellite paths below are relative to `Lean2dYangMills/` at the pinned
commit. These are reusable prior results, not new results of this campaign.

| Required ingredient | Existing source and actual scope | Decision |
|---|---|---|
| Concrete SU(2), normalized Haar, orbital/character integration | `SU2Haar.lean`, `SU2Orbit.lean`, `SU2CharacterConvolution.lean` | Reuse the established analysis when needed; do not start another Haar or character construction. The mother repo already has its own `sunHaarProb` API. |
| Heat semigroup and a genuine shared-edge integral | `SU2HeatSemigroup.lean`: `su2HeatKernel_convolution`, `su2Migdal_twoFace_merge` | Cite as existing 2D heat-kernel results. These do not identify a Wilson-action weight with a heat kernel. |
| Original-edge orientation and gauge covariance | `SU2GlobalEdgeGaugeFixing.lean`: `edgeValue_gaugeTransform`, `dartHolonomy_gaugeTransform_of_closed`, `allFaceHolonomies_gaugeTransform` | Already available for certified disk cellulations. The mother repo also proves generic plaquette covariance in `L0_Lattice/WilsonAction.lean`. Remove the redundant new square gauge action and its covariance proof from R1. |
| Product-Haar gauge fixing on all original edges | `SU2GlobalEdgeGaugeFixing.lean`: `RootedSpanningTree.globalEdgeGaugeEquiv_measurePreserving` and `unreducedEdgeIntegral_eq_chordGaugeFixedIntegral` | Existing physical source bridge. Do not describe this as missing from the author's programme or rebuild its spanning-tree machinery. |
| Retention of the actual exterior holonomy | `SU2BoundaryConditionedGaugeFixing.lean`: `SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart.globalPhysicalBoundaryEdgeEquiv_measurePreserving`, `globalPhysicalBoundaryEdgeEquiv_apply_exterior` | Existing measure-preserving chart, retaining the complete boundary word. Use this construction as the reference for an honest change of variables. |
| Exact conditioned original-edge amplitude | `SU2PhysicalConstructionIntegral.lean`: `SU2BoundaryDiskCellulation.conditionedEdgeModelAmplitude_eq_heatKernel` | Closed in the cited source for its certified finite 2D heat-kernel disk model; do not recreate it as a new physical-bridge milestone. |
| Exact character area law | `SU2FiniteCellulation.lean`: `su2ConnectedDisk_simpleLoop_areaLaw_exact` | Existing endpoint on the schedule-independent connected-disk functional. For an original-edge consumer, compose the physical amplitude theorem and match the measures/normalization explicitly. |
| Obstruction from freely integrated crossing variables | Mother repo `OS/TwoTransporterHaarProjection.lean`: `su2Wilson_quadraticD_eq_partition_mul_mean_sq`, `su2Wilson_quadraticE_eq_partition_mul_mean_sq` | Existing Lean source for projection onto the Haar mean, documented in `SU2-TWO-TRANSPORTER-NOGO-20260731.md`. Do not recreate it or confuse it with the frozen positive reduced-kernel result. Its independent terminal audit remains pending in that record. |
| Geometric reflection of the mother's Wilson plaquette | No reflection/OS construction found in the inspected satellite source. The mother repo's existing SU(2) auxiliary cut explicitly has a common transporter that cancels. | Retain only the small R1 orientation/reflection adapter and four independent local variables. This is elementary group geometry, not a new gauge-fixing or area-law theorem. |
| Physical Wilson reflected Gram form, transfer construction and total observable family | Not supplied by the disk-amplitude endpoints; no such source declaration was found in the inspected satellite | R2–R5 stay open with their physical hypotheses visible. |

The same Lean release (`v4.29.0-rc6`) and Mathlib revision
`07642720480157414db592fa85b626dafb71355b` are pinned in both repositories.
That makes reuse technically plausible; it does not identify their different
measure definitions, configuration types or actions. No satellite dependency
or copied source tree is added by this checkpoint.

## What must still be proved for Wilson reflection

The satellite integrates products of heat kernels with positive face-area
parameters on certified finite disk cellulations. The reflection campaign
needs the mother's Wilson-action density and the actual oriented crossing
links. A heat-kernel convolution identity alone supplies neither the
Wilson reflected integral nor its positive Gram form. Any adaptation must
state the change of variables, product Haar, action, observable support and
normalization on the same object.

The retained R1 square has boundary word `b*r*t^-1*l^-1` and reflection
`(b,r,t,l) -> (b^-1,l,t^-1,r)`. Its dictionary to
`GaugeConfig.plaquetteHolonomy` is a local coordinate identity. It does **not**
construct an inhabited global reflected lattice, prove that every independent
four-tuple extends to every abstract `FiniteLatticeGeometry`, or transport a
global measure. Those stronger statements must not be inferred from the name
`ofPlaquette`.

The generic local identity is useful for the later Wilson kernel input
`(b*r, l*t)`, where the two crossing variables are distinct. The removed gauge
covariance theorem was redundant with already proved work. Consequently the
revised R1 oracle list has **nine**, not ten, declarations. The earlier
ten-declaration diagnostic remains a historical run on its original source
hash and is not evidence for changed source bytes.

## Consequence for the Millennium assessment

The mother repo also already contains the general free-transporter collapse
`Q(F) = Z * conjugate(mean(F)) * mean(F)`. For continuous Wilson data on a
compact group, the ordinary integral manipulations are justified. A centered
observable then has zero norm in that form. In the single open square, direct
Haar integration of a crossing edge gives the same mathematical obstruction;
the coordinate change to the existing formal D/E statements is not silently
claimed as an already compiled square-specific theorem. This is prior
obstruction evidence, not a new result of this audit.

R3 must therefore prove a strictly positive reflected norm, not merely choose
a nonconstant function. A finite spatial cylinder with two spatial links per
slice is a candidate geometry to examine before implementing the integral:
its two crossing plaquettes share the crossing links, and its half-slices
contain closed spatial loops. Neither those features nor the 2D paper alone
prove a nonzero OS sector. The frozen reduced SU(2) lane remains unmodified.

This paper adds important existing finite two-dimensional infrastructure to
the programme's inventory. It does not supply the four-dimensional continuum
construction, OS/Wightman reconstruction, or a positive physical spectral gap.
Its own section 11 excludes a continuum holonomy field, and its disk model
does not establish the 4D Wilson or hRpoly assertions. The campaign therefore
keeps the earlier assessment: hRpoly remains one necessary branch, and its
closure alone would not close the continuum problem.

The repository's historical Clay label remains **~0% (<0.1%)**, explicitly a
convention and not a measured completion percentage. No increase is inferred
from this reuse audit or the elementary R1 geometry.

## Recorded action

The campaign plan, news, handoff and dashboard are updated to link this audit.
R1 drops its duplicate gauge-covariance construction before publication. R2
will start from the existing Haar and gauge-fixing inventory, with the
Wilson-specific reflected integral as its target. No ARR assessment is
represented as a proof check performed by this task.
