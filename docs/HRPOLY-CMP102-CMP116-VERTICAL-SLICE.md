# hRpoly CMP102 → CMP116 vertical slice

**Date:** 2026-07-28  
**Branch:** `codex/cmp116-interacting-wilson-hessian`  
**Baseline audited:** `d8856a76`

## Purpose

This document replaces job count by a consumer-facing progress metric.  A
checkpoint counts as progress toward the terminal CMP116 theorem only when it
constructs, or removes a hypothesis from, one of the objects consumed by

```lean
cmp116Eq226PhysicalContour_singleScaleUVDecay_boundedHoles_of_boundaries
```

The terminal boundary objects are:

1. a physical contour source family `S`;
2. `CMP116Lemma3Eq229ScaleBoundary`;
3. `CMP116Lemma3PStageSourceScaleBoundary`;
4. `CMP116Lemma3WeightedPostPSourceScaleBoundary`;
5. the scalar decay profile `hprofile`.

The fifth item contains the target time profile
`Real.exp (-(c0 * (t : ℝ)))`; it must therefore be generated from source
parameters rather than treated as a harmless bookkeeping premise.

## Import-graph audit

Before the bridge module introduced after `d8856a76`, no file whose basename
was outside the `BalabanCMP102*` family imported a `BalabanCMP102*` module.
The terminal theorem occurred only in its definition file and its audit file.
Consequently, the CMP102 producer lane compiled but did not feed the CMP116
consumer lane.

The first exact type bridge is now:

```lean
cmp102FineFieldEquivCMP116PhysicalGaugeField
```

in `BalabanCMP116CMP102PhysicalFieldBridge.lean`.  It identifies the plain
physical positive-bond field used by CMP116 with the `PiLp 2` realization
used by CMP102, proves coordinate equality, and proves both round trips.
This bridge discharges no analytic boundary by itself.

## `CMP116Eq226PhysicalContourTermSource` field audit

The source record is the first object that must be constructed physically.
Its current status against the CMP102 lane is:

| Record component | CMP102 producer status |
|---|---|
| `contour` | **missing**: no CMP102 definition produces the literal `CMP116Eq214PhysicalContourDensity` |
| `source` | physical Gamma/operator ingredients exist, but no equality installs them in the contour density |
| `domainMetric`, `domainSupport` | domain geometry exists on the CMP102 side; no typed equality to the contour index family |
| Cauchy-radius identities | generic CMP116 formulas exist; not instantiated by a CMP102 contour producer |
| positivity/smallness scalars | many scalar lemmas exist; no complete source record |
| `outer_bound` | no CMP102-to-contour theorem |
| `inner_bound` | no CMP102-to-contour theorem |
| `interaction_bound` | the literal domain FTC term is now `C²`, normalized, and radial; no equality with the contour interaction exponent |
| `source_bound` | operator/source bounds exist parametrically; no installed contour source |
| `domain_nonempty`, `domain_subset` | geometric ingredients exist; no source-record construction |
| `rooted_residual` | **missing source instance** |
| `volume_budget` | **missing source instance** |

Therefore:

```text
physical CMP116Eq226PhysicalContourTermSource constructed: 0
terminal boundary objects discharged from CMP102:          0 / 5
terminal theorem instantiated nontrivially:                 0
```

## Closed CMP102 result retained

The literal reconstructed fine-head-tail domain FTC contribution now has:

1. a source-derived second field derivative;
2. `ContDiff ℝ 2`;
3. value zero at the zero field;
4. Fréchet derivative zero at the zero field;
5. an exact radial identity

```text
F_Y(A) = (1 / 2) * inner A (Q_Y(A) A).
```

This is a valid producer-side theorem.  It is not yet the CMP116 residual
bound and must not be counted as a discharged terminal hypothesis.

## Next acceptance target

The next theorem must construct the **literal contour interaction
component**, not another abstract certificate.  It should prove an equality
between the field-dependent real exponent obtained from the CMP102
fine-head-tail contribution (transported through
`cmp102FineFieldEquivCMP116PhysicalGaugeField`) and the corresponding
`interactionExponent` field of a source-defined
`CMP116Eq214PhysicalContourDensity`.

Only after this equality exists should the radial bound be used to discharge
the `interaction_bound` field of a concrete
`CMP116Eq226PhysicalContourTermSource`.

No theorem is to be accepted if it takes that equality, `interaction_bound`,
the complete `TermSource`, `hraw`, or `hprofile` as a renamed premise.
