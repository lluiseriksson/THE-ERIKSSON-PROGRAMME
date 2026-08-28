# Step 8b.24: positive-radius Poincare reachability

Status: static design only.  No Lean/Lake command has been run and no
counter moves.

## Measured boundary

Every physical P0--P5 Green/covariance producer ultimately consumes

```text
cmp99SourcePoincareErrorCoeff d Lblock depth spacing epsilon < 1.
```

The current joint-smallness record does not contain or imply this statement.
The tree proves only the exact flat endpoint

```text
cmp99SourcePoincareErrorCoeff d Lblock depth spacing 0 = 0
```

by `cmp99SourcePoincareErrorCoeff_zero`.  Thus the premise is consistent, but
the existing producer covers only the exactly flat background.  Calling it an
already named joint window would hide a physical reachability obligation.

Static inspection of
`CMP116CenteredConditionedJointSmallnessRegime` also shows why the two
layers must remain distinct: that record contains norm/rate targets and a
CMP109 pivot record, but no top-level source `epsilon` parameter.  The nested
pivot record does carry `pivot.epsilon0`, so a physical assembler may not
silently choose it independently of the background radius used by Poincare.
The two pivot inequalities are monotone under decreasing nonnegative radius:
the source deviation is linear, and
`cmp109PhysicalPivotBackgroundBudget_eq_at_one_mul` exposes the pivot budget
as a nonnegative linear coefficient times `epsilon0`.  Therefore the common
choice

```text
epsilon = min poincareRadius pivot.epsilon0 / 2
```

simultaneously preserves the pivot regime and enters the Poincare interval.
The future physical assembler must still combine these scalar facts with
operators attaining the fourteen registered norm/rate targets.

## Minimal producer to add

For fixed finite `depth` and arbitrary `spacing`, prove continuity at the flat
radius of the literal generated coefficient:

```text
ContinuousAt
  (fun epsilon =>
    cmp99SourcePoincareErrorCoeff d Lblock depth spacing epsilon)
  0.
```

The proof is finite induction on `depth` and must use the literal recursive
definitions.  First record the stronger exact simplification that
`cmp99SourcePoincareEnergyCoeff` is independent of `epsilon`: the parameter is
only threaded into the recursive call and never occurs in a base or additive
term.  This removes it entirely from the analytic part of the proof.  The
only non-polynomial component left is
`cmp99SourceUbarNextFineRadius`; at zero both denominators in its rational
remainder are one, so its continuity is local and unconditional there.
The scaled-gradient step error is then continuous at zero, and the remaining
induction proves continuity of the error recurrence.

No `hspacing : 0 < spacing` premise belongs to this continuity/reachability
theorem.  Lean's division is total and the numerator vanishes at the flat
radius even when the fixed denominator is zero.  Positive spacing remains a
separate, genuinely consumed premise of the later physical Green producer;
adding it here would be dead weight.

Combine continuity with the already proved zero value to obtain an open
neighborhood on which the error coefficient is below one.  Intersect it with
the open neighborhood at zero for

```text
cmp99SourceUbarDeviationCoefficient d Lblock *
  cmp99SourceUbarRadiusGrowthFactor d Lblock ^ depth * epsilon <
    min (cmp99UbarNoWindingThreshold Nc) (1 / 4).
```

The right-hand side is strictly positive by
`cmp99UbarNoWindingThreshold_pos`.  Choosing half the minimum of the two ball
radii produces one **strictly positive** `epsilon` together with

```text
CMP99SourceUbarClosedBudget d Lblock Nc depth epsilon
```

and the terminal Poincare inequality.  The flat gauge configuration then
supplies a concrete background satisfying the fine-small condition at that
positive radius, so the result is not merely a scalar compatibility claim.

## Required public endpoints

The primary source-facing theorem should expose the whole admissible
interval:

```text
exists radius, 0 < radius /\
  forall epsilon, 0 <= epsilon -> epsilon < radius ->
    CMP99SourceUbarClosedBudget ... epsilon /\
    PoincareErrorCoeff ... epsilon < 1.
```

Its concrete nonvacuity corollary should then have the shape

```text
exists epsilon,
  0 < epsilon /\
  CMP99SourceUbarClosedBudget d Lblock Nc depth epsilon /\
  cmp99SourcePoincareErrorCoeff d Lblock depth spacing epsilon < 1 /\
  (forall e, norm (flatBackground e - 1) <= epsilon).
```

Exact Lean notation may differ, but none of the four conjuncts may be
dropped.  In particular:

1. `epsilon = 0` is not an accepted substitute;
2. the Poincare inequality is derived, not a field of the witness;
3. the closed `Ubar` budget and Poincare inequality use the **same** radius;
4. the background witness is literal, not an assumed inhabitant;
5. no family of prefix inequalities is accepted -- P1 derives them from the
   one terminal inequality by its monotonicity theorem;
6. this is a reachability theorem for a flowing physical quantity, not a
   sixteenth freely chosen field of the joint-window registry.

A second concrete endpoint must use the same positive `epsilon` for the
closed `Ubar` budget, Poincare absorption, CMP109 chart radius and CMP109
pivot contraction.  It is derived by restricting the existing pivot witness;
the caller supplies none of those four scalar conclusions.

## Scope

This producer removes the extra scalar premise from the eventual flat
nonvacuity endpoint and makes the P0--P5 chain genuinely reachable at a
positive radius.  It does not prove the operator estimates for a non-flat
background, attain window 15, move `20/41`, or construct `TermSource`.

## Source-regularity integration boundary

The positive interval does **not** by itself discharge the C6d coercivity
premise for an independently fixed `alpha1`.  The source-facing retained
background uses the literal radius

```text
cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1 = 2 * alpha1,
```

while Corollary 3.6 separately requires

```text
geometryFactor * Mlarge * alpha0 <= alpha1.
```

Therefore an assembler may consume the admissible interval only after it
constructs one `alpha1` satisfying both the source lower bound and

```text
2 * alpha1 < poincareRadius
alpha1 <= 1 / 2.
```

Choosing the least admissible value
`alpha1 = geometryFactor * Mlarge * alpha0` reduces that integration to the
visible source smallness condition

```text
geometryFactor * Mlarge * alpha0 < min (poincareRadius / 2) (1 / 2).
```

This condition controls the original flowing radius `alpha0`; it is not a
sixteenth free window and may not be replaced by a caller-supplied Poincare
conclusion.  The eventual physical assembler must construct `alpha1`, the
closed Ubar budget at `2 * alpha1`, and the Poincare inequality from the one
admissible interval.  Until that assembler exists, the current C6d
source-terminal coercivity theorem remains correct intermediate plumbing but
is not a fully reached physical endpoint.

## Scratch implementation status

`tmp/PoincarePositiveRadiusReachability.lean` now contains eight proposed
declarations implementing the route above, with an eight-line sibling axiom
audit in `tmp/PoincarePositiveRadiusReachabilityAudit.lean`.  The exact text
guard reports

```text
LEAN_OVERLAY_TEXT_OK files=2
POINCARE_POSITIVE_RADIUS_STATIC source_decls=8 audit_prints=8
```

Source SHA-256:
`5E89500F4A786432F23F10D68540933AD5805CB7ACFD80A558289E18BB18058D`.
Audit SHA-256:
`91AED2683FD8A9316094684016560D8D084828B95AEB72618144E96985FAAC29`.
These are static scratch hashes, not compiler evidence.

The deterministic read-only promotion preview additionally reports

```text
POINCARE_PROMOTION_PREVIEW_OK files=2 declarations=8 audits=8
promoted_content_manifest_sha256=
  43235D28E56164C195A1F3F9847BE3AC5F59B32EDAC3B157B9695AD943B7AC77
```

The original preview accidentally retained the scratch status comment before
the imports, which would violate Lean's import-order rule.  That preview is
superseded.  The corrected promoted source and audit hashes are respectively
`CD829E4B733557B1A4C9B17DE4E239B0E78E8FB85C11D2E7780ED1E47F6DD60C`
and
`C10DC5576D135F534964BAECF41371B97A63A5B1DB9CAAD6FD3116265ED17FB6`.
Both put the module docstring after the imports and pass the overlay text gate.
The preview script SHA-256 is
`B4F3600B20F64DB3A973985B52DE0B0EB14D7320551939385E1F3D73D1243914`.
The target pair is present in the tree as PRE-VALIDATION source; no `.olean`
or compiler/oracle verdict exists yet.
