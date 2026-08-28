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

`tmp/PoincarePositiveRadiusReachability.lean` now contains seven proposed
declarations implementing the route above, with a seven-line sibling axiom
audit in `tmp/PoincarePositiveRadiusReachabilityAudit.lean`.  The exact text
guard reports

```text
LEAN_OVERLAY_TEXT_OK files=2
POINCARE_POSITIVE_RADIUS_STATIC source_decls=7 audit_prints=7
```

Source SHA-256:
`5659CCC5C4FEA43794AE57E399B195961A9662A47B1E5F032471E14B17BC9FAC`.
Audit SHA-256:
`2EB33641451CFF2F25D0685E9634FCA2DECED191BFF8D06B02AAEF34B3C961B7`.
These are static scratch hashes, not compiler evidence.

The deterministic read-only promotion preview additionally reports

```text
POINCARE_PROMOTION_PREVIEW_OK files=2 declarations=7 audits=7
promoted_content_manifest_sha256=
  C020325705C5AB758EF91FBFEA4E4F3573EBD94C1F9B57F1DBD27F5E8107D508
```

The original preview accidentally retained the scratch status comment before
the imports, which would violate Lean's import-order rule.  That preview is
superseded.  The corrected promoted source and audit hashes are respectively
`08FAB284B35B6175441A17FFA67F2F7F9FC29EC350CE8233357A998316CBFDA8`
and
`D570CC0A30ADCC0C9A828FC0503002C5F320633B202FD5F05DFFAB29F80EED7F`.
Both put the module docstring after the imports and pass the overlay text gate.
The preview script SHA-256 is
`12053074C788AD994288EFC7394AB7FECB485CB8BBEECCD8945EA7D7EC779EB6`.
No target file was written.
