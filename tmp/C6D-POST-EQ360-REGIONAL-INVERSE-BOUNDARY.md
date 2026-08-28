# C6d post-Eq360 boundary: regional precision to canonical Green

Status: static design plus PRE-VALIDATION scratch only.  No Lean/Lake or
axiom-oracle verdict is claimed here.  This boundary moves neither `20/41`
nor window 15 and constructs no `TermSource`.

## Measured carrier mismatch

The source-facing Eq. (3.35)/(3.60) precision is an endomorphism of

```text
ActiveGaugeZeroCochain Omega (SUNLieCoord Nc).
```

The reusable `cmp99RegionalDirichletGreen` and both Eq. (3.42) certificate
types instead start from an endomorphism of the full ambient zero-cochain
carrier and then apply `cmp99RegionalDirichletPrecision Omega`.

The existing CMP96 Green on
`cmp96SourceSeparatedRegionalCell P L K Q depth cell` cannot close this
boundary.  The selected Eq. (3.35) region is arbitrary source data constrained
by the printed source-region dictionary; it is not definitionally that
separated cell, and restriction of an inverse on a larger Dirichlet region is
not the inverse on a smaller one.

There is also one exact scale specialization before the certificate types
match.  The current C6d wrapper is intentionally generic in the regularity
ratio `L`, retained-tower ratio `M`, and residual side `N'`.  The separated
source consumer must instantiate

```text
M  = L
N' = cmp99RegionalLatticeSize L (2 * (K * Q)) depth,
```

so that its fine side `L * N'` is transported to

```text
cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)
```

by the already sealed theorem
`cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier`.  This cast is a
named source specialization, not definitional reduction and not a new free
equality.  The generic C6d theorem remains useful algebra, but it cannot feed
the source-localized Eq. (3.42) certificate until this specialization is
written.

## Accepted adapter

For literal restriction `R`, zero extension `E`, and the regional physical
precision `K`, use the canonical ambient completion

```text
K_ambient = E K R + (I - E R).
```

The exterior identity is not a physical claim.  It is a fixed technical
completion whose irrelevance must be proved before any source estimate uses
it.  The proof chain is finite:

1. `ER` and `I-ER` give an exact Pythagorean coordinate splitting;
2. coercivity of `K` with constant `c` yields coercivity of `K_ambient` with
   constant `min c 1`;
3. `R K_ambient E = K` exactly;
4. the regional Dirichlet Green generated from `K_ambient` equals
   `covarianceOfIsCoerciveCLM K` by inverse uniqueness.

The PRE-VALIDATION implementation and audit are:

```text
tmp/BalabanCMP99ActiveRegionCanonicalAmbientCompletion.draft.lean
tmp/BalabanCMP99ActiveRegionCanonicalAmbientCompletionAudit.draft.lean
```

Both lightweight text/import guards pass.  They remain scratch and may not be
cited until a compiler/audit gate passes and the exact files are promoted.

## Exact Eq. (3.42) target after completion

The two source certificate types were re-read field by field.  The endpoint
needed by the separated source route is literally

```text
CMP99Eq342SourceLocalizedGreenCertificate depth Omega
  (matrixSUNAdjointModel Nc) U spacing A c hc hAcoer B0 delta0
```

on the carrier

```text
cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q).
```

It contains four bounds on the **same**
`cmp99RegionalDirichletGreen Omega A hc hAcoer`, with owner maps fixed
definitionally to `cmp99Eq342SourceLocalizedActiveOwner` and
`cmp99Eq342SourceLocalizedBondOwner` and scale vector
`[B0 * ell^2, B0 * ell, B0 * ell, B0]`, where
`ell = L^(depth+1)`.  Thus the canonical completion must instantiate

```text
A       = cmp99ActiveRegionCanonicalAmbientCompletion Omega K1
c       = min c1 1
hc      = lt_min hc1 zero_lt_one
hAcoer  = isCoerciveCLM_cmp99ActiveRegionCanonicalAmbientCompletion ...
```

and the named inverse-uniqueness theorem then identifies the certificate's
Green with `covarianceOfIsCoerciveCLM K1 hc1 hK1coer`.

This identification closes only the operator/inverse dictionary.  It does
**not** transport the existing four CMP96 estimates: those theorems are fixed
to `cmp96SourceSeparatedRegionalCell` and
`cmp89SourceSeparatedAmbientPrefixPrecision`, whereas the C6d consumer uses
the selected source region and the interacting localized retained precision
`K1`.  Reusing their conclusions by reindexing, direct restriction, or a
caller-supplied Green equality is forbidden.  The four actions must be
re-instantiated on the covariance of this exact `K1`, after the physical
Eq. (3.60) factorization and resolvent have constructed it.

There is one further real/complex gate before this target is even well typed.
The C6d Eq. (3.60) wrapper currently constructs complex `baselinePrecision`
and `perturbedPrecision`, while the Eq. (3.42) certificate is real.  The
source-facing specialization must identify its baseline real slice with
`CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision`, and
derive the physical perturbation equality using
`cmp99Eq360_sourceGaugePrecision_eq_sub_perturbation`.  It may not accept a
real precision, its complexification, or their equality as caller data.

The scalar specialization here is not the bare cast `a_j : R -> C`.  The
analytic tower's `starred_realSlice` theorem lands on the explicitly
constructed source-weighted adjoint, while C6d.1 is presented with Lean's
counting-space Hilbert adjoint.  The sealed identity

```text
T.Qprime.adjoint =
  (spacing^4 / T.terminalSpacing^4) * T.weightedAdjoint
```

(`CMP99SourceWeightedRegionalTower.adjoint_eq_spacingRatio_smul_weightedAdjoint`)
therefore forces the analytic coefficient to be

```text
((a_j * spacing^4 / T.terminalSpacing^4 : R) : C)
```

when the real-slice target is the current counting-Hilbert C6d.1 precision.
The terminal-spacing formula must be derived from the internally generated
retained tower (ultimately `terminalSpacing = M^depth * spacing`), not supplied
as a scalar equality.  Omitting this factor would be the same normalization
class as the earlier double-`M^-4` defect: all operators would typecheck while
the physical coefficient changed silently.

That derivation is now pinned to an existing compiled source theorem rather
than a planned induction:

```text
CMP99SourceActiveRegionChain.weightedQprimeTower_terminalSpacing
```

and the PRE-VALIDATION dictionary

```text
tmp/BalabanCMP99SourceWeightedGaugePrecisionDictionary.draft.lean
```

exposes the resulting coefficient as

```text
a * spacing^d / ((M^depth * spacing)^d).
```

The next real-slice theorem must therefore have the following orientation:
the complex printed-star precision is evaluated at

```text
((a_j * spacing^4 / T.terminalSpacing^4 : R) : C),
```

and its value on a compact-real-slice field equals the canonical
complexification of the counting-Hilbert physical precision with coefficient
`a_j`.  The theorem must derive `T` from
`baselineRetainedTowerRealSliceAgreement`, rewrite its terminal member through
`canonicalTerminal_eq_generated`, and use the generated terminal-spacing
theorem above.  It may not accept `T.terminalSpacing = M^depth * spacing`, the
real-slice precision, or the final equality from the caller.

This also fixes the status of the C6d.1 phrase “printed `a_j`”.  Until the
weighted/counting dictionary above is installed in the real-slice wrapper,
the existing sealed module is a correct counting-Hilbert operator endpoint;
it must not by itself be cited as equality with the printed analytic starred
presentation.

## Baseline coercivity is generated, but the source coefficient is not free

A static re-read of the compiled Poincare tower and CMP99 pp. 394, 397 fixes
the next coercivity boundary.  For positive retained depth, the exact same
typed `regions`, physical background and generated terminal `Qprime` already
give

```text
(1 - B_j) ||phi||^2 <= A_j <phi, Delta_U phi> + CP^j ||Q'_j phi||^2.
```

Therefore the literal counting-Hilbert baseline precision is coercive with
the explicit floor

```text
(1 - B_j) * min (A_j)^(-1) (a_j * (CP^j)^(-1)),
```

using `isCoerciveCLM_of_twoWeightPoincare`.  No separate `hDelta`, regional
Green or coercivity witness is needed.  The PRE-VALIDATION scratch pair

```text
tmp/BalabanCMP99SourceActiveRegionTerminalCoercivity.draft.lean
tmp/BalabanCMP99SourceActiveRegionTerminalCoercivityAudit.draft.lean
```

records that positive-depth producer against already sealed generic
substrate only.  It has passed the lightweight overlay-text gate but has no
Lean or axiom-oracle verdict.  Depth zero is intentionally not smuggled into
the formula: `A_0 = 0`, while the stop-tower `Qprime` is the identity, so the
base case needs its own exact theorem.

This does not duplicate the already sealed
`BalabanCMP99SourceGeneratedPhysicalPrecision`.  That module proves
coercivity and constructs a Green operator for the canonical iterated-lift
region after normalizing the derivative coefficient to one.  C6d instead
selects an arbitrary typed source-region chain and must preserve the literal
Eq. (3.60) counting coefficient through the weighted/counting real-slice
dictionary.  The new scratch theorem is precisely that missing generality;
the existing canonical theorem remains the reference specialization and a
useful consistency check.

The scalar `a_j` in the Eq. (3.60) algebra is still not source closure.
CMP99 (3.24) fixes it recursively from `a_0 = a > 0`, and Theorem 3.1 then
specializes the physical Green statement to `a = 1`.  After the required
source specialization `M = L`, the Green consumer must therefore instantiate

```text
a_j = cmp99SourceMassParameter 1 L depth
```

and derive positivity from `cmp99SourceMassParameter_pos`; it may not expose
an arbitrary positive `a_j` as its final public input.  The current C6d
Eq. (3.60) wrapper remains valid algebra parametrized by a coefficient, but
the outer physical inversion wrapper must perform this source specialization.

The flow coefficient itself is not a remaining uniformity mystery.  The
already cold-sealed theorem
`cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter`, specialized to
`a = 1`, gives the depth-independent bound

```text
1 - L^(-2) <= cmp99SourceMassParameter 1 L depth,
```

and `cmp85Eq215SourceAveragingCoefficientFloor_pos` makes the left-hand side
strictly positive for `1 < L`.  Thus the averaging part of the baseline gap
does not collapse along the RG flow.  This does **not** by itself make the
full Poincare floor uniform: the generated `A_j`, `B_j`, and `CP^j` factors
remain visible and must be handled by the exact source estimates rather than
hidden inside the coefficient recurrence.

## What remains physical

This adapter does not manufacture any of the substantive source inputs.  A
source-facing consumer still has to:

1. construct the real physical Eq. (3.60) precision `K1` on `Omega`;
2. specialize its scale/carrier by the existing separated-carrier theorem;
3. derive coercivity of `K1` from the baseline gap and the attained relative
   perturbation budget;
4. construct its canonical regional covariance through the adapter above;
5. prove the four Eq. (3.42) actions on that same covariance;
6. establish one depth-uniform `B0, delta0` pair and then attain
   `norm R' < 1` by the direct Eq. (3.89) route.

No ambient precision, Green, inverse equality, `B0`, `delta0`, coercivity
constant or contraction may be accepted as a renamed free input.
