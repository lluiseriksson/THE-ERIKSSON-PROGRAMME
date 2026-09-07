# CMP116 equation (2.14): physical contour-density constructor audit

Date: 2026-07-30

Static scan at `d6cbf8763eb1`:

- `rg -l --glob '*.lean' 'CMP116Eq214PhysicalContourDensity' YangMills/RG`
  returns **96** files;
- no public declaration constructs the record from scratch without first
  receiving a record-valued carrier.

This reproduces the reported grep count while separating constructor
circularity from producer existence.

This audit distinguishes three different questions which a search for
`CMP116Eq214PhysicalContourDensity ... where` conflates:

1. whether a field has a literal physical producer;
2. whether the producer proves the required base-point law;
3. whether the final record can be constructed without first receiving an
   already inhabited record of the same type.

The first two questions are substantially closed for the complex Gaussian
sector.  The third is now closed by a non-circular assembly constructor,
while the final source-specific choice of its potential families remains a
separate composition step.

## Exact record surface

`CMP116Eq214PhysicalContourDensity` has fifteen data fields:

| field | current source-facing producer |
|---|---|
| `spectatorSupport` | geometric choice, preserved by installers |
| `fluctuationSupport` | geometric choice, preserved by installers |
| `deltaRadius` | Cauchy-radius choice, preserved by installers |
| `yRadius` | Cauchy-radius choice, preserved by installers |
| `referenceRoot` | `withSourcePi4RestrictedComplexGaussian` |
| `baseGamma` | `withSourcePi4RestrictedComplexGaussian` |
| `contourGamma` | `withSourcePi4RestrictedComplexGaussian` |
| `baseCovariance` | `withSourcePi4RestrictedComplexGaussian` |
| `contourCovariance` | `withSourcePi4RestrictedComplexGaussian` |
| `basePrecision` | `withSourcePi4RestrictedComplexGaussian` |
| `contourPrecision` | `withSourcePi4RestrictedComplexGaussian` |
| `determinantDensity` | `withSourcePi4RestrictedComplexGaussian`, using `cmp116Eq214LogDeterminantDensity` |
| `potential` | installer `withSourcePhysicalComplexTauPotential`; `cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily` supplies the literal CMP102 quadratic family, while the exact indexed total residual still needs the contour adapter |
| `bondField` | `withSourcePhysicalBondField` |
| `threshold` | `withSourcePhysicalBondField` |

It also has six law fields:

| law | current producer |
|---|---|
| `contourGamma_zero` | proved by `withSourcePi4RestrictedComplexGaussian` |
| `contourCovariance_zero` | proved by `withSourcePi4RestrictedComplexGaussian` |
| `contourPrecision_zero` | proved by `withSourcePi4RestrictedComplexGaussian` |
| `determinantDensity_zero` | proved by `withSourcePi4RestrictedComplexGaussian` |
| `determinantDensity_sq_mul_basePrecision_det` | proved by `withSourcePi4RestrictedComplexGaussian` from contour nonsingularity |
| `potential_zero` | proved by `withSourcePhysicalComplexTauPotential` |

The stronger declaration
`withSourcePi4RestrictedComplexGaussianOfPhysicalContour` constructs the
contour nonsingularity premise from the physical patched-walk estimate and
scalar Neumann bounds.  Thus the complex covariance, precision, Gamma and
determinant are not free contour inputs in that endpoint.

The full and restricted physical constructors entered history at
`4f8c27ea` and `0871bc00`, respectively.  Both commits are ancestors of the
tracked public PR branch; this is not uncommitted scratch infrastructure.

## What the grep count missed

The following declarations are complete record-valued installers even though
they are methods taking an existing `C`:

- `CMP116Eq214PhysicalContourDensity.withSourcePi4FullComplexGaussian`;
- `CMP116Eq214PhysicalContourDensity.withSourcePi4FullComplexGaussianOfPhysicalContour`;
- `CMP116Eq214PhysicalContourDensity.withSourcePi4RestrictedComplexGaussian`;
- `CMP116Eq214PhysicalContourDensity.withSourcePi4RestrictedComplexGaussianOfPhysicalContour`;
- `CMP116Eq214PhysicalContourDensity.withSourcePhysicalComplexTauPotential`;
- `CMP116Eq214PhysicalContourDensity.withSourcePhysicalBondField`.

Consequently the statement “the three complex fields have zero producers” is
false.  The accurate statement is:

> the literal producers exist, but every public installer starts from an
> already inhabited `CMP116Eq214PhysicalContourDensity`.

That circular assembly surface explains how ninety-six files can use the
record without there being a single non-circular source constructor.

## Remaining non-circular assembly frontier

A final source constructor must start only from:

- the two supports and the two Cauchy-radius families;
- the physical Gaussian inputs consumed by
  `withSourcePi4RestrictedComplexGaussianOfPhysicalContour`;
- the literal quadratic and residual domain functions consumed by
  `withSourcePhysicalComplexTauPotential`;
- the physical cutoff threshold consumed by
  `withSourcePhysicalBondField`.

It must then return the record directly and expose field-evaluation theorems
showing that no neutral seed field survives.

A neutral seed is source-faithful only as a private implementation detail of
such a direct constructor.  Publishing a neutral density as an independently
usable physical object would create a vacuity vector: zero Gamma and identity
covariance/precision satisfy the structural laws but are not the CMP116
contour.  The acceptance test is therefore not merely inhabitation.  It is a
terminal theorem bundle identifying all of

`referenceRoot`, `baseGamma`, `contourGamma`, `baseCovariance`,
`contourCovariance`, `basePrecision`, `contourPrecision`,
`determinantDensity`, `potential`, `bondField`, and `threshold`

with their literal source producers.

The older installer
`withCMP102FineHeadTailPotential` already installs the literal radial
quadratic family, but deliberately uses zero residual.  It therefore proves
that the quadratic half of the dictionary is source-specific; it does not
close the equation-(1.36) remainder.

The direct total residual has the correct codomain for the remaining
`remainder` slot:
`cmp102Eq80PhysicalIndexedCouplingScaledResidual ... i ... B : ℝ`.
The companion quadratic object is already total as well:
`cmp102Eq80CouplingScaledFixedHessian`; unlike the older radial-family
installer, it stores no contour regularity proof.  The focal theorem
`cmp102Eq80CouplingScaledPotential_eq_fixedHessian_add_totalResidual`
identifies these two total objects with the literal coupling-scaled potential
on every `C²`, source-normalized instance.  This removes the apparent need
for an `if`-defined extension outside the contour.  The theorem and its audit
compile with exactly the standard axiom set.

The remaining adapter is explicit:

1. set `nY` to `CMP102Eq80SourcePi4DomainCount anchor domains`;
2. send the restricted contour coordinate through
   `cmp116SourceRestrictedShiftedCoupling`;
3. send `i : Fin nY` to the canonical indexed localization domain;
4. project the physical field to that domain's bilateral bond support before
   evaluating the residual.

The projection-composition identity
`physicalBondProjection_indexedSourceDomain_centeredRegion` is the exact
dictionary needed because `cmp116SourcePhysicalComplexTauPotentialCoordinate`
first projects the Gaussian coordinate to the centered `Z0` region.

The indexed adapter now defines

- `cmp102Eq80PhysicalIndexedContourFixedHessian`;
- `cmp102Eq80PhysicalIndexedContourResidual`;
- `cmp102Eq80PhysicalIndexedContourResidual_centeredRegion`;
- `cmp116Eq142PhysicalPotentialTerm_indexedContour_eq_couplingScaled`.

The terminal equality reconstructs the literal coupling-scaled equation-(80)
domain potential from the fixed Hessian and total residual after the two
physical projections are composed.

## Constructor acceptance test

The public endpoint

`CMP116Eq214PhysicalContourDensity.ofSourcePi4RestrictedPhysicalContour`.

receives no pre-existing contour density.  Internally it composes, in this
order:

1. a private dependent record shell carrying only the two supports and two
   radius families;
2. `withSourcePhysicalComplexTauPotential`, which overwrites `potential`;
3. `withSourcePhysicalBondField`, which overwrites `bondField` and
   `threshold`;
4. `withSourcePi4RestrictedComplexGaussianOfPhysicalContour`, which
   overwrites `referenceRoot`, the six Gamma/covariance/precision fields and
   `determinantDensity`, while deriving all five complex-Gaussian laws from
   the physical contour estimates.

Thus none of the eleven non-geometric data fields survives from the shell.
The constructor, its audit, the indexed adapter and its audit were copied
byte-for-byte from their independently checked scratch versions into the
tracked tree and then built together in an exact clean replica:

- repository head: `d6cbf8763eb1774f96f4d01493c548d13acbc5da`;
- Lean toolchain: `leanprover/lean4:v4.29.0-rc6`;
- Mathlib: `07642720480157414db592fa85b626dafb71355b`;
- terminal line: `Build completed successfully (8864 jobs).`;
- all focal audit declarations depend exactly on
  `[propext, Classical.choice, Quot.sound]`.

The replica initially rejected a stale persistent Mathlib checkout.  The
accepted build used the exact manifest revisions.  The only transplanted
cache artifacts were ProofWidgets build products, and both their source and
destination checkouts were printed in the same run at the identical commit
`2e58165a9dcdca9837b666528f974299ee1a51cc`.

This establishes a first non-circular constructor as a compiled fact.

The source specialization
`ofSourcePi4RestrictedEq80PhysicalContour` now removes its last two free
potential families.  It fixes them to
`cmp102Eq80PhysicalIndexedContourFixedHessian` and
`cmp102Eq80PhysicalIndexedContourResidual`, uses every canonical domain index,
and fixes `Z0` to `cmp102Eq80SourcePi4CenteredRegion`.  Its direct elaboration
in the exact replica exits successfully.  Its tree audit remains part of the
pending checkpoint validation, so it is not yet counted as a published
constructor.

## Measured status

- Data fields with a literal physical producer or explicit geometric choice:
  **15/15**.
- Data fields whose producer exists but is not specialized in any source
  constructor: **0/15**.
- Law fields with a named proof producer: **6/6**.
- Non-circular assembly constructors from source inputs: **1**.
- Source-specialized non-circular equation-(80) constructors: **1 directly
  elaborated, pending tree audit and commit**.
- Complex Gaussian fields requiring new analytic definitions: **0/4**.
- Canonical source-domain enumeration and projection dictionary: **compiled**.
- The Lemma-1 contribution is now exposed as the single named
  `CMP116Lemma1Eq136ResidualCertificate`.  Its type deliberately starts after
  transport to the consumer's domain index and metric, so it does not conceal
  the still-open scale/domain reindexing dictionary.
- Remaining work: install the specialized density and that certificate into a
  first partial terminal source, then discharge the remaining terminal
  bounds.

This audit measures producer existence, not completion of `hRpoly`.
It does not close the Lemma-1 sector, the terminal scalar windows, or the
final `TermSource` constructor.
