# CMP116 interacting Wilson-Hessian campaign

## Objective

Construct, rather than assume, the interacting Hessian and the random-walk
remainders needed for the CMP116 estimate (2.16).  This campaign is independent
of the frozen `hRpoly` reduction release.

The objects must remain separate:

1. the literal second variation `D² S_Wilson(Ubar)`;
2. the gauge-fixed precision `Delta_k`;
3. the derived remainders `R1`, `R2`, and `R3`.

No remainder is to be introduced together with the estimate it is meant to
satisfy.

## Primary-source conventions

- Bałaban CMP99, pp. 390--392, equations (3.1)--(3.12): the perturbation is on
  the left, `U = exp(i eta A) Ubar`; the quadratic Taylor coefficient carries
  the factor `1/2`, and the plaquette action uses `1 - Re tr U(p)`.
- CMP99, pp. 393--395, equations (3.17)--(3.27): gauge fixing and block
  constraints are added after the Wilson Hessian to form the gauge-fixed
  operator.  The flat operator is not the definition at a small nontrivial
  background.
- CMP99, p. 407, equations (3.82)--(3.86): the perturbation convention is
  `Delta(U' U) = Delta(U) - V(A)`, hence the inverse expansion uses powers of
  `V(A) G(U)` with the displayed positive series convention.
- Bałaban CMP116, pp. 15--17, equations (2.14)--(2.26): the replacement point is
  `sigma = 0`, `U = Ubar`, `J = 0`, not `U = 1`.  The estimate (2.16) is the
  target for `R1`, `R2`, and `R3`, not their definition.
- CMP102 supplies the restricted variational interpretation.  CMP96 is an
  abelian gauge-fixing substrate.  Dimock's random-walk papers are scalar
  analogies and do not prove the Yang--Mills Hessian estimate.

## Checkpoints

- **WIL-H1:** literal two-parameter group-valued variation and mixed Wilson
  derivative.
- **WIL-H2:** support locality, symmetry, and gauge covariance.
- **WIL-H3:** exact recovery of the flat gauge-fixed operator.
- **WIL-H4:** uniform small-background perturbation.
- **WIL-RW1:** base resolvent and convergent random-walk expansion.
- **WIL-RW2:** construction of `R1`, `R2`, and `R3`.
- **WIL-RW3:** the full CMP116 (2.16) estimate.
- **WIL-BRIDGE:** discharge `hdom` and return to `hraw -> hRpoly -> KP`.

## Current checkpoint

`BalabanCMP116WilsonHessianLiteral.lean` closes the structural part of WIL-H1
and the first locality part of WIL-H2:

- one independent group value per positive physical bond;
- reversed edges reconstructed by inversion;
- the left variation `increment * Ubar`;
- exact passage through the background at `(0,0)`;
- literal iterated mixed derivatives of plaquette terms and of the full action;
- zero mixed plaquette contribution when either parameter is absent on the
  plaquette support.

`BalabanCMP116WilsonHessianUnitaryChart.lean` then supplies an axiom-free
concrete exponential chart in the ambient unitary group:

- the physical `SU(N)` background is embedded without changing edge matrices;
- every increment is the matrix exponential of a genuine traceless
  skew-Hermitian direction;
- skew-adjointness and unitarity of the exponential are proved in Mathlib;
- the chart passes exactly through the physical background at `(0,0)`;
- the resulting mixed Wilson derivative is a literal scalar derivative, not a
  supplied Hessian matrix.

Both modules are deliberately independent of the experimental `LieSUN` path.
Strengthening the increment codomain from `U(N)` to `SU(N)` still requires an
axiom-free determinant--exponential identity.  This does not alter the
underlying matrix curve or Wilson trace being differentiated.

`BalabanCMP116WilsonHessianDifferential.lean` closes the differential part of
WIL-H1 and WIL-H2:

- an ambient real matrix chart extends the same physical unitary curve;
- the complete finite Wilson action is proved analytic in that chart;
- its Fréchet Hessian is bilinear and symmetric;
- the ambient and unitary charts agree on every oriented edge, every
  plaquette holonomy, and the complete scalar action;
- the previous literal nested derivative is proved exactly equal to the
  physical restriction of the symmetric Fréchet Hessian;
- bilinearity and symmetry therefore hold for the literal mixed variation,
  not merely for a parallel auxiliary object.

`BalabanCMP116WilsonHessianFlatDictionary.lean` begins WIL-H3 without assuming
the answer:

- the orthonormal `SUNLieCoord` one-cochain is transported to the concrete
  `su(N)` exponential directions;
- positive and negative oriented edge tangents are fixed with the exact flat
  signs;
- the four-edge matrix curl is proved equal to the inverse-coordinate image of
  the repository's `covariantD1CLM` at the trivial background;
- its trace inner product is exactly the coordinate inner product of the two
  `D1` curls, both plaquettewise and after summation over all plaquettes.

`BalabanCMP116WilsonHessianExpDerivative.lean` closes the local
noncommutative calculus input needed by WIL-H3:

- the diagonal second derivative of the Banach-algebra exponential at zero is
  extracted from Mathlib's power series and proved equal to `X * X`;
- symmetry and polarization give the exact formula
  `D² exp(0)[X,Y] = (1/2) • (X * Y + Y * X)`;
- no commutativity assumption is introduced for the matrix algebra.

`BalabanCMP116WilsonHessianFlatPlaquette.lean` closes that local WIL-H3
calculation:

- it differentiates the ordered product of four noncommuting exponentials;
- cyclicity of trace pairs the reverse ordered cross terms;
- the diagonal formula is polarized using the symmetric literal plaquette
  Hessian;
- the terminal endpoint proves that the mixed flat plaquette Hessian is
  exactly
  `matrixTraceInner (flatPlaquetteSuMatrixCurl A p)
    (flatPlaquetteSuMatrixCurl B p)`.

`BalabanCMP116WilsonHessianFlatGlobal.lean` then closes the global Wilson part:

- the finite plaquette sum is commuted with both Fréchet derivatives;
- the local mixed Hessian formula is summed;
- the global curl dictionary is consumed;
- the terminal physical theorem identifies the literal flat Wilson Hessian
  exactly with `inner ℝ (D1 A) (D1 B)`.

`BalabanCMP116WilsonHessianFlatPrecision.lean` closes WIL-H3:

- the gauge-fixing mass is identified bilinearly with
  `inner ℝ (div A) (div B)`;
- Wilson plus gauge fixing is identified with the flat Hodge operator
  `D1†D1 + div†div`;
- the block-constraint form `a inner ℝ (Q A) (Q B)` is added separately;
- the terminal theorem identifies the resulting literal bilinear form with
  `gaugeFixedBasePrecisionCLM flatGaugeHodgeK0CLM Q a`.

Thus the flat CMP116 precision used downstream is now connected end to end to
the literal Wilson action at the trivial background.  The representation uses
`matrixSUNAdjointModel`; no arbitrary adjoint model is silently substituted
for the matrix Wilson Hessian.

`RealBilinearRiesz.lean` and
`BalabanCMP116WilsonHessianOperator.lean` strengthen this closure from
bilinear forms to canonical continuous operators:

- a bounded real bilinear form is converted to the sesquilinear interface of
  Mathlib's basis-free Riesz theorem without introducing coordinates;
- the literal physical Wilson Hessian is represented by the unique continuous
  operator `physicalWilsonHessianCLM`;
- at the trivial background this operator is exactly `D1†D1`;
- after adding gauge fixing it is exactly `flatGaugeHodgeK0CLM`;
- after adding the block constraint, the full operator family is literally
  the downstream `gaugeFixedBasePrecisionCLM`.

Thus WIL-H3 now holds as an operator identity.  No inference from equality of
quadratic forms alone is used.

`BalabanCMP116WilsonHessianLocality.lean` begins WIL-H4 at a nontrivial
background:

- the physical support of a plaquette is identified with its four explicit
  bond slots;
- the local unitary mixed variation is identified with the local ambient
  Fréchet Hessian;
- if either cochain direction vanishes on those four bonds, the local
  plaquette Hessian is zero;
- hence, for every physical background `U`, single-bond Hessian matrix
  elements vanish exactly when `physicalBondDist > 2`.

The Wilson Hessian therefore has a background-independent exact finite range
before any small-field or random-walk estimate is invoked.

`BalabanCMP116WilsonHessianOperatorLocality.lean` transfers this vanishing
through the canonical Riesz representation.  Its terminal theorem is the
downstream operator statement

`PhysicalCovarianceFiniteRange (physicalWilsonHessianCLM U)
  physicalBondDist 2`

for every physical background `U`.  Thus the interacting literal operator,
not only its matrix elements viewed externally, now satisfies the exact
finite-range interface consumed by the Combes--Thomas layer.

## Current non-claims

This checkpoint does not prove:

- packaging the concrete unitary exponential path as a path in `SU(N)`;
- the small-background estimate;
- a random-walk expansion;
- CMP116 (2.16), (2.26), `hraw`, or `hRpoly`.
