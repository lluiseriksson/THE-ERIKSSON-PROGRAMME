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

## Current non-claims

This checkpoint does not prove:

- packaging the concrete unitary exponential path as a path in `SU(N)`;
- identification with `covariantD1CLM` or `Delta_flat`;
- the small-background estimate;
- a random-walk expansion;
- CMP116 (2.16), (2.26), `hraw`, or `hRpoly`.
