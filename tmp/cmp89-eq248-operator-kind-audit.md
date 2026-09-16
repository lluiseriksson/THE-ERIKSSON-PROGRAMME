# CMP89 (2.42)/(2.48) operator-kind audit

Status: static primary-source finding; not yet a compiler seal.

Primary source: Balaban, *Regularity and Decay of Lattice Green's
Functions*, CMP 89 (1983), printed pp. 584--585.  Local primary PDF:
`tmp/cmp89-primary.pdf`, SHA-256 already catalogued as
`416E2B1F00B52E7235AB27D2BE066B50D42DDE33CF8596BAEAE0A6688B145143`.
The relevant visual renders are `tmp/cmp89-p-14.png` and
`tmp/cmp89-p-15.png`.

## Source distinction

1. Equation (2.42), printed p. 584, is the multiple-reflection
   representation of the regional propagator `G_j(□; x,x')` in terms of
   the full-lattice propagator `G_j(x,x')`.
2. Equation (2.44) defines `G_j` as the inverse of the full fine-lattice
   precision on an arbitrary fine source `f`.
3. Equation (2.46) is the Fourier solution for that arbitrary source.
4. Only afterwards the source says: "To calculate `G_j Q_j^*`, we take
   `f = Q_j^* g` in this formula, `g` is a function on the unit lattice".
5. Equation (2.47) is the corresponding alias-fibre solution for that
   restricted source.
6. Equation (2.48) is explicitly introduced as the formula for
   `(G_j Q_j^*)(x,y)`, with `x` on the fine lattice and `y` on the unit
   lattice.

Therefore (2.48) is not the fine-to-fine Green kernel required on the
right-hand side of (2.42).  Its two integer-coordinate arguments carry
different lattice conventions even though Lean can assign both the erased
type `Fin 4 -> Int`.

## Tree consequence

`cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen` implements the
source shape of (2.48).  The alias numerator and the already sealed
transpose-system solution agree with `G_j Q_j^*`.

The current name
`cmp89Eq248PhysicalFullLatticeGreen` and its use as the arbitrary
fine-to-fine `fullGreen` parameter of
`cmp89NeumannScalarReflectionOperator` are therefore not a source-faithful
dictionary.  In particular, the proposition
`CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRightInverse`
must not be treated as a reachable physical endpoint merely because it is a
well-typed conditional proposition.

The tree already contains the source-faithful endpoint convention in
`BalabanCMP99SourceFlatQprimeEndpointPhase`:
`cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y = M*y-x`.
The complete physical endpoint lane consumes its negative, `x-M*y`, in
`BalabanCMP99SourceFlatQprimeCompleteEndpointIntegrand` and identifies the
result explicitly as `G Qprime^*`.  Thus the repair is not speculative: the
correct fine-to-coarse dictionary and the corresponding generated operator
lane already exist, separately from the same-scale Neumann insertion.

## Required repair

- Preserve the existing (2.48) Fourier algebra as algebra for
  `G_j Q_j^*`; do not delete valid seals.
- Retract the name/role "full-lattice Green" wherever it claims (2.48)
  supplies the `G_j` kernel in (2.42).
- Give the fine and unit lattice arguments distinct named types (or an
  explicit typed dictionary), so the convention cannot erase again.
- For (2.42), construct the arbitrary-source full Green from the full
  solution (2.46), or prove the regional `G_j Q_j^*` estimate by composing
  the genuine (2.42) representation of `G_j` with `Q_j^*` on the source
  side.  Do not insert (2.48) directly as `G_j`.
- The generated physical particular-solution theorem that maps the literal
  full precision to the weighted-adjoint coarse mode is evidence for the
  `G_j Q_j^*` interpretation, not for a fine-to-fine inverse.

Counters remain `20/41`, `TermSource = 0`; no window is attained by this
finding.
