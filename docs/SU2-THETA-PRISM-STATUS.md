# (9) Fabricante del prisma theta: delivery status

This is a manufacturer status record, not an external audit verdict.  The
artefact is limited to the abstract six-point theta gate and its auxiliary
lemmas on the fixed domain `0 < beta <= 1`.

## EXACTO

The following are theorem statements over concrete definitions and require no
task-specific loaded analytic input:

- the two-vertex half-cell has exactly three branches and cycle rank two;
  deleting branch `2` leaves two branches, cycle rank one, and no injection of
  three distinct theta legs;
- every pruning use exposes the local hypothesis that the selected
  incidence-one edge occurs in the weight and not in the observable;
- the concrete eight-variable SU(2) cell, point reflection, relative variables
  and holonomies are defined without `GaugeConfig` or `ReflectionSplitting`;
- `reflect` is involutive and
  `holonomy (reflect c) i = c.s^-1 * (holonomy c i)^-1 * c.s` pointwise;
- the fundamental character is the actual `2 x 2` matrix trace, is conjugation
  invariant, and the concrete witness is simultaneously conjugation invariant;
- `F(1,1)=3`, hence `F` is not zero; `I_2 != -I_2`, hence SU(2) is not a
  singleton; the normalized Haar measure has total mass one; and `beta=1`
  belongs to the exact domain;
- the general twice-spin triangle/parity rule gives multiplicity one for
  `(2,1,1)`, i.e. physical spins `(1,1/2,1/2)`, with a concrete one-element
  channel type;
- the singlet coefficient `1/2` is derived from inverse fundamental dimension,
  and the fundamental tensor multiplicities at orders one and two are computed;
- the central multipliers use the general dimension `twiceSpin+1`; from the
  independently derived witness norm and dimensions, the pairing factor is
  algebraically `1/16`;
- the fixed local inequality `beta^4/512` follows from the two coefficient
  remainder bounds.  It is not programme Gate 7.

## CERTIFICADO

The endpoint `manufactured_six_point_theta_gate` is a conditional certificate.
It consumes only the following named technical steps and derives every
headline through local artefact lemmas:

- `TraceRealityCertificate`: reality of the SU(2) fundamental trace;
- `CharacterBoundCertificate`: the pointwise trace bound;
- `HaarSchurSteps`: character integrability, zero first moment, translated
  coordinate identities, and the registered two-character Schur integral;
- `FubiniCoordinateSteps`: the three explicit product-Haar/Fubini exchange
  identities, including the relative coordinate `X=UV^-1`;
- `NormMomentSteps`: four concrete product-Haar Schur moments plus
  integrability; the witness expansion itself is proved locally;
- `CoefficientRemainderSteps`: nonnegative half-spin and spin-one series
  remainders on the fixed beta interval;
- `WeightMeasurabilityStep`: measurability against the supplied finite cell
  measure; the explicit bound `weight <= exp(3*|beta|)` is proved locally.

The independent exact-rational replay in
`scripts/certify_su2_theta_prism_rationals.py` reproduces cycle ranks `2/1`,
singlet coefficient `1/2`, witness norm `3/4`, pairing factor `1/16`, and gate
factor `1/512`.  Two executions were byte-identical.

## VERIFICADO

- Exact build target: `YangMills.SU2ThetaPrism.Endpoint`.
- Separate oracle target: `YangMills.SU2ThetaPrism.Oracle`.
- All 20 oracle headlines report only `[propext, Classical.choice, Quot.sound]`.
- Static contract validator rejects project axioms, `sorry`/`admit`/`sorryAx`,
  the forbidden continuous splitting import, alternate task numbering, and
  unresolved hypothesis-participation rows.
- The rational certificate output is 410 UTF-8 bytes with SHA-256
  `ad027cbe00176826c0a5657f2a1d674cb0711e548a57befcfc30d447ac65a723`,
  identical to the checked-in JSON certificate.

These are manufacturer verifications only.

## ABIERTO

The endpoint does not discharge the following bricks:

- trace reality and the sharp trace bound from first principles inside this
  lane;
- the concrete two-character Haar identity, translated-coordinate
  integrability, and the three Fubini/measure-preserving exchanges;
- the four Schur moments used by the norm computation;
- construction of the full spin-indexed irreducible character family and the
  analytic coefficient-series remainder bounds for the integral `alpha`;
- a canonical eight-variable normalized product-Haar measure on
  `CellConfiguration` (weight integrability is stated for an explicit supplied
  finite measure plus measurability step);
- any identification with a physical lattice cell, plaquette, or `GaugeConfig`;
- reflection positivity, OS positivity, continuous reflection splitting,
  programme Gate 7, a paper claim, or a terminal external audit verdict.

The resulting raw commit requires a new blind adversarial audit in another
session.
