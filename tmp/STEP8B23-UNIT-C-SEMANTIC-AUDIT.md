# Step 8b.23 Unit C — static semantic audit

Status: **STATIC ONLY — NOT COMPILER-VERIFIED**.

Scope:

- `BalabanCMP99CenteredTorusSampleDictionary.draft.lean`
- `BalabanCMP99CenteredTorusPhysicalGreenSampleTransport.draft.lean`

## Gate C1 — sign-sensitive finite sample dictionary

**PASS (static).**

- `cmp99SourceFlatQprimeUnitTorusSample` is the positive torus sample
  `ell/N'`.
- `cmp99SourceFlatQprimeCenteredUnitCubeRepresentative` uses the negative
  centered alias `-a_ell/N'`. This minus sign is necessary because the
  centered alias represents `-ell mod N'`.
- `cmp89CenteredUnitCubeToTorus_centeredRepresentative_eq_sample` proves that
  this negative centered representative covers the positive torus sample;
  the quotient divisibility is constructed from the sealed signed-alias
  dictionary.
- `cmp89Eq248NegativeTwoPiTorusMomentum_centeredRepresentative` then maps the
  representative under `p(t) = -2*pi*t` to the literal positive centered
  physical coarse base momentum.
- `cmp89UnitAddTorus_mFourier_unitTorusSample_eq_flatCharacter` separately
  identifies Mathlib's positive torus monomial with the finite `ZMod`
  character. No Fourier-reflection hypothesis is used.

Thus the two independent sign gates—continuous momentum and finite
character—are both explicit.

## Gate C2 — both nonzero displayed domains are constructed

**PASS (static).**

For `ell != 0`, `cmp99MassZeroDisplayedGreenDomain_centered` constructs all
three factors needed to identify the displayed and stabilized Green at the
centered momentum: unit symbol, reduced denominator, and every fine-alias
symbol.

`cmp99MassZeroDisplayedGreenDomain_physical` constructs the same complete
domain at the literal uncentered physical momentum. It transports the full
denominator through the integer-period dictionary and then derives its unit
and reduced factors; neither factor is independently declared periodic.
The fine fibre is supplied by its literal physical nonvanishing producer.

## Gate C3 — transport occurs only through the displayed sum

**PASS (static).**

`cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_centered_eq_physical`
performs the safe sequence:

1. construct the centered displayed domain;
2. construct the physical displayed domain;
3. exit the stabilized quotient at the centered point;
4. transport the displayed Green through the derived integer-vector period;
5. re-enter the stabilized quotient at the physical point.

It does not assert that the stabilized quotient is globally periodic outside
its non-singular domain.

## Gate C4 — zero and nonzero fibres are not conflated

**PASS (static).**

`cmp89Eq248CenteredGreenTorus_unitSample_eq_physical` splits on `ell = 0`.
The zero fibre is discharged by equality of the two literal momentum
arguments and congruence of the total stabilized endpoint; no nonzero-domain
producer is invoked. Only the nonzero branch uses the displayed-domain
transport theorem.

## Delimitation

This unit closes a pointwise sample dictionary only. It does not prove a
Fourier series reconstruction, finite-grid aliasing sum, reflection law,
uniform Green bound `B0`, window-15 attainment, or a terminal field. The
specialization `K`, `N'`, `a`, and downstream scale dictionaries remain the
responsibility of later units.

## Static verdict

All four Unit-C gates pass statically. The design blocks the principal false
shortcut: declaring the stabilized rational expression periodic and applying
that declaration at a singular zero mode. Promotion remains blocked on Lean
elaboration and axiom audit in the sanctioned remote validation path.

