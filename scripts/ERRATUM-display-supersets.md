# Erratum: display supersets in arb transcripts (ruling, round 2026-07-10u)

## Scope

Applies to the quotient diagnostic lines in the PROVISIONAL harvest
transcript (`harvest_arb_PROVISIONAL_blob98eca69.txt`, script blob
`98eca694` @ commit `5592d05`):

    [point]     Wc/<D>^2 = [+/- 0.455]
    [stability] Wc/<D>^2 = [+/- 0.431]

## Mechanism (demonstrated by reproduction, protocol desk)

python-flint's `.str(n)` falls back to the symmetric form `[+/- R]`
whenever the midpoint is not significantly representable at n digits
relative to the radius. A STRICTLY NEGATIVE ball divided by a positive
ball can therefore PRINT as `[+/- 0.455]` while `r < 0` still returns
True. The printed form is a decimal SUPERSET of the ball, not the
ball. Crucially, the genuinely broken route (a reciprocal against a
wide denominator that loses the sign) prints THE SAME WAY - the ink
alone does not carry the sign.

This is the second specimen of the display-superset class (the first:
a correct [0,1] ball printing as `[+/- 1.01]`, documented in the ghost
#22 autopsy). Two bites = a class, not an instance.

## Ruling

1. The provisional verdicts STAND: `Wc < 0: True` was computed on the
   Wc ball directly (the load-bearing route, which is sound), never on
   the printed quotient.
2. These quotient lines receive this erratum, not retroactive
   correction; the transcript file is immutable evidence.
3. RULE (with the rank of a rule, to the acta): NO PRINTED BALL WITHOUT
   ITS BOOLEAN. Every diagnostic line in every future driver carries
   the enclosure AND the explicit comparison result next to it. The
   contract-v2 driver (sha256 `1d888e99...`) already prints full
   [lo, hi] enclosures with the verdict booleans adjacent.
