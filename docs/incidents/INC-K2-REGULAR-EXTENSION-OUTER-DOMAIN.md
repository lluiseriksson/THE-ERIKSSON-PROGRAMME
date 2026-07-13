# INC-K2-REGULAR-EXTENSION-OUTER-DOMAIN

**Opened:** 2026-07-13  
**State:** `QUARANTINED`; repair in progress  
**Affected claims:** regular K2 promotions from `[0,1/1000]` to
`[0,1/250]` and `[0,1/200]`

## Finding

The sealed endpoint certificate was built for `delta_max=1/1000`.  Its outer
derivative helper fixes

```text
dmax = 0.001
```

inside `annulus_derivative_bounds`, and `moving_band_value_coefficients()`
defaults to the same endpoint with the conservative scaled radius 31.  Those
constants are valid for the manifested `[0,1/1000]` run.

The later extension drivers enlarged only the nominal core lane to
`1/250` and `1/200`; they reused the endpoint outer helpers without enlarging
their domain.  At the new endpoints the physical transition band begins at
scaled radius `1/sqrt(delta)`, approximately `15.81` and `14.14`,
respectively.  The value charge beginning at radius 31 therefore does not
cover the full transition band, and the annulus derivatives were evaluated
only through `delta=0.001`.  No inequality in the transcripts repairs that
gap.

## Consequence

The interval calculations and their printed margins are reproducible, but
they certify an incomplete outer-domain accounting.  All six regular004 and
regular005 segment/validation manifests are quarantined.  They carry no G2
load.  The last current regular certificate is again the independently
manifested endpoint `[0,1/1000] x [0,pi]`.  The terminal positive stress
descendant is unaffected because it uses the fixed physical-square driver.

## Repair contract

1. Preserve every affected script and transcript byte-for-byte for audit.
2. Build a new outer helper whose annulus cap and moving-band lower radius are
   explicit functions of the claimed `delta_max`.
3. Require an executable domain assertion linking every extension driver to
   that parameter.
4. Recompute the adversarial box including the enlarged band charge before
   any exhaustive rerun.
5. Only a fresh production pair, manifests, and joint validator may restore
   an extension.

