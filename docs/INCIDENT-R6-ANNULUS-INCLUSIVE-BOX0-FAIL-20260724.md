# R6 annulus-inclusive box-0 failure (2026-07-24)

**Scope:** diagnostic only; no K2, (H_{\rm tail}), G2, or G6 promotion.

The existing R6 exact-outer production transcript reports 158 positive rows,
but its judge iterates only the six `CORE_BOXES`.  The registered tenth-birth
contract also requires the ten `ANNULUS_BOXES`; those are the domain split used
to charge the outer derivative bounds on the positive delta lane.

The separate wrapper
`scripts/probe_surface_remainder_r6_annulus_single.py` was run on born
`t`-box index 0, `[0,1/50]`, with the registered grid 384, 140-bit Arb
arithmetic.  It calls the annulus-inclusive `judge_t` from
`surface_remainder_delta0_r6_extension_010_cover.py` without changing its
target or constants.

```text
R6 ANNULUS-INCLUSIVE SINGLE-BOX PROBE 0 t 0 1/50 grid 384
RESULT radius 59/5
head 0.0732775021777342772111296654
Y5 19654.8271696074674679266536259
value 0.3475911759460323253265034726
margin_lower -12055.174760783413500326
R6 ANNULUS-INCLUSIVE SINGLE-BOX FAIL
```

Provenance: wrapper SHA-256
`770CB4DC98CD13643FB96ED91C094BF011F5E46B171B7F7F902F58DBAA6C4A78`,
source head `01db70633947838f23b3d00ea53f0c921deef886`.

This is a failure of the present annulus/outer majorant, not a disproof of the
Surface Theorem.  It shows that the prior 158-row R6 transcript is not a
global K2 certificate: it omits a required positive-lane contribution.  The
next admissible route must either preserve the cancellation in the annulus
charge or supply a new registered absolute tail bound; increasing the target
7600 is not permitted.
