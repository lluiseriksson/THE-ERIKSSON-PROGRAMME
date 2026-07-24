# K2 uniform Gaussian-tail design probe (2026-07-24)

## Scope

This record extends the midpoint-only Gaussian-complement probe to a finite
`c` interval.  It is a design brick only: it does **not** discharge K2, G2,
or any manuscript slot.

The script evaluates each rational coefficient of the explicitly derived
low-order moment polynomials on an outward Arb interval.  The Gaussian tail
and prefactor use the least `c` in the box.  A denominator crossing zero is a
hard failure, rather than a midpoint fallback.

## Reproduction

```text
PYTHONPATH=work/pydeps;scripts \
python scripts/probe_surface_remainder_closed_gaussian_tail_uniform.py \
  --t-lo 2.90 --t-hi 2.91 \
  --output scripts/surface_remainder_closed_gaussian_tail_uniform_290_291_20260724.json

python scripts/probe_surface_remainder_closed_gaussian_tail_uniform.py \
  --t-lo 3.13 --t-hi 3.14 \
  --output scripts/surface_remainder_closed_gaussian_tail_uniform_313_314_20260724.json
```

The implementation hash is
`65A0B4BA85DFFD71C16C616C23065DFEDD8E12B32BAF13184A9D2476AFC33B93`.

## Observed bounds

For `[2.90,2.91]`, the largest displayed charge is
`2.12728412536651012e-25` (the `kf`, order-1 lane); for `[3.13,3.14]`,
the largest is `6.72729564735796170e-23` (the `hdf`, order-4 lane).
The JSON hashes are, respectively,

* `43CAC522E843992EF19AA5DF6DBD4E509F136C552587504292C12D7877D26E9C`,
* `B8C07A3A79DC76BBF4CEBFBE2B1EC585D94A5C843C62EED50196FBBD3095D208`.

These magnitudes are compatible with a tail budget, but compatibility is not
a proof: the Taylor remainder, companion contribution, and the complete
ordered cover of the curved `(delta,t)` domain are still absent.

## Deliberate negative control

Running one box `[0.10,3.14]` without subdivision fails because interval
cosine encloses a denominator zero.  This is the intended behaviour and shows
that a global midpoint or unsplit trigonometric enclosure cannot be used as a
certificate.  The terminal route must supply born-ordered `t` boxes (or an
equivalent monotone enclosure) and record every failed box.

## Status

`DESIGN_ONLY`.  No K2 promotion, no G2 promotion, and no manuscript edit.
