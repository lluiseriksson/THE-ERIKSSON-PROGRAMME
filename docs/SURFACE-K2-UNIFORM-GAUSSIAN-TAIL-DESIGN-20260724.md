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
`A65CDF629FA632C8A3B99D3169FDB3D4FB1B7DD288E173DDBE3B4CF370427403`.

## Observed bounds

For `[2.90,2.91]`, the largest displayed charge is
`2.12674706157225666e-25` (the `kf`, order-3 lane); for `[3.13,3.14]`,
the largest is `6.72860908070667518e-23` (the `hdf`, order-4 lane).  A
single deliberately coarse box `[0.10,3.14]` also runs, with largest charge
`8.44495657658986312e-21`; it is useful as a scale check, not as the required
fine cover.
The JSON hashes are, respectively,

* `DCF9FF89EB38841673C1B3A1CC910D49D8B60685FFEBC6D2EC254B9224708C33`,
* `5C81035770A3A43B51996A834BDC97248AEF68A562D61678707A74E2467BD2FB`,
* global-box JSON: `56A9AE764DF82C62B308252BD3D0488819BA01377813CA4B89EEC98A85E74434`.

These magnitudes are compatible with a tail budget, but compatibility is not
a proof: the Taylor remainder, companion contribution, and the complete
ordered cover of the curved `(delta,t)` domain are still absent.

## Required subdivision

The global box now succeeds because the script constructs the monotone
`cos(t/4)` enclosure from endpoint evaluations and uses a polynomial
Lipschitz enclosure.  This does **not** remove the need for subdivision in the
terminal route: the resulting coefficient radii are much wider than local
boxes, and the joint `(delta,t)` contract still requires a born-ordered cover
and a separate Taylor/companion budget.  Any box whose denominator interval
crosses zero remains a hard failure.

## Status

`DESIGN_ONLY`.  No K2 promotion, no G2 promotion, and no manuscript edit.
