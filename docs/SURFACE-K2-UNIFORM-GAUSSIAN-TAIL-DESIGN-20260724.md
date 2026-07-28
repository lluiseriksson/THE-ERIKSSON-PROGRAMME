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
`99A8BEDE85399AF522838EE69EF8D98060243380B50376860281E3D985E8E0CF`.

## Observed bounds

For `[2.90,2.91]`, the largest displayed charge is
`2.12674706260520575e-25` (the `kf`, order-3 lane); for `[3.13,3.14]`,
the largest is `6.72860909012295055e-23` (the `hdf`, order-4 lane).  A
single deliberately coarse box `[0.10,3.14]` also runs, with largest charge
`8.44495729976172562e-21`; it is useful as a scale check, not as the required
fine cover.
The JSON hashes are, respectively,

* `DA7BC7A6F92F49EB84D2016A81AFEAA80F965DB402D70EC19EC999FDBF7C0D86`,
* `3AF0031E589ECB4D139AE263CA9AD81EADA1D8370E79873C8E4BD217592D01F3`,
* global-box JSON: `193971686820B20A047376936E6E134E8F5D153ACC04360DC9A34F69E7B228AC`.

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
