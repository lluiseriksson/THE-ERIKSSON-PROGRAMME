# K4 exponential real-part modulus — preregistration

Date: 2026-07-25. This is a design-only go/no-go experiment for the
regular-ball route. It does not promote K4, `S1'''/S2'''`, G1, G2, or G6.

## Frozen inputs

The comparison uses the same stress parameters as the rejected crude-modulus
probe: `t=29/10`, `rho=7/100`, scaled radius `R=4`, `Phi=4*pi`, carrier
`nuD_main`, Cauchy radius `r=59/2000`, Arb precision 140, and degree cap
`N<=16`. Both main and mirror saddle amplitudes are checked.

## Required output

The new module must return an outward-rounded bound for the real part of the
complex exponent factor on the registered disk, together with the induced
finite modulus `M_realpart`. The driver must print the old crude modulus and
the new modulus on the same frozen parameters. It may not edit or reuse the
old falsifier as a dependency.

The acceptance judge is deliberately unchanged:

```text
min_N M_realpart*(N+1)*(N+2)*(r/rho)^(N-1)/(1-r/rho)
    < 0.5*(1-0.2758)
```

Any branch/sector ambiguity, non-finite enclosure, or failure of this strict
inequality is an incident and leaves the regular-ball route blocked. A pass
is only a design milestone: coefficient heads, moving `phi` tails, spatial
tails, two delta derivatives, overlap, and t-uniformity remain unproved.

## Provenance

Production and any replay must include hashes of this preregistration, the
new module, the new driver, and `surface_remainder_k4_complex_disk.py`.
