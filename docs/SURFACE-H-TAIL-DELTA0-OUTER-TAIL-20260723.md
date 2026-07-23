# δ=0 outer derivative tail: independent replay

**Status:** `CERTIFIED LOCAL INPUT`; no promotion of K2, K4, `S1'''/S2'''`,
`(H_tail)`, G2, or G6.

The authoritative script `scripts/surface_remainder_delta0_derivative_tail.py`
was replayed with the repository Arb runtime at precision 180.  Script
SHA-256:

```text
63A147FF86D9AE08E596F38629F0E490211A0BA5AC64CCD95823907EAB43258B
```

The analytic Gaussian outer-tail bounds (the square complement beyond radius
32, with the moving-band charge included separately) were finite:

| carrier | order-5 outer coefficient | moving-band δ⁵ coefficient |
|---|---:|---:|
| `kd` | `8.3847939e-15` | `1.1116487e-9` |
| `kf` | `1.4216231e-8` | `1.6613041e-3` |
| `hdd` | `2.6433132e-11` | `3.2901646e-6` |
| `hdf` | `4.4351194e-5` | `4.8659490` |

The run ended with `DELTA0 OUTER NORMALIZED DERIVATIVE TAILS BOUNDED`.
These are absolute analytic bounds for the endpoint outer region only.  They
do not provide the missing joint carrier inequality, the positive-δ union,
the Cauchy supremum for `(H_tail)`, or the sign-to-relay implication.  The
final-seal gate must therefore remain unchanged.
