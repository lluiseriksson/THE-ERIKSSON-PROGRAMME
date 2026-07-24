# Incident — centred ratio-factorization design is too wide (2026-07-24)

The preregistered smoke in
`docs/SURFACE-K2-CENTERED-RATIO-DESIGN-20260724.md` was attempted with the
existing midpoint-plus-Hessian spatial rule.  The full grid-12/grid-24,
two-`t` run exceeded the 120-second operational ceiling before producing a
transcript.

Cheap falsification runs, with the same `delta=[0,1/80]` lane and 140-bit Arb,
gave:

| `t` | grid | `g(0)` bad components | nominal `B/delta` radius |
|---|---:|---:|---:|
| 2.90 | 4 | 0 | `5.45968372224e11` |
| 3.13 | 4 | 0 | `4.39981016576e11` |
| 2.90 | 8 | 0 | `1.81779338867e5` |

The exact zero-defect check therefore passes, but the spatial Hessian charge is
far too wide for a terminal margin.  This route is rejected as a K2 closure
architecture; no production/replay evidence or theorem promotion follows.
