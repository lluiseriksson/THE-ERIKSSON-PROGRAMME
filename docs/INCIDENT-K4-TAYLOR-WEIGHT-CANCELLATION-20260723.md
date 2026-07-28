# K4 Taylor-weight cancellation incident — 2026-07-23

The centred-delta design prototype used

```text
delta_final*(hi-lo) - (hi^2-lo^2)/2
```

for the integrated Taylor weight.  On narrow boxes, independent Arb
evaluation of the unfactored expression suffered cancellation.  The
isolated candidate helper
`scripts/surface_remainder_centered_delta_integrator_factored.py` now uses the
exact factored identity

```text
(hi-lo)*(delta_final-(hi+lo)/2),
```

which preserves the width under outward rounding.  The historical design
module and its manifests were deliberately left unchanged.  The regression
`tests/test_surface_remainder_centered_delta_integrator_design.py` checks a
box wholly below the endpoint.  It also records that a box centred on
`delta_final=1/15` has genuinely zero signed weight; such a box must be split
one-sided or charged with an absolute weight and cannot carry a certificate.

All K4 results produced before this correction are superseded design evidence
and carry no promotion load.
