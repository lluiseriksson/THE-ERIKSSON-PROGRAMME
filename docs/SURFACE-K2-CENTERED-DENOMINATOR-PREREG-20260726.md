# K2 centered-denominator carrier — preregistration (2026-07-26)

This is a bounded conditioning probe for the exact R4 widening incident. It
does not promote K2, G2, G6, `(H_tail)`, or the manuscript.

Frozen configuration:

```text
birth index: 144
t-box: [72/25, 29/10]
delta box: [9/1000, 1/100]
center: 19/2000
half-width: 1/2000
spatial grid: 192 x 192
Arb precision: 140 bits
physical split: 1181/1000
```

The nominal moment carrier is expanded about the exact delta midpoint. The
outer-domain derivative bounds are added as symmetric coefficient radii. The
probe reports (i) the centered constant-term lower bound and (ii) a uniform
lower bound after charging all coefficient variation over the half-width.

Acceptance is diagnostic only: the reported uniform lower bound must be
strictly positive and the output must end in `CENTERED DENOMINATOR PASS`. A
failure is terminal for this carrier on the frozen cell. A pass is not a K2
certificate: the complete birth-and-t cover, the R3 residual inequality,
production/replay byte identity, and the registered role audit remain
mandatory.
