# K2 centered grid scan — refinement insufficient (2026-07-26)

The preregistered grid ladder on cell 144 was replayed byte-identically:

```text
production/replay SHA-256: 2AF88A480407DF5364010B5248C3C2FDDA28509DF8A81ED42A164D5CA3F1ED41
grid 192: Y=+/-9.02, raw margin=-9.25490211291410...
grid 384: Y=+/-4.71, raw margin=-4.95314012436367...
grid 768: Y=+/-2.81, raw margin=-3.05536242356695...
terminal line: CENTERED GRID SCAN COMPLETE; NO R3 PROMOTION
```

Refining the spatial grid improves conditioning monotonically but does not
approach the registered R3 budget on this cell. This rejects quadrature
refinement alone as a closure route; no K2/G2/G6/manuscript state changes.
