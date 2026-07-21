# K4 t-box boundary failure: `[9/4,23/10]`

The fixed candidate configuration was run on
`delta=[1/25,81/2000]`, `t=[9/4,23/10]`, 9,216 cells, and 140 Arb bits.
Production and replay were generated from the same frozen driver. The
independent validator rejects the box because two literal weighted fractions
are non-subunit:

```text
MD2r_mirror = 1.83618128611367...
MD_mirror   = 1.19740549482380...
```

The transcript hash is
`214D1F68A63C99E781B332322EB091B6EF86AB6462BAEFAB31CCA79ACF725E18`.
This is a negative design result, not a theorem counterexample: the box is
not admitted to any K4 union, and no parameter was retuned after the failure.
The adjacent box `[23/10,12/5]` passes independently and is archived as a
candidate only.
