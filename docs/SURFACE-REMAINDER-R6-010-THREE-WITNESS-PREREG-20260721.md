# R6 tenth-birth three-witness probe

**Registered:** 2026-07-21, before reading this probe's output

This isolated design probe tests the tenth regular birth
`delta in [9/1000,1/100]` under the registered R6 target

```text
|Y - T - r2*delta - r3*delta^2 - r4*delta^3 - r5*delta^4|
    <= 7600*delta^5.
```

The frozen geometry and witness set are imported byte-for-byte from
`surface_remainder_delta0_r4_extension_010_hybrid_contract.py`:
`(parent_000, grid=384)`, `(parent_050, grid=192)`, and
`(tail_156, grid=384)`.  The nominal seventh-order moment series is
assembled through the coefficient of `delta^5`; the fixed outer-domain
majorant is charged through the existing v7 wrapper, and the order-five
Bessel companion error is converted to the registered `delta^5` coefficient
budget by the exact maximum `delta=1/100`.

This is a **design probe only**.  A green result does not promote K2, G2, or
G6.  Promotion would require a fresh 158-unit production cover, an
independent byte-identical replay, an order-free union validator, and a new
manifest with all dependency hashes.  Any failure is retained as a negative
incident and does not alter gate state.
