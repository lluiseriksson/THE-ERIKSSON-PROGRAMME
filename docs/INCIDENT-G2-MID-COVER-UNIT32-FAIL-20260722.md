# Incident: mid-order cover unit 32 reaches the minimum t width

**Date:** 2026-07-22

The fixed CWIN=`3/2`, beta-order-20, t-order-25, 180-bit contract was run on
unit 32, `[225/4,113/2]`, with the preregistered minimum `t` width
`1/100000`.  The recursive cover reached that floor near
`t=3.1113119102511955` and raised:

```text
RuntimeError: mid-order cover failure near t=3.1113119102511955
```

The driver emitted no terminal transcript, and no manifest was created.  The
failure is therefore not a sign row and carries no G2 or G6 load.  Units
0--31 remain valid quarantined evidence; unit 32 and later units are not
admissible until a repair is preregistered, independently rerun, and checked
for exact beta/t adjacency.  No mesh, Taylor order, or boundary was changed
after observing the failure.

An isolated probe with the same mesh, precision, and stopping rule but beta
Taylor order 22 passed unit 32 with 168 rows.  This was only a repair
candidate until fresh production/replay evidence was made.  The change was
preregistered in
`docs/SURFACE-G2-CWIN3P2-MID-COVER-ORDER22-REPAIR-PREREG-20260722.md`; it
is now archived as quarantined evidence in
`surface-scaled-bulk-cwin3p2-mid-cover-order22-repair-partial-20260722.json`.
It remains a sign-row candidate and does not promote G2, G6, or `H_tail`.
