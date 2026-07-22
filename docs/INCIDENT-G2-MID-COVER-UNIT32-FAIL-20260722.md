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
