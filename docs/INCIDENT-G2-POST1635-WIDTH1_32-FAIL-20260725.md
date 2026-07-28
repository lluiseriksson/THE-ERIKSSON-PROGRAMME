# Incident: post-1635/16 width-1/32 cell still loses sign

The preregistered beta cell `[1635/16,3271/32]` was run with the unchanged
seeded-grid contract: `CWIN=3/2`, beta order `30`, t order `37`, 180-bit Arb,
and seed step `1/64`.

After approximately eight minutes the driver aborted before emitting a
transcript:

```text
RuntimeError: bulk failure near t=3.123099211026197
```

The output file is empty and no manifest was created. The failure is at the
same narrow t obstruction as the width-`1/16` attempt, so beta-width reduction
alone is not an adequate repair. No further subdivision, order increase, or
precision change is authorized by this diagnostic; a new analytic enclosure
would require a fresh preregistration.

