# Preregistration: wider lambda cell for direct W-sign route

Register the next fixed cell before reading its result:

```text
beta   [13059/128,13060/128]
lambda [2,3]
modes 115; beta/lambda orders 50/50; Arb 500 bits
```

The unchanged mean-value driver must emit production and replay.  This is a
route-width diagnostic: a pass is candidate evidence only and a failure is
retained without changing the registered orders or cell boundaries.  No
G2/G6 promotion is authorized.
