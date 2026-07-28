# Background execution record: remaining `[31,74]` ladder

The preregistered width-`1/16` ladder has passed through index 27, ending at
`beta=131/4`.  The remaining fixed slice was initially attempted with the
exact same driver and contract:

```text
start_index=28, count=660, workers=4
```

The desktop sandbox terminates detached child processes when the tool call ends,
so that launch is not treated as evidence.  The ladder is being executed in
foreground slices: each worker performs production and an independent replay,
and every pair is validated and given an owning manifest before the G2 relay
audit is rerun.  Failures remain terminal incidents under the preregistration;
there is no adaptive rescue.

This background run is evidence collection only.  It cannot promote G2/G6 or
replace `(H_tail)` without the exhaustive-cover and logical-relay audits.
