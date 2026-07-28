# G2 mid-order CWIN=3/2 cover `[193/4,69]`

**Registered:** 2026-07-22, before cover production  
**State:** `AMENDED BEFORE ACCEPTED RERUN; QUARANTINED UNTIL COMPLETE`

## Frozen partition

The interval is partitioned into the following exact rational units, with no
data-dependent boundaries:

```text
[193/4, 97/2], [97/2,195/4], ..., [273/4,275/4], [275/4,69]
```

Equivalently, the first endpoint is `193/4`, each interior step is `1/4`,
and the final endpoint is `69`; there are 83 units.  Every unit uses the
same evaluator contract:

```text
CWIN=3/2, beta order 20, t order 25, 180 Arb bits,
minimum t width 1/100000,
t domain [3/5, PI_UP-(3/2)/beta_hi].
```

The earlier width-`1/2` attempt failed before emitting a row and is recorded
in [`INCIDENT-G2-MID-COVER-WIDTH-HALF-20260722.md`](INCIDENT-G2-MID-COVER-WIDTH-HALF-20260722.md).

The interval `[765/16,193/4]` is handled by the separately manifested
mid-order unit.  This cover starts at its exact right seam and is intended to
join it without overlap or gap.

## Acceptance and quarantine

Each unit requires a production/replay pair, exact rational beta/t headers,
adjacent strict-negative `trow` rows, identical dependency hashes, byte
identity after normalization, and an independent validator pass.  A failed
or timed-out unit emits no admissible transcript and blocks the cover.

Even a complete green cover remains quarantined: sign rows establish the
pointwise Wronskian sign only after the finite-beta analytic relay is supplied.
They do not, by themselves, prove `(H_tail)` or promote G2/G6.
