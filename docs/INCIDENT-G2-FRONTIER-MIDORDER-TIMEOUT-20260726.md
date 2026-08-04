# Incident: frontier mid-order diagnostic timed out (2026-07-26)

The separately preregistered order-20/25 diagnostic on
`[1635/16,6541/64]` was run with Arb-180 and `MIN_DT=1/100000`.  It exceeded
the 420-second wall budget without emitting a terminal transcript.  The
zero-byte capture is retained as an execution record.  No sign rows or
manifest were admitted, and no G2, `(H_tail)`, K2, or G6 state changes follow.
