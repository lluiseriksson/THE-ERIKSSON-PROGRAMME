# G2 scaled-bulk gap timeout: `[765/16,193/4]`

**Date:** 2026-07-22  
**Status:** `DESIGN_TIMEOUT`; no certificate emitted

## Frozen command

The existing high-order CWIN=`3/2` backend was invoked on the first
uncovered beta interval reported by the relay audit:

```text
python - <<'PY'
from fractions import Fraction
import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high as m
print(m.run('gap_probe_765_48', Fraction(765,16), Fraction(193,4)))
PY
```

The run used the driver's registered settings (180 Arb bits, beta order 30,
t order 37, minimum `dt=1/100000`, cached Bessel backend).  It was terminated
by the external 120-second execution ceiling before returning a terminal row,
margin, transcript, or replay.

## Interpretation

This is an operational falsification of the unmodified backend for this
interval, not a sign failure and not a theorem counterexample.  No partial
stdout is promoted to a row, and no manifest is created.  The finite-beta
relay remains incomplete; the G2 audit therefore remains
`RELAY_LEMMA_UNPROVED` and the final seal remains blocked.

## Required next step

A replacement evaluator must be preregistered (or the interval must be
split under an already registered rule) and independently replayed before any
row from this gap can enter the admissible union.  Increasing precision or
silently changing Taylor orders is not authorized by this incident.
