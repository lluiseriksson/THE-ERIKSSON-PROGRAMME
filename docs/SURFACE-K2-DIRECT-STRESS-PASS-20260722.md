# K2 direct joint-remainder stress pass — 2026-07-22

## Scope

This is a single-point design result for the repaired direct joint-remainder
judge, not a K2, S2''' or G2 certificate.  It is recorded because the same
stress point failed at a coarse spatial partition and passed after the
registered refinement ladder reached 65536 cells.

## Reproduction

```text
python scripts/surface_remainder_s2_direct_judge.py 20 65536 2.9
```

```text
script sha256 = b99267ae931e05c4d8d6e5535ebc5d62f85e863d367a8e66fd0f34b7d8b6b780
python = 3.12.6
python_flint = 0.9.0
arb_prec_bits = 100
effective_cells = 65536
```

The terminal enclosure reported

```text
theta3       = 2.8640686974502770101547029683 +/- 4.22e-29
residual_abs = 0.00501634292655138931397033910391 +/- 2.79e-33
budget       = 0.007160171743625692525386757421 +/- 4.00e-31
margin       = 0.002143828817074303211416418317 +/- 3.07e-31
DESIGN_POINT_PASS
```

At the same point and precision, the 4096-cell run had
`residual_abs = 0.0513094163307063...`, `budget = 0.00716017...`, and
margin `-0.04414924...`; this is an interval-dependency failure, not a
certified sign failure.  The refinement therefore removes a measured
enclosure obstruction, but it does not establish a uniform delta/t cover,
the completion and outer-tail budgets, a production/replay pair, or the
analytic relay from the scaled Wronskian to `(H_tail)`.

**Promotion status:** `CANDIDATE ONLY; G2 REMAINS OPEN`.

An exact replay with the same command, script hash, precision and cell count
returned the same decimal enclosures and margin.  This is a reproducibility
check for the point smoke, not the independent implementation and exhaustive
coverage required by the K2 production contract.
