# Incident: low-z weighted smoke does not widen directly to a parameter box

Date: 2026-07-23
Status: candidate-only; no K4/S1'''/S2''' promotion

The successful point smoke was widened experimentally to

```text
delta in [0.0660, 0.0666666667]
t     in [2.899, 2.901]
```

with the same low-z dispatcher and 4096 adaptive cells per lane.  The
absolute partition totals became far too wide: for example
`nuD_main ≈ 2770.13` against budget `0.94119`, and
`MD2r_mirror ≈ 3834.45` against budget `12.577`.  The point smoke's strict
margin therefore does not extend to this two-parameter box by simply hulling
the parameters.

This is a measured enclosure-width failure, not a disproof of K4.  A global
route needs parameter jets, much finer coupled subdivision, or an analytic
regular-ball majorant; the single-point transcript remains quarantined.

Even a much narrower test, `delta∈[0.06665,0.0666666667]` and
`t∈[2.8999,2.9001]`, left `nuD_main≈29.8931` of absolute total at 16,384
spatial cells.  This confirms that simply hulling the delta argument inside
the existing second-derivative carrier is not a viable parameter-box proof;
the missing delta-jet/regular-ball treatment is substantive.
