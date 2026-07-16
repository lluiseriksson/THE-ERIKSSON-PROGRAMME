# K2 delta-`1/80` split probes: negative and unresolved outcomes

**Date:** 2026-07-15  
**Scope:** three-witness design probe only; no production or theorem load.

The four pre-registered physical splits were tested at the three fixed
witnesses `(0,384)`, `(50,192)`, and `(157,384)`.

| split | outcome |
|---|---|
| `1181/1000` | all three witnesses resolved with strictly negative margins: `-33640.2619188618248743`, `-33695.0838539740038954`, and `-14173.1865349198708999` |
| `1183/1000` | all three witnesses unresolved: `ValueError: leading term in denominator is not nonzero` |
| `237/200` | all three witnesses unresolved with the same denominator representation failure |
| `1187/1000` | all three witnesses unresolved with the same denominator representation failure |

Thus no split supplies a positive certificate.  The negative split is a
mathematical rejection of that registered geometry; the other three are
representation failures, not sign evidence.  The exhaustive K2 positive-lane
union remains open, and these probes must not be cited as a theorem result.

As a diagnostic repair, splitting each outer derivative parameter box into two
delta subboxes removes the denominator representation failure for split
`1183/1000` at witness `(0,384)` and grid `192`.  The resulting outward
enclosure is finite but has margin about `-3.64e4`, so the repair confirms the
failure is representational without rescuing the registered budget.  This
two-slice smoke is not a production partition or a promotion of K2.

## Follow-up representation smoke

On 2026-07-16 the same split-`1183/1000`, witness-`0`, grid-`192` run was
repeated with four deterministic subdivisions of every outer delta box. The
leading denominator remained finite, but the terminal margin was
`-36389.5703 +/- 5.98e-5`, unchanged at printed precision from the two-slice
run. This confirms that the earlier `UNRESOLVED` was a representation issue,
not that the present enclosure is close to a positive K2 budget. The result
is diagnostic evidence only; no production cover or theorem load is created.
