# AXIOM_FRONTIER.md — v0.9.29 (PUBLIC P91 API NOW POINTS TO THE CORRECTED MULTIPLICATIVE-WINDOW LANE)

## Status
TOPOLOGICAL SU FRONT CLOSED LOCALLY. THE P80/P81 CORRIDOR IS GREEN UNDER THE CURRENT ZERO-MAP SEMANTICS. THE LEGACY P91 OLD ROUTE HAS ALREADY BEEN CERTIFIED TOO WEAK BY EXPLICIT COUNTEREXAMPLE. THIS STEP DOES NOT CREATE A NEW HUB: IT EXPORTS A SINGLE PUBLIC SHIM THAT POINTS THEOREM-SIDE CONSUMERS TO THE CORRECTED MULTIPLICATIVE-WINDOW P91 LANE.

## Public lane
- `P91CorrectedWindowPublicShim.lean` is now the preferred public theorem-side entrypoint for the corrected P91 lane.
- `BalabanCouplingRecursionWindow.lean` remains the preferred corrected asymptotic-freedom file.
- `P91DenominatorControlWindow.lean` remains the preferred corrected denominator bridge.
- `P91BetaDriftClosedWindow.lean` remains the preferred corrected drift/divergence bridge.
- `P91LegacyRouteCounterexample.lean` remains the preferred audit file for the old route.

## Remaining live mathematical obstruction
The live obstruction is not to prove the old P91 route as written.
It is:
- migrate remaining theorem consumers off the old-route files,
- retire the remaining legacy `sorry` declarations once they are no longer load-bearing,
- and, more fundamentally, replace the placeholder zero-map RG semantics by the explicit Balaban blocking map and rebuild the theorem-side corridor there.

## Soundness note
This remains an honest reduction. No unconditional Haar-LSI theorem is claimed here. No fake closure of the legacy P91 route is attempted. This step only makes the corrected multiplicative-window lane the explicit public entrypoint.
