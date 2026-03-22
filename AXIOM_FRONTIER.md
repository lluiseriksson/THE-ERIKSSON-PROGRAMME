# AXIOM_FRONTIER.md — v0.9.30 (THE CORRECTED P91 PUBLIC SHIM NOW USES A DIRECT MULTIPLICATIVE-WINDOW DRIFT/DIVERGENCE ROUTE)

## Status
TOPOLOGICAL SU FRONT CLOSED LOCALLY. THE P80/P81 CORRIDOR IS GREEN UNDER THE CURRENT ZERO-MAP SEMANTICS. THE LEGACY P91 ROUTE HAS ALREADY BEEN CERTIFIED TOO WEAK BY EXPLICIT COUNTEREXAMPLE. THIS STEP DOES NOT ADD A NEW HUB: IT ADDS A DIRECT MULTIPLICATIVE-WINDOW DRIFT FILE AND REWIRES THE CORRECTED PUBLIC SHIM TO USE IT.

## Public lane
- `P91CorrectedWindowPublicShim.lean` remains the preferred public theorem-side entrypoint for the corrected P91 lane.
- `P91UniformDriftWindowDirect.lean` is now the preferred direct multiplicative-window drift/divergence file.
- `BalabanCouplingRecursionWindow.lean` remains the preferred corrected asymptotic-freedom file.
- `P91DenominatorControlWindow.lean` remains the preferred corrected denominator-control file.
- `P91LegacyRouteCounterexample.lean` remains the preferred audit file for the rejected old route.

## Remaining live mathematical obstruction
The live obstruction is not to repair the legacy route as written.
It is:
- migrate any remaining theorem consumers off the old-route files,
- retire the remaining old-route `sorry` declarations once they are no longer load-bearing,
- and then replace the placeholder zero-map RG semantics by the explicit Balaban blocking map and rebuild the theorem-side corridor there.

## Soundness note
This remains an honest reduction. No unconditional final Bałaban theorem is claimed here. This step only makes the corrected public P91 surface less dependent on deprecated legacy drift files.
