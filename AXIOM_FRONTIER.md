# AXIOM_FRONTIER.md — v0.9.17 (CLEAN P91 DENOMINATOR-CONTROL WINDOW)

## Status
TOPOLOGICAL SU FRONT CLOSED LOCALLY. THE THEOREM-SIDE P81 CORRIDOR IS ALREADY RIGID ENOUGH. THE LIVE FRONT REMAINS ANALYTIC + THEOREM-SIDE. THE P91 WEAK-COUPLING WINDOW IS PROVED IN MULTIPLICATIVE FORM, AND THIS STEP ADDS A CLEAN DENOMINATOR-CONTROL WINDOW SO THE `P91RecursionDataWindow` CONSUMER NO LONGER LEANS ON THE LEGACY `β < 2 / b₀` DENOMINATOR ROUTE.

## Public lane
- `BalabanRGUniformLSIFrontier` remains the preferred short public entrypoint for the Haar-LSI lane.
- `BalabanRGUniformLSIQuantitativeP81ThresholdOneNormalForm` remains the preferred threshold-one theorem-side normal form.
- `BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry` remains the preferred threshold-one theorem-side registry.
- `BalabanCouplingRecursionWindow.lean` remains the preferred analytic correction file for P91 Appendix A.2.
- `P91DenominatorControlWindow.lean` is now the preferred clean denominator-control bridge for the multiplicative weak-coupling window.
- `CauchyDecayFromAFWindow.lean` remains the preferred first reroute consumer of that multiplicative weak-coupling window.
- `P91BetaDivergenceWindow.lean` remains the preferred second reroute consumer of that multiplicative weak-coupling window.
- `P91BetaDriftClosedWindow.lean` remains the preferred third reroute consumer of that multiplicative weak-coupling window.
- `P91RecursionDataWindow.lean` remains the preferred core interface reroute consumer and now uses the clean denominator-control window directly.

## Remaining live mathematical obstruction
The theorem-side P81 target and the actual package-level uniform-LSI content still have to be discharged internally.

## Soundness note
This remains an honest reduction. No unconditional Haar-LSI theorem is claimed without the actual theorem-side P81 proof and without the actual package-level closure. This step removes one more indirect dependency on the legacy denominator route but does not claim the theorem-side gap solved.
