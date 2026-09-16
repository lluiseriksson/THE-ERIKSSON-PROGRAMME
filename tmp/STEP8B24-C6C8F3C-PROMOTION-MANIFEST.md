# C6c.8f3c localized weighted-tower promotion manifest

Status: **PRE-VALIDATION scratch only**.  No `.olean`, focal build or axiom
oracle exists for either module.

## Intended tracked paths

1. `YangMills/RG/BalabanCMP99SourceLocalizedWeightedQprimeTower.lean`
2. `YangMills/RG/BalabanCMP99SourceLocalizedWeightedQprimeTowerAudit.lean`

## Endpoint

`CMP99SourceActiveRegionChain.localizedWeightedQprimeTower` consumes
smallness only on `regions.retainedFineReadBonds`.  At every successor it:

1. extracts the Ubar pullback for the tail's selected coarse bonds;
2. constructs the f3b selected/identity next background;
3. derives its global next-scale radius internally;
4. restricts that certificate to the recursive tail carrier; and
5. prepends the literal physical transported average.

No global fine-smallness premise on the initial background and no arbitrary
next background occur.  The depth theorem confirms the recursion follows the
typed region chain exactly.

Remaining f3 work: prove agreement of this localized tower with the canonical
global source tower whenever a globally admissible extension is supplied, and
package the retained prefixes required downstream.

## Audit queue

Three readouts, exactly those in the companion audit file.  Expected allowed
axiom set is the standard project subset; no claim is made before sanctioned
elaboration and oracle output.
