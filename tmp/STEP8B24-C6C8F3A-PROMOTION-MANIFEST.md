# C6c.8f3a local Ubar-deviation bound promotion manifest

Status: **PRE-VALIDATION scratch only**.  No `.olean`, focal build or axiom
oracle exists for either module.

## Intended tracked paths

1. `YangMills/RG/BalabanCMP99SourceUbarLocalDeviationBound.lean`
2. `YangMills/RG/BalabanCMP99SourceUbarLocalDeviationBoundAudit.lean`

## Endpoint

The literal source estimate

```text
norm UbarDeviationLogArg <= cmp99SourceUbarFineDeviationRadius
```

is rederived from smallness on the exact one-bond f2b carrier, not on every
fine edge of the torus.  The proof reads the straight coarse base path and the
three source contours only.  Reversed oriented edges are discharged from the
positive physical coordinate by `norm_sun_inv_sub_one_le`.

This is the first analytic input of the localized scale constructor.  It does
not yet build the selected/identity next background or the recursive localized
tower.

## Audit queue

Three readouts, exactly those in the companion audit file.  Expected allowed
axiom set is the standard project subset; no claim is made before sanctioned
elaboration and oracle output.
