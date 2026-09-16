# C6c.8f2f retained Qprime locality promotion manifest

Status: **PRE-VALIDATION scratch only**.  No `.olean`, focal build or axiom
oracle exists for either module.

## Intended tracked paths

1. `YangMills/RG/BalabanCMP99SourceRetainedQprimeLocality.lean`
2. `YangMills/RG/BalabanCMP99SourceRetainedQprimeLocalityAudit.lean`

## Endpoint

For two globally admissible fine backgrounds agreeing on the generated
`retainedFineReadBonds`, the literal source recursion constructs equal
retained `Qprime` maps.  The proof is an induction on
`CMP99SourceActiveRegionChain`:

1. f2d gives equality of the current transported average;
2. f2d+f2e give equality of the selected next-background bonds required by
   the tail; and
3. the induction hypothesis gives the tail `Qprime` equality, after which the
   two literal compositions agree.

No complete next-background equality, transport equality or `Qprime` equality
is an input.  This theorem still assumes each global extension is admissible;
constructing the localized deviation/Ubar scale that removes that premise from
the Corollary-3.6 consumer remains C6c.8f3.

## Audit queue

One source-facing readout.  Expected allowed axiom set is the standard project
subset; no claim is made before sanctioned elaboration and oracle output.
