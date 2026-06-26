# PO 03 — `proof.eq231.pointwise-p-residual-majorization`

**Blocker:** hpointwise/hgeometry

**Source keys:** cmp116.eq231.p-bond-sum, cmp116.eq231.p-family-carrier-source-target

**Lean payoff:** cmp116PStageSourceBound_of_eq231_pointwise, CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise

**v3 action:** After P dictionary, identify the pointwise residual factor exactly; do not infer it from entropy alone.

## Acceptance rule

A commit passes this card only if it removes or narrows this exact blocker, or records the exact missing source theorem with enough quantifiers and constants for the next agent to attack directly. New downstream wrappers without source-field removal fail this card.
