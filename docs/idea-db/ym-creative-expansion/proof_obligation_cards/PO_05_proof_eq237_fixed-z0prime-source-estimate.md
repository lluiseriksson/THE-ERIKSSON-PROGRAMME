# PO 05 — `proof.eq237.fixed-z0prime-source-estimate`

**Blocker:** fixed-Z0prime premise and final summation

**Source keys:** cmp116.eq237.post-p-resummation, cmp116.constants.c3-alpha5, crosswalk.eq237.combined-postp-route

**Lean payoff:** cmp116PostPResidualSourceBound_of_eq237, CMP116Eq237MajorizationBoundary

**v3 action:** Keep fixed estimate and final summation coupled; avoid splitting unless source has split.

## Acceptance rule

A commit passes this card only if it removes or narrows this exact blocker, or records the exact missing source theorem with enough quantifiers and constants for the next agent to attack directly. New downstream wrappers without source-field removal fail this card.
