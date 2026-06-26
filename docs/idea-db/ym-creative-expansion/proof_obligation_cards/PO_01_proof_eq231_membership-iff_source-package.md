# PO 01 — `proof.eq231.membership-iff.source-package`

**Blocker:** hPIndex plus hPcarrier/source identification

**Source keys:** cmp116.eq231.p-family-carrier-source-target, cmp109.bond-convention.positive-oriented, crosswalk.eq231.p-family-source-dictionary-route

**Lean payoff:** cmp116Eq231_balabanPFamily_sourcePIndexMemIff, cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff

**v3 action:** Do not add wrappers. Try to discharge exactly one source-package field or source-shape it with a smaller theorem.

## Acceptance rule

A commit passes this card only if it removes or narrows this exact blocker, or records the exact missing source theorem with enough quantifiers and constants for the next agent to attack directly. New downstream wrappers without source-field removal fail this card.
