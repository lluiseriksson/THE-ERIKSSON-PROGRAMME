# PO 12 — `proof.final-frontier.pipeline`

**Blocker:** pipeline still waits on Eq. (2.29) and activity inputs

**Source keys:** crosswalk.final-frontier-pipeline, cmp116.lemma3.final-2.38, cmp116.effective-action.2.39-2.41

**Lean payoff:** CMP116RawSourceM3Frontier, BalabanCMP116SourceTheorem

**v3 action:** No final pipeline commits until an upstream source hypothesis is actually removed.

## Acceptance rule

A commit passes this card only if it removes or narrows this exact blocker, or records the exact missing source theorem with enough quantifiers and constants for the next agent to attack directly. New downstream wrappers without source-field removal fail this card.
