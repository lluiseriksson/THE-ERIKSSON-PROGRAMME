# PO 11 — `proof.source-status-promotion.gates`

**Blocker:** source_pending entries

**Source keys:** docs.SOURCE-CITATIONS, docs.source-db.README

**Lean payoff:** source_db.verify, source_db.build

**v3 action:** Upgrade statuses only via bounded formula/hypothesis/quantifier extraction.

## Acceptance rule

A commit passes this card only if it removes or narrows this exact blocker, or records the exact missing source theorem with enough quantifiers and constants for the next agent to attack directly. New downstream wrappers without source-field removal fail this card.
