# Agent Checklists — Batch 003

## Before opening a paper

1. Run `python scripts/source_db.py search "<term>"`.
2. Run `python scripts/source_db.py show <citation-key>`.
3. Run the legacy excerpt command when a local-text range exists: `python scripts/source_citations.py excerpt <key> -C 3`.
4. Read `SOURCE-KEY-ROUTER.md` for the key before creating new wrappers.
5. Only then open the rendered page or PDF page named by the citation.

## Before promoting to `source_extracted`

A record may be promoted only when it contains:

- exact printed and PDF pages;
- exact theorem/equation/paragraph locator;
- formula with quantifiers, assumptions, constants and index dependencies;
- source-symbol to Lean-symbol dictionary;
- `use_for` and `do_not_use_for` lists;
- at least one Lean target;
- open questions restricted to downstream issues, not the extracted statement itself.

## Before claiming a hypothesis removed

- Identify the exact field/hypothesis name.
- Name the theorem that supplies it.
- Show which previous caller premise disappears.
- Run `lake build YangMillsCore` and `lake env lean oracle_check.lean` in the real checkout.
- Update the proof card status only after the Lean consumer is actually theorem-fed.

## Red flags

- A lower bound on one summand's size is used as an upper bound on the carrier.
- `admissible` is defined tautologically from membership in `PIndex`.
- CMP109's orientation convention is cited as the CMP116 carrier theorem.
- Dimock Appendix F is treated as ordinary overlap instead of Ω-connectivity.
- Balaban polymer-local R bounds are rewritten as scalar `M*r^k` without a flow/irrelevant-operator bridge.
- An OCR-only formula is used to set signs, constants, exponents or summation domains.
