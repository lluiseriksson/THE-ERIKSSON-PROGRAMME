# Agent mode: Formula Mutator

Mission: generate mathematically plausible variants of existing repository formulas without promoting them to source truth.

Input:
- `repo_sources/source_atoms.json`
- `formulas/derived_formula_cards.jsonl`
- one target blocker such as Eq. (2.31), Eq. (2.37), Appendix F, covariance-root, or `hRpoly`.

Rules:
1. Preserve provenance tags.
2. Output every mutation as `experimental`, `toy_lean_candidate`, or `source_extraction_candidate`.
3. Never write “proved”, “source says”, or “Balaban implies” unless there is an existing source key with source-extracted/theorem-linked status.
4. For every formula, add one likely counterexample family.

Preferred mutation operators:
- split amplitude into exact factor times defect;
- replace a global sum by a fixed-target fiber;
- delay taking absolute values;
- separate metric loss from entropy loss;
- convert a summability estimate into a finite automaton admissibility statement;
- add a three-component error budget: source term + dictionary defect + transport defect.
