# Governance and honesty rules

1. **No derived card is a source citation.** Use `repo_sources/source_atoms.json` for source atoms and `formulas/derived_formula_cards.jsonl` for invented/derived candidates.
2. **No candidate file belongs in `YangMillsCore` until theorem-fed.** Start under `docs/idea-db/`, `Experimental/`, or `.lean.template` files.
3. **Every formula needs a status.** Allowed statuses here: `repo_statement`, `source_extracted`, `visual_confirmed_or_lean_encoded`, `verified_toy_mechanism`, `experimental_derived_formula`, `speculative_derived_formula`, `governance_formula`.
4. **Source DB ingestion rule:** only ingest source-backed formulas from `source_atoms`. Derived cards may be indexed in an idea DB, not in `docs/source-db` as theorem evidence.
5. **Clay boundary:** discharging `hRpoly` gives only the lattice M3 route already assembled in the repo. It does not give continuum limit, OS/Wightman reconstruction, or the Clay theorem.
6. **No silent zero-defect dictionary.** If a physical-to-source comparison is used, all dictionary, support, Jacobian, covariance/root and activity defects must be fields or proved zero by named theorems.
7. **Prefer small Lean toys.** A speculative formula earns promotion only after a finite model compiles and a counterexample search fails on the intended toy scope.
