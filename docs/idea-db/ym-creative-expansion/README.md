# YM Creative Expansion Pack — 2026-06-26

This ZIP is a handoff package for agents working on `lluiseriksson/THE-ERIKSSON-PROGRAMME`.

It combines five repositories into a **source-aware idea database**:

- `THE-ERIKSSON-PROGRAMME`: current Yang-Mills Lean core, CMP116/CMP109/CMP119/Dimock source frontier, and `hRpoly` live UV target.
- `riemann-prime-resolvent`: reusable finite error-budget, resolvent positivity, prime-tail and rate templates.
- `lean-rooted-tree-polymer-expansion`: verified target-preserving rooted-tree summation and 4^n closure.
- `physmath-knowledge-tree`: evidence-labelled research moves and audit discipline.
- `rooted-tree-catalan-closure`: Catalan closure, finite evidence and Prüfer-profile plan for the exact rooted-child factorial identity.

## What this pack is

A structured generator of **new candidate formulas**, proof routes, Lean toy targets, and source-aware handoff tasks.

## What this pack is not

It is not a proof of Yang-Mills, not a source citation database, not a replacement for CMP/Balaban/Dimock papers, and not something to import into `YangMillsCore`.

## Repository integration note

This copy is staged under `docs/idea-db/ym-creative-expansion/` so it remains
separate from the verified Lean core and from `docs/source-db`.  Some cards were
generated before the repository named the Eq. (2.31) repository carrier-count
lemmas (`cmp116Eq231GapCarrier_*`); when there is a conflict, the repository
source-db and Lean files are authoritative.  The remaining Eq. (2.31) blocker is
the CMP116/CMP109 source identification of Balaban's eligible carrier and
membership predicate, not the elementary repository carrier count.

## Most important files

| File | Purpose |
|---|---|
| `repo_sources/source_atoms.json` | Compact source/verified atoms extracted from the repos. |
| `formulas/derived_formula_cards.jsonl` | Invented/derived candidate formulas with risks and blockers. |
| `formulas/derived_formula_cards.md` | Human-readable formula cards. |
| `data/ym_formula_expansion.sqlite` | Queryable SQLite idea database. |
| `data/handoff_queue.json` | Ranked tasks for the constructor. |
| `prompts/constructor_main_prompt.es.md` | Prompt to give the construction agent. |
| `GOVERNANCE_AND_HONESTY.md` | Guardrails preventing false progress. |
| `lean_templates/*.lean.template` | Lean-like sketches, deliberately not compilable core files. |

## Quick query

```bash
python scripts/query_expansion_db.py --list-cards
python scripts/query_expansion_db.py --search eq237
python scripts/query_expansion_db.py --queue
```

## Best immediate payoff

1. Eq. (2.31) source membership iff / admissible P automaton.
2. Eq. (2.37) metric-product extraction lemma.
3. YM activity error-budget theorem.
4. Covariance-root resolvent finite toy.
5. Catalan/target-preserving second-Ursell closure experiment.

## Non-negotiable honesty boundary

Even a complete `hRpoly` discharge gives only the unconditional **lattice M3** mass-gap route already assembled in the repository. The continuum Clay problem still requires continuum limit, reconstruction and physical mass-gap identification.
