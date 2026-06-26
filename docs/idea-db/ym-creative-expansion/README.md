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


## v2 quick start

```bash
python scripts/query_expansion_db.py --list-cards
python scripts/query_expansion_db.py --search Eq231
python scripts/query_expansion_db.py --queue
```

Read `builders/CONSTRUCTOR_PLAYBOOK_v2.es.md` and `rankings/BUILDER_PRIORITY.md` before integrating anything.
