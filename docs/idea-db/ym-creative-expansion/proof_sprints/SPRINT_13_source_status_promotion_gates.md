# Sprint 13 — source status promotion gates

## Purpose

Prevent operational metadata from being promoted to source theorem evidence.

## Allowed promotion

```text
source_pending -> source_extracted
```

requires:

- bounded source window;
- formula statement;
- assumptions;
- quantifier order;
- constants and parameter dependencies;
- convention dictionary;
- local artifact hash or source URL;
- Lean target mapping.

```text
source_extracted -> theorem_checked
```

requires:

- Lean theorem compiles;
- oracle check remains standard only;
- no `sorry`, no project axiom;
- no import into `YangMillsCore` unless theorem belongs to verified core.
