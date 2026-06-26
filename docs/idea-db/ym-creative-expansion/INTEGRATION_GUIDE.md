# Integration guide for the constructor

## Recommended commit sequence

### Commit 1 — Add the idea database without touching the verified core
- Copy `repo_sources/`, `formulas/`, `data/`, `schemas/`, `scripts/query_expansion_db.py` under `docs/idea-db/ym-creative-expansion/`.
- Add a short README explaining that this is **not** a source DB and **not** theorem evidence.
- Run only JSON/schema/script checks.

### Commit 2 — Add safe bookkeeping Lean toys outside `YangMillsCore`
- Start with `D01.YMActivityBudget.min_exponent_triangle` and `D09.eq237_metric_stitching_product_extraction`.
- Use a namespace like `YangMills.Experimental` or `YangMills.RG.Experimental`.
- Do not import these from `YangMillsCore` until they are useful and oracle-clean.

### Commit 3 — Source-honest Eq. (2.31) membership iff
- Use `D06.eq231_admissible_automaton` only to structure the proof.
- The real theorem must be source-shaped from CMP116/CMP109 and target the existing consumers.
- Expected target: `CMP116Eq231SourcePIndexMemIff` or the currently preferred project naming.

### Commit 4 — Eq. (2.37) metric extraction / final summation scaffold
- Prove the algebraic metric-product lemma.
- Keep `sourceZ0PrimeIndex` and repository `cmp116Eq237GlobalZ0PrimeIndex` separate until the dictionary theorem exists.

### Commit 5 — High-risk/high-payoff covariance-root toy
- Implement a diagonal finite SPD model for D04 before attempting spectral calculus.
- The output is a certificate shape, not a physical theorem.

## Minimal validation

```bash
python docs/idea-db/ym-creative-expansion/scripts/query_expansion_db.py --list-cards
python docs/idea-db/ym-creative-expansion/scripts/query_expansion_db.py --search eq231
python docs/idea-db/ym-creative-expansion/scripts/query_expansion_db.py --queue
```

## Promotion gates

A derived card can move from idea to Lean target only if:

1. it has exact hypotheses;
2. it names what source atoms it depends on;
3. it has a finite toy theorem or a direct source theorem target;
4. it does not erase target, support, sign, gauge or scale data needed later;
5. it says which live hypothesis it removes.


## v2 additions

- Start from `rankings/BUILDER_PRIORITY.md`.
- Use `agent_modes/falsifier.md` before creating Lean files.
- Prefer `proof_sprints/SPRINT_01_eq231_membership_iff.md` as the next real-payoff task.
- Keep `source_patch_templates/*` experimental until source extraction is complete.


## v4 integration note

Do not copy the whole v4 pack into theorem-bearing code.  Use it as a local agent
runner.  Only these outputs should become repository commits:

1. source-db status promotion with exact extraction;
2. a Lean theorem discharging a named source-package field;
3. a narrowed blocker in a proof card;
4. a CI/tooling check that enforces no-new-consumers or source-promotion gates.

The mission contracts are disposable execution aids.  Theorems and source records
remain the repository source of truth.
