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


## v5 integration note

Copy v5 over the existing idea DB only as process metadata.  The new scripts are local helper tools; they do not certify theorem status.  Keep `patch_intake/`, `source_locks/` and `mission_contracts/` together so a future reviewer can reconstruct why a patch was accepted or rejected.
## v6 Batch-006 lane

When working near `BalabanCMP116SourceAssumptions`, choose exactly one live field
from `data/batch006_live_field_map.v6.json` and one corresponding mission
contract.  Do not use downstream H# identities, final Lemma 3 bounds, or scalar
Dimock architecture to backfill upstream Gaussian/root/Hessian fields.

Minimal v6 workflow:

```bash
python scripts/field_board.py --order
python scripts/batch006_prompt_compiler.py covariance_root_certificate
python scripts/generate_patch_intake.py OC_016_covariance_root_certificate_dictionary > patch_intake/oc016.json
python scripts/check_no_backfill.py patch_intake/oc016.json
python scripts/score_patch_intake.py patch_intake/oc016.json
```

A useful patch either removes one field from the live-field map, promotes a
source record under the source promotion state machine, proves a narrow theorem
skeleton, or sharpens the exact blocker enough that the next agent can attack a
single theorem statement.
