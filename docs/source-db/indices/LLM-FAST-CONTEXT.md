# LLM Fast Context Brief — Source DB Batch 003

This file is designed to be read before an LLM analyzes `THE-ERIKSSON-PROGRAMME`.
It gives the shortest safe context needed to connect source papers, formulas,
Lean consumers and open hypotheses.

## Current source database state

- Sources indexed: 14
- Citation/crosswalk/proof-card records: 62
- Claim/formula/proof-obligation records: 215
- Lean target links: 274
- Blocking citations: 10

## Highest-value source-removal targets

1. **CMP116 Eq. (2.31) P-family dictionary** — prove the source membership iff and identify Balaban's eligible carrier with the already counted repository carrier. Do not add downstream wrappers.
2. **CMP116 Eq. (2.29) D-stage** — extract Cammarota CMP85 theorem and dictionary.
3. **CMP116 Eq. (2.37)** — prove fixed-Z0' estimate and final summation; keep route combined.
4. **Activity/termwise** — identify H(Z) summands with physical activity and prove norm estimate.
5. **Gaussian/root/Hessian** — source-feed coordinate dictionary, Jacobian, covariance root and Hessian facts.
6. **CMP119/CMP122 R-operation** — keep polymer-local bounds distinct from scalar geometric surrogates.
7. **Flow/IR** — separate marginal logarithmic gauge flow from irrelevant geometric contraction.

## Three recurring traps

- A lower bound on `|P|` is not an upper bound on the eligible carrier.
- Dimock Appendix F uses Omega-connectivity, not ordinary full-polymer overlap.
- Balaban's R-operation bounds are polymer-local; `|R_k| <= M*r^k` needs an extra bridge.

## Query commands

```powershell
python scripts\source_db.py search "Eq. (2.31)"
python scripts\source_db.py lean CMP116Eq231PBondBoundary
python scripts\source_db.py show crosswalk.eq231.p-family-source-dictionary-route
python scripts\source_db.py show proof.eq231.membership-iff.source-package
python scripts\source_db.py show proof.eq231.carrier-count.four-positive-directions
python scripts\source_db.py blockers
python scripts\source_db.py coverage
```

## Files added by batch 002

- `docs/source-db/catalogs/llm-operational-crosswalk.json`
- `docs/source-db/indices/FORMULA-REGISTRY.md`
- `docs/source-db/indices/LEAN-SOURCE-CROSSWALK.md`
- `docs/source-db/indices/BLOCKER-MATRIX.md`
- `docs/source-db/indices/PAPER-COVERAGE-MATRIX.md`
- `docs/source-db/indices/SYMBOL-DICTIONARY-SEED.md`
- `docs/source-db/indices/DEPENDENCY-GRAPH.md`

## Files added by batch 003

- `docs/source-db/catalogs/proof-obligation-cards.json`
- `docs/source-db/indices/PROOF-OBLIGATION-CARDS.md`
- `docs/source-db/indices/HYPOTHESIS-REMOVAL-QUEUE.md`
- `docs/source-db/indices/SOURCE-KEY-ROUTER.md`
- `docs/source-db/indices/AGENT-CHECKLISTS.md`
- `docs/source-db/indices/LLM-QUERY-PROMPTS.md`

Batch 003 records are operational proof cards. They route agents from a live
hypothesis to source keys and Lean declarations; they are not primary-source
evidence.
