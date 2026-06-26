# Batch 003 — Proof-Obligation Cards and Source-Key Router

Batch 003 adds theorem-shaped operational metadata. It does not scan new primary pages and does not promote source status. Its purpose is to prevent future agents from adding cosmetic wrappers and to point every live hypothesis at the smallest source theorem that can remove it.

## Added

- `proof-obligation-cards.json`: 12 operational proof cards indexed by source key and Lean target.
- `PROOF-OBLIGATION-CARDS.md`: human theorem-card view.
- `HYPOTHESIS-REMOVAL-QUEUE.md`: ordered queue of live source hypotheses.
- `SOURCE-KEY-ROUTER.md`: reverse map from citation/source key to proof cards.
- `AGENT-CHECKLISTS.md`: promotion and anti-error gates.
- `LLM-QUERY-PROMPTS.md`: ready prompts for source extraction agents.

## Highest-payoff next commits

1. CMP116 Eq. (2.31) P-family membership iff and carrier count.
2. Cammarota CMP85 theorem feeding CMP116 Eq. (2.29).
3. CMP116 Eq. (2.37) fixed-Z0' estimate plus final summation.
4. Activity/termwise identification for H(Z).

## Scope

All new records use `repo_operational_crosswalk` and `status=lean_linked`; they are not primary source claims and all formula entries are `source_verified=false`.
