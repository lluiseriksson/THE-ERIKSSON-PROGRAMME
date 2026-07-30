# CONTINUUM-C1 build transcript

## Environment

- Source branch: `codex/continuum-c1`
- Source base: `81721890ad3e111d73cbe45074d42ec698ce07b2`
- Dependency worktree: same source SHA, with existing Lake artifacts
- Date: 2026-07-30

The lane worktree's Mathlib package checkout was incomplete. The source file
was therefore compiled by absolute path from another worktree at the exact
same repository SHA; no theorem or source from that worktree was imported.

## Lean build and oracle

```text
lake env lean <C1-worktree>/YangMills/Continuum/TightnessScaleNoGo.lean
```

Exit code: `0`.

```text
'YangMills.ContinuumC1.beta_lt_kpBetaCap' depends on axioms:
[propext, Classical.choice, Quot.sound]

'YangMills.ContinuumC1.not_kpRadiusAtUnit_beta2D' depends on axioms:
[propext, Classical.choice, Quot.sound]

'YangMills.ContinuumC1.eventually_not_kpRadiusAtUnit_of_tendsto'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No project axiom appears.

## Prose checker

```text
python scripts/check_module_prose.py \
  YangMills/Continuum/TightnessScaleNoGo.lean
```

```text
YangMills/Continuum/TightnessScaleNoGo.lean    OK

modules checked: 1  failures: 0
```

## Static checks

- `git diff --check`: clean.
- `rg "sorry|axiom "` finds only the prose phrase “No sorry” in the module
  header; there is no declaration.
