# CONTINUUM-C1 build transcript

## Environment

- Source branch: `codex/continuum-c1`
- Source base: `81721890ad3e111d73cbe45074d42ec698ce07b2`
- Dependency worktree: same source SHA, with existing Lake artifacts
- Latest run: 2026-07-31

The lane worktree's Mathlib package checkout was incomplete. The source file
was therefore compiled by absolute path from another worktree at the exact
same repository SHA; no theorem or source from that worktree was imported.

## Lean build and oracle

```text
lake env lean <C1-worktree>/YangMills/Continuum/TightnessScaleNoGo.lean
```

Exit code: `0`.

```text
'YangMills.ContinuumC1.kpRadiusAtUnit_nonempty_from_checkedWindow'
depends on axioms:
[propext, Classical.choice, Quot.sound]

'YangMills.ContinuumC1.checkedCorrelatorAfterKPRadiusAtUnit'
depends on axioms:
[propext, Classical.choice, Quot.sound]

'YangMills.ContinuumC1.kpRadiusAtUnit_witness_4_3'
depends on axioms:
[propext, Classical.choice, Quot.sound]

'YangMills.ContinuumC1.beta_lt_kpBetaCap' depends on axioms:
[propext, Classical.choice, Quot.sound]

'YangMills.ContinuumC1.not_kpRadiusAtUnit_beta2D' depends on axioms:
[propext, Classical.choice, Quot.sound]

'YangMills.ContinuumC1.eventually_not_kpRadiusAtUnit_of_tendsto'
depends on axioms:
[propext, Classical.choice, Quot.sound]

'YangMills.ContinuumC1.unitScale_kpCap_small' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No project axiom appears. The run emitted no warning.

The non-vacuity theorem invokes `sun_clustering_window_nonempty`.
`checkedCorrelatorAfterKPRadiusAtUnit` also partially applies the actual
`sun_two_plaquette_correlator_bound` through `hr`; Lean infers the remaining
dependent function type. Together these are compile-time guards connecting
`KPRadiusAtUnit` to both the witness producer and the checked consumer.

## Prose checker

```text
python scripts/check_module_prose.py \
  YangMills/Continuum/TightnessScaleNoGo.lean
```

```text
YangMills/Continuum/TightnessScaleNoGo.lean    OK

modules checked: 1  failures: 0
```

## Automated window canary

```text
python scripts/continuum_c1_window_canary.py --self-test
```

```text
CONTINUUM-C1 window canary + mutation self-test: PASS
```

The script extracts `KPRadiusAtUnit` and the actual `hr` argument of
`sun_two_plaquette_correlator_bound`, specializes the exponent text to
`t=ε=1`, and compares the whitespace-normalized bodies. Its self-test changes
the exponent to `1+1+2` and requires the comparison to differ. The GitHub
`honesty` job invokes this command; the canary is an automated drift alarm,
not a mathematical proof.

## Static checks

- `git diff --check`: clean.
- `rg "sorry|axiom "` finds only the prose phrase “No sorry” in the module
  header; there is no declaration.
