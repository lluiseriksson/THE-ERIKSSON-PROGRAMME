# Long Lake Build CI Plan

**Task**: `CODEX-CI-LONG-LAKE-BUILD-TASK-SPEC-001`
**Date**: 2026-04-26T18:05:00Z
**Status**: `CI_SPEC_ADDED_AWAITING_REAL_RUN`
**Recommendation**: `REC-COWORK-LONG-CI-LAKE-BUILD-001`

## Outcome

The repository already had a GitHub Actions convention in:

```text
.github/workflows/ci.yml
```

Codex added a long-timeout job:

```yaml
long-lake-build:
  timeout-minutes: 120
  ...
  - name: lake build (full YangMills integration target)
    run: lake build YangMills
```

The job uses the same Lean/Lake installation pattern as the existing narrow CI
build, then runs `lake exe cache get` before the full `lake build YangMills`.

## Blocked Step

The job has not yet run on GitHub Actions in this workspace.  Therefore the
project must not claim that the master import graph is fully green yet.

The remaining blocked step is:

```text
Observe one real GitHub Actions run of long-lake-build finishing with exit code 0.
```

Until that happens:

- `REC-COWORK-LONG-CI-LAKE-BUILD-001` remains `OPEN`.
- `dashboard/agent_state.json` keeps `audit_state.lake_build_full` at
  `INTEGRATION_PENDING`.
- No mathematical ledger row or project percentage moves.

## Validation

Local validation for this task is limited to CI-spec coherence:

```text
python -c "import yaml; yaml.safe_load(open('.github/workflows/ci.yml'))"
```

The actual full integration validation is the future CI run itself.
