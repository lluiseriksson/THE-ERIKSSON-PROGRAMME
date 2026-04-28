# Long Lake Build Run Evidence Scope

**Task**: `CODEX-CI-LONG-LAKE-BUILD-RUN-EVIDENCE-SCOPE-001`
**Date**: 2026-04-28T03:10:00Z
**Status**: `DONE_SCOPE_BLOCKED_NO_LONG_LAKE_BUILD_RUN_EVIDENCE`
**Recommendation**: `REC-COWORK-LONG-CI-LAKE-BUILD-001`

## Scope Result

No inspectable green `long-lake-build` run evidence was found.

The local workspace contains the intended long-timeout GitHub Actions job in
`.github/workflows/ci.yml`:

```text
job: long-lake-build
timeout-minutes: 120
command: lake build YangMills
```

That is task-spec evidence only. It is not completion evidence for the full
YangMills import graph.

## Evidence Checked

- `registry/recommendations.yaml` keeps `REC-COWORK-LONG-CI-LAKE-BUILD-001`
  `OPEN` and explicitly requires a real green GitHub Actions run before
  `audit_state.lake_build_full` may honestly move to `PASS`.
- `UNCONDITIONALITY_LEDGER.md` still records the full `lake build YangMills`
  graph as integration-pending after a local 15-minute timeout.
- `dashboard/agent_state.json` still records
  `audit_state.lake_build_full` as
  `CI_SPEC_ADDED_AWAITING_REAL_RUN`.
- GitHub Actions API checks for
  `https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/workflows/ci.yml`
  found successful workflow runs, but sampled job lists for recent successful
  runs `24958167532`, `24958146688`, and `24958047779` contained only
  `registry` and `lean-build`, not `long-lake-build`.
- GitHub contents API for `origin/main` `.github/workflows/ci.yml` did not
  contain `long-lake-build` at audit time, while the local file is modified to
  add it.
- `gh` is not installed locally, so no authenticated CLI artifact/log pull was
  available.

## Exact Blocker

The blocker is missing run evidence for the actual long job. To advance
`REC-COWORK-LONG-CI-LAKE-BUILD-001`, an auditor needs an inspectable GitHub
Actions run URL/job URL where `long-lake-build` completed with conclusion
`success`, or an equivalent local full `lake build YangMills` transcript with
exit code 0, date, and commit.

Until that evidence exists:

- Do not claim the full `lake build YangMills` graph is green.
- Do not close or downgrade `REC-COWORK-LONG-CI-LAKE-BUILD-001`.
- Keep `audit_state.lake_build_full` integration-pending.
- Keep F3-COUNT as `CONDITIONAL_BRIDGE`; no percentage moves.

## Validation

This task made no CI behavior changes and did not weaken Cowork polling or CI
requirements. YAML/JSON/JSONL validation should pass after registry updates.
