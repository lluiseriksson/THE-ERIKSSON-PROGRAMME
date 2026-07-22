# Incident: legacy run-manifest drift in global validator

**Date:** 2026-07-22  
**Scope:** provenance infrastructure only; no mathematical promotion

The first repository-wide run of `scripts/validate_run_manifests.py` reported
175 JSON files and 1,180 structural/hash errors. After migrating the three new
CWIN=4 candidate manifests to schema v1, the same run reports 1,139 residual
errors in the historical set. The failures fall into two
separate classes:

1. Historical manifests use pre-schema layouts and therefore lack fields such
   as `schema_version`, UTC timestamps, `command`, `environment`, `inputs`,
   `outputs`, and `supersedes`.
2. Several otherwise structured historical manifests record `sha256_lf`
   values for an earlier line-ending/worktree representation. Their current
   files are not byte-identical to those recorded values.

This is not evidence that the corresponding mathematics changed, and no hash
has been rewritten retroactively. The affected records remain historical
until each one is either migrated with a dual-hash addendum or explicitly
quarantined under the manifest policy. The new CWIN=3/2 `[30,31]` and CWIN=4
`[31,37]` candidate manifests pass independent path/hash/production-replay
checks and are not part of this incident.

**Required repair before a repository-wide green provenance audit:**

* inventory legacy schemas and assign each a stable status;
* add an explicit migration/dual-hash record for any retained artifact;
* rerun the strict validator and preserve the failure transcript until it is
  green.

This incident does not alter G2, K2, K4, S1‴/S2‴, G6, or the manuscript
submission state.
