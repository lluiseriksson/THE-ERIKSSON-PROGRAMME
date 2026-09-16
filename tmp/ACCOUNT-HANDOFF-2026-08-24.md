# hRpoly account handoff — 2026-08-24

- Objective: validate the unified uniform-B0 + literal source-flow C6b queue.
- Branch: `codex/cmp116-interacting-wilson-hessian`
- Local HEAD / runner checkpoint: `59b2ddf5a34d4cd52dc54a617b53975124ca45f6`
- Remote tracking before handoff: `602ab7a3`; the exact HEAD push has not yet been executed.
- Worktree: tracked checkpoint files committed; unrelated untracked material must be preserved.
- Active external processes/runtimes: none.
- GitHub: the user's PowerShell recovery verified account `lluiseriksson`, API access, HTTPS helper, and repository read access. No push or worktree mutation occurred during recovery.
- Colab: no active runtime.
- Mathematical status: new uniform-B0 and localized-field C6b modules remain `PRE-VALIDATION`; no local Lean/Lake was run; hard counters remain `20/41`, `TermSource = 0`, window 15 compatible but unattained.

## Exact continuation

In the authenticated user PowerShell:

```powershell
$repo="C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian"
git -c "safe.directory=*" -C $repo push github `
  59b2ddf5a34d4cd52dc54a617b53975124ca45f6:refs/heads/codex/cmp116-interacting-wilson-hessian
```

After confirming the remote SHA, open one Colab Pro+ CPU/high-RAM runtime and execute exactly once:

- runner: `scripts/colab_source_flow_uniform_point_source_b0_validation.py`
- runner checkpoint: `59b2ddf5a34d4cd52dc54a617b53975124ca45f6`
- runner SHA-256: `1ad575d5c0d814e4a15f0f414f91c2b43bf1f7ac8b8d655ef0974a7a83bd6165`
- source checkpoint compiled by runner: `f681aacdeab3be53ccb0abb70c93493236515323`

Queue: uniform B0 focal/audit, then localized-field focal/audit, stop on first error. On PASS preserve and hash evidence, disconnect the runtime, and seal only the verified modules. On FAIL preserve the first real error and retain `PRE-VALIDATION`.
