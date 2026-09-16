# hRpoly handoff — uniform/localized B0 gate

Date: 2026-08-24

## Objective and hard state

- Objective: close the physical hRpoly chain without renaming open obligations.
- Hard counters remain `20/41`; `TermSource = 0`.
- Window 15 remains compatible but not yet attained.
- PR #29 remains draft.

## Branch and checkpoints

- Repository: `C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian`
- Branch: `codex/cmp116-interacting-wilson-hessian`
- Immutable mathematical source: `73bb1a2008c557840a91e50d8abe6b874947f7ee`
- Published runner/control parent: `a754e28555270ebbdab8bff05f262368a39c43fa`
- Local terminal-workflow control commit: `ebccd7e8811d639587563fe060705811163e1c57`
- `a754e285..ebccd7e` changes exactly `.github/workflows/validate-localized-carrier.yml`.
- The worktree contains a large pre-existing unrelated dirty/untracked set. Preserve it.

## Colab result

One Colab Pro+ CPU/high-RAM cell was executed exactly once against the immutable source.
The runtime self-unassigned after completion.

- Runner revision: `source-flow-uniform-point-source-b0-v3`
- Launcher SHA-256: `2563bfba3de16b09733d2ae751a7f39ed0d29282386857ef51f8ed0767a29021`
- Lean: `4.29.0-rc6`
- Toolchain asset SHA-256: `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`
- Uniform focal: exit `0`, `2541.952 s`
- Uniform audit: exit `0`, `11.463 s`, exactly five allowed axiom blocks
- Localized focal: exit `0`, `39.544 s`, 8778 jobs
- Localized audit: exit `0`, `19.279 s`, exactly two allowed axiom blocks
- Allowed axioms: `{propext, Classical.choice, Quot.sound}`
- `FINAL_STATUS=PASS`
- Evidence inner SHA-256: `9d76e67d90772dadd6dbe4b3d553ae0c5865ed29910b697eb8115bb8c19a1cb3`
- Evidence archive SHA-256: `808fdcb3d2b4d737bb15234700da89d60da2d6cf797f7fdfedbdab70489a1722`

The notebook output is saved in Google Drive, but the automatic browser download did
not materialize in a locally verifiable path. Therefore the Colab stdout is accepted
as a successful compiler run but not yet as independently archived evidence.

## GitHub state

- User PowerShell successfully pushed `a754e285...` by fast-forward.
- The Codex sandbox cannot reach GitHub on port 443 and its `gh auth status` reports an
  invalid token. No remote mutation was made from the sandbox.
- No GitHub Action was dispatched for this checkpoint.

## Exact continuation

Run once in the owner's PowerShell:

```powershell
pwsh -NoProfile -ExecutionPolicy Bypass -File `
  "C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian\tmp\push_and_run_uniform_b0_terminal.ps1"
```

The script verifies identity, ancestry, exact one-file diff, remote parent, and the
post-push remote SHA; it then dispatches one cold terminal workflow and prints its run
ID/URL. It has no force-push, checkout, reset, logout, or rerun path.

After the run completes, download the durable artifact once, verify it with:

- `tmp/audit_uniform_localized_b0_terminal_evidence.py`
- `tmp/retrieve_uniform_localized_b0_terminal_evidence.ps1`

Only after that verification may the corresponding PRE-VALIDATION marks be retired.
Do not count a terminal-field movement from this gate alone; the hard state remains
`20/41`, `TermSource = 0`.

## Next mathematical step after sealing

Resume the physical regional/Dirichlet bridge toward attaining window 15. The C6d
regularity-class draft remains scratch PRE-VALIDATION; do not replace its missing
global adjoint theorem with a hypothesis or record field.
