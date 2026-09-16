# Account-transfer checkpoint: source-flow C4

Date: 2026-08-23

## Durable state

- Objective: close the literal source-flow chain without inflating the terminal counters. C4 is the physical point-source owner bound; C5 is the next source-owner specialization.
- Branch: `codex/cmp116-interacting-wilson-hessian`.
- Sealed source HEAD before this handoff record: `f638ae1b70d713d628c9fa13929b319f8a4717f5`.
- C4 seal commit: `2e9d6349c83a50e54591d3e571e0e526cff9e128`.
- C4 PRE source checkpoint: `934efa2a281824db90d13724eb143f7df2a7c4db`.
- C4 repaired source checkpoint: `8bb90cd1f666ad94eca099ec26cd81d29239f0b8`.
- C4 validation runner checkpoint: `9c37609b8cdc2a6172c23fb087e76c8fc7ffab93`.
- C4 runner revision: `source-flow-point-source-owner-bound-v2`.
- C4 runner SHA-256: `b05e4c1551dbc0a1799e96b6fd1203703628c76ab7b5faa8d398f021b9bb6865`.

## Gate result

Fresh Colab Pro+ CPU/high-RAM validation passed:

- `FINAL_STATUS=PASS`.
- focal: exit `0`, 8773 jobs, 2830.365 s.
- audit: exit `0`, 19.501 s.
- both audited declarations: exactly `[propext, Classical.choice, Quot.sound]`.
- evidence SHA-256: `aa5c556db3aba0e293e8c19e7aa41ba24c25bc8877951e22aefe0081f68109eb`.
- evidence archive SHA-256: `05bcdaac8cc1a0a6001850a10da330c7630337b08a9750ba0106419612928b78`.
- source blob SHA-256: `0988be971b058d18e5383f7733b6cb27c9c109b71f69216f51fcecd69f25a2ea`.
- audit blob SHA-256: `8e9751454782a53562d671a7f7336f7b5b0021bc1ad4d3956c11ce327d196403`.

The first v1 attempt remains preserved as diagnostic evidence. It stopped at the first elaboration error caused by an omitted `(K := Kfine)` and did not count as validation:

- diagnostic evidence SHA-256: `a1659185736632ff333c7e81f918f371a99809443d0a633e097a525a619d942f`.
- diagnostic archive SHA-256: `91a05376a833319943bdc96e9d34ac71dc860b67270282554bfa09c29c0ebd2a`.

## Runtime and external processes

- No Colab calculation is active. The successful runner auto-unassigned the runtime after emitting `FINAL_STATUS=PASS`; the UI returned to the disconnected/reconnect state before this transfer request arrived.
- No local Lean, Lake, oracle, scientific Python, GitHub Action, push, or other external computation is active.
- The single Colab notebook tab may remain open, but it has no assigned runtime.

## GitHub state

- `gh auth status --hostname github.com` succeeded immediately before this checkpoint.
- Active account: `lluiseriksson` via keyring; Git protocol HTTPS; scopes include `repo` and `workflow`.
- No logout, credential change, force-push, workflow dispatch, or rerun was performed for the transfer.
- PR #29 remains draft.
- The final handoff commit containing this record is pushed fast-forward after this file is committed; verify its exact SHA with the commands below.

## Relevant uncommitted material

There are no tracked source or documentation edits left pending after the handoff commit. The workspace contains a large pre-existing untracked archive that must not be cleaned. The only next-step scratch material intentionally preserved is:

- `tmp/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBound.draft.lean`
- `tmp/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBoundAudit.draft.lean`
- `tmp/source-flow-source-owner-bound-draft-paths.txt`
- `tmp/source-flow-point-source-owner-bound-paths.txt`
- `tmp/source-flow-point-source-owner-bound-seal-paths.txt`

The C5 draft passed only textual guards. It is **not compiler-verified** and must remain scratch until promoted with PRE-VALIDATION markings.

## Exact continuation commands

Run only lightweight Git inspection on Windows:

```powershell
$repo='C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian'
git -c 'safe.directory=*' -C $repo branch --show-current
git -c 'safe.directory=*' -C $repo rev-parse HEAD
git -c 'safe.directory=*' -C $repo status --short --untracked-files=no
git -c 'safe.directory=*' -C $repo ls-remote github refs/heads/codex/cmp116-interacting-wilson-hessian
gh auth status --hostname github.com
```

Then continue with C5, without starting a new long block before reviewing this checkpoint:

1. Promote the two C5 scratch drafts to tracked source/audit modules using `apply_patch`.
2. Add explicit PRE-VALIDATION module markings.
3. Run the lightweight import-prefix and overlay text guards over exactly the promoted paths.
4. Commit the source pair as a PRE source checkpoint.
5. Derive a C5 Colab runner from the C4 v2 runner; queue only the C5 focal and audit.
6. Verify Git blob hashes, `gh` account, and fast-forward ancestry; push without force.
7. Validate once in fresh Colab Pro+ CPU/high-RAM, stop on first error, and seal only on literal PASS.

## Counters and boundary

- `20/41`.
- `TermSource = 0`.
- Window 15 remains compatible but unattained.
- C4 is infrastructure in the literal source-flow chain and does not move any terminal counter.
- C5 is the next bounded brick; it has not started as tracked source and has not been compiled.
