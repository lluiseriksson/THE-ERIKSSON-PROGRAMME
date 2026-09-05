# Durable handoff — source-flow C3

Date: 2026-08-23

## Current objective and result

The atomic objective was C3: compose the sealed source-flow point-source
endpoint (C1b) with the sealed literal zero-residue aliasing identity (C2).
The exact source and audit passed in one fresh Colab Pro+ CPU/high-RAM clone.

- `FINAL_STATUS=PASS`
- build: 8,762 jobs
- focal: `exit=0`, `2507.291 s`
- audit: `exit=0`, `16.847 s`
- audited declaration: exactly `[propext, Classical.choice, Quot.sound]`
- evidence SHA-256:
  `20958A8BE610544F453C5463DF2491A42D87EA68588C10A318755906FB164271`
- evidence archive SHA-256:
  `7F0DA1D4E30468B6D3061ABA9087EB7BDE520159DA0249863E7141E4882D6A88`

The Colab runner requested release and the UI showed
`Återanslut Mycket RAM-minne`; there is no live Colab process to kill.  The
single notebook tab remains available but disconnected.  No local external
process from this block is active.

## Git state

- repository:
  `C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian`
- branch: `codex/cmp116-interacting-wilson-hessian`
- PRE-VALIDATION source checkpoint:
  `5099e6f02d209f4503e2db04a4793048b4a5dcb5`
- runner checkpoint:
  `224684a63e149c6915fa519ba3be6e3a4b464ac5`
- seal checkpoint:
  `f023ac85997016eede1769f72534feeea0f33ff0`
- documentation checkpoint before this handoff record:
  `ef44f131227681633cc5955179531194b46c43b1`
- source/audit Git-blob SHA-256:
  `16545F173048FDBABA1081FB300CA152A9B524C7B87D8F1DA768793DC1A35004`,
  `B4A8A92348D693AB17514DDD8BB8D3406E60F440D139EBE1DD437CAB4853BCE9`
- runner SHA-256:
  `ACC8E219E4C62BBDCFBAD2AD51AA1B34E077F1D5EBC3DD18A8ADDA090678832F`

At capture time the tracked worktree was clean.  There were 4,317 preserved
untracked entries belonging to the existing scratch/evidence workspace; none
was deleted or rewritten.  Relevant C3 scratch files include:

- `tmp/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceZeroResidue.draft.lean`
- `tmp/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceZeroResidueAudit.draft.lean`
- `tmp/source-flow-point-source-zero-residue-seal-paths.txt`

## GitHub state

`gh auth status --hostname github.com` was verified immediately before this
record: active keyring account `lluiseriksson`, HTTPS protocol, scopes
`gist`, `read:org`, `repo`, and `workflow`.  No logout or credential change
was performed.  Before the final handoff push the remote branch was exactly
runner checkpoint `224684a63e149c6915fa519ba3be6e3a4b464ac5`; the seal,
documentation, and this handoff record are intended to advance it by a
fast-forward only.

## Exact continuation commands

Run only these light state checks on Windows after the account transition:

```powershell
$repo="C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian"
gh auth status --hostname github.com
git -c "safe.directory=*" -C $repo status --short --branch
git -c "safe.directory=*" -C $repo rev-parse HEAD
git -c "safe.directory=*" -C $repo ls-remote github refs/heads/codex/cmp116-interacting-wilson-hessian
```

Do not run Lean/Lake/oracles on Windows.  The next brick is C4, the
source-flow owner-bound continuation downstream of the now sealed C3
point-source zero-residue identity.  Prepare it statically, publish a raw
source checkpoint by fast-forward, and validate heavy work only in Colab Pro+
CPU/high-RAM.  No C4 work has been started during this handoff.

Hard counters remain exactly `20/41`, `TermSource = 0`; window 15 remains
compatible but unattained.
