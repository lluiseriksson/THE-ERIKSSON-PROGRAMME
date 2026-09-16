# hRpoly source-flow C5 account-transfer checkpoint

Status recorded on 2026-08-23 after the single authorized C5 Colab gate returned
`FINAL_STATUS=PASS`.  This file is the durable handoff checkpoint; the exact
evidence identifiers below are the compiler record for the C5 seal.

## Current objective

Validate and then seal the source-faithful C5 specialization
`BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBound`: evaluate the
literal source-flow point-source endpoint at
`cmp99Eq389SourceLocalizationSiteEquiv`, rewrite the owner to
`cmp99Eq389SourceLocalizationOwner`, and preserve the literal coefficient
`cmp99SourceFlowFlatFullComplexA a L depth`.

This brick does not produce a generated coefficient, a free Green/readout, a
uniform `B0`, window-15 attainment, or a terminal field.  The hard counters stay
exactly `20/41`, `TermSource = 0`, and window 15 compatible but unattained.

## Git state

- repository: `C:/Users/lluis/Documents/Codex/2026-07-12/pu/work/THE-ERIKSSON-PROGRAMME-wilson-hessian`
- branch: `codex/cmp116-interacting-wilson-hessian`
- C5 source checkpoint: `60537615aab13f687253473f988bf5e2a7281c4f`
- runner checkpoint / source used by Colab:
  `86e293e888d3fb1d553ead114357d94d17efafa1`
- C5 seal checkpoint:
  `6543e50187cc671306a0f4cda14cb1b13108df50`
- final handoff/documentation checkpoint: this document is part of that commit;
  use the `git rev-parse HEAD` value reported with `LISTO-PARA-CAMBIO` as its
  non-recursive authoritative SHA
- push policy: fast-forward only; never force-push
- tracked worktree: clean at checkpoint time
- untracked worktree: large pre-existing campaign scratch/evidence inventory;
  preserve it and do not clean it

GitHub CLI was verified as authenticated through the Windows keyring to the
active account `lluiseriksson`, HTTPS protocol, with scopes
`gist`, `read:org`, `repo`, and `workflow`.  Do not log out or rotate credentials
as part of this handoff.

## C5 tracked inputs

- `YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBound.lean`
  - Git-blob SHA-256:
    `79593551380c35c9b023d2ca04303ed758edf286e4c1ac56ac453ab768174da0`
- `YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBoundAudit.lean`
  - Git-blob SHA-256:
    `3d19746d80d46aa84406b1c139cdcbf7c2e038c9fda06d46e9284f82b263e5dd`
- runner: `scripts/colab_source_flow_source_owner_bound_validation.py`
  - runner revision: `source-flow-source-owner-bound-v1`
  - Git-blob SHA-256:
    `b6e2d8b8c64590562525e639577d3cd6d30bedd9b5749aeacc69ac6b2cc02f09`
  - pinned parent runner commit:
    `9c37609b8cdc2a6172c23fb087e76c8fc7ffab93`
  - pinned parent SHA-256:
    `b05e4c1551dbc0a1799e96b6fd1203703628c76ab7b5faa8d398f021b9bb6865`

Both Lean files carried `PRE-VALIDATION` in the exact source compiled by Colab.
Seal checkpoint `6543e50187cc671306a0f4cda14cb1b13108df50` removes exactly
those two marks and imports the audit into `YangMillsCore`.  Post-seal static
gates passed: `LEAN_IMPORT_PREFIX_OK files=3`,
`LEAN_OVERLAY_TEXT_OK files=2`, `PRE_COUNT=0`, and `SORRY_ADMIT=0`.

## Colab result and external-process state

The single Colab Pro+ CPU/high-RAM runtime ran in account
`lluiseriksson@gmail.com` at notebook
`https://colab.research.google.com/drive/1E-XhSBNnDfZo6vUHQv8X_j_JoNhiZ7sN`.
It opened at `2026-08-23T17:27:58.644795+00:00` with 50.99 GiB RAM.  The
launcher, parent chain, source SHA, two source blob hashes, toolchain, package
pins, text gate, import gate, and cache materialization all passed.  The focal
and audit then passed:

```text
Build completed successfully (8774 jobs).
STAGE=source_flow_source_owner_bound_focal EXIT=0 SECONDS=2375.691
STAGE=source_flow_source_owner_bound_audit EXIT=0 SECONDS=14.661
'YangMills.RG.norm_cmp99SourceSeparatedSourceFlowFlatPhysicalGreenQprimeStar_pointSource_apply_siteEquiv_le_sourceOwner' depends on axioms: [propext, Classical.choice, Quot.sound]
EVIDENCE_SHA256=9f55a6ed2e76644536990c571312892d944c3f1ebe74eb74825eefdfd993a20f
EVIDENCE_ARCHIVE_SHA256=2a770cf15d9038b58077b3c69a69a17af1f6a4aa634d8ed1a5e13199a4fc5ec7
FINAL_STATUS=PASS
RUNTIME_UNASSIGN_REQUESTED=1
EVIDENCE_DOWNLOAD_REQUESTED=1
```

The runner requested runtime unassignment and evidence download after PASS.
There is no Lean/Lake process to resume and the cell must not be rerun.  The
notebook may be retained as the browser-side transcript during the account
transfer; reconnecting it is neither required nor authorized by this checkpoint.

## Exact completed commands

The running Colab queue is exactly:

```bash
lake build YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBound
lake env lean YangMills/RG/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalSourceOwnerBoundAudit.lean
```

The current gate printed `FINAL_STATUS=PASS`; focal jobs, timings, the single
axiom block, evidence-manifest SHA-256, and archive SHA-256 are recorded above.
The completed seal did exactly this:

1. removed `PRE-VALIDATION` from exactly the two C5 files;
2. added the C5 audit import to `YangMillsCore.lean`;
3. passed only the light textual guards locally;
4. committed seal `6543e50187cc671306a0f4cda14cb1b13108df50`;
5. recorded Step 8b.24/C6c.9r and Addendum 941 with exact Colab evidence and
   unchanged hard counters.

The PASS authorized only the completed C5 seal.  It did not authorize C6
promotion and did not change any hard counter.

## Prepared next work — do not promote during the handoff

These are scratch-only, statically checked drafts and are not compiler-verified:

- `tmp/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0.draft.lean`
- `tmp/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPointSourceB0Audit.draft.lean`
- `tmp/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalLocalizedFieldB0.draft.lean`
- `tmp/BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalLocalizedFieldB0Audit.draft.lean`

Their manifests are `tmp/source-flow-point-source-b0-draft-paths.txt` and
`tmp/source-flow-localized-field-b0-draft-paths.txt`.  Promote C6a only after the
C5 seal is compiler-certified and published; never stack it on unvalidated C5.
