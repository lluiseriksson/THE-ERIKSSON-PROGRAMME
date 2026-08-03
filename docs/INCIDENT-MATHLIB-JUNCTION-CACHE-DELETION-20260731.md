# Mathlib junction cache deletion (2026-07-31)

**Status:** `INFRASTRUCTURE INCIDENT; RECOVERED; RULE ADOPTED`

This is an operational incident record.  It makes no mathematical claim and
does not certify any Lean result.

## Evidence classes

The measurements below were reported from the incident while recovery was in
progress.  No command transcript or filesystem snapshot of the damaged state
is versioned in this repository.  They are therefore **incident measurements
as reported**, not measurements independently reproduced by this note.

The causal account is a **post-incident reconstruction** from the reported
filesystem layout and cleanup action.  It is not presented as an exact shell
transcript.

## Measured state, as reported

- A worktree shared `.lake/packages` with the principal clone through a
  Windows directory junction.
- After cleanup, the principal clone's cache contained one package and zero
  `.olean` files.
- The destroyed cache had been measured at 7.2 GB and 7,788 `.olean` files.
- The two mornings lost during the week's combined audit and infrastructure
  incidents are an aggregate cost.  This cache deletion contributed to that
  cost; this note does not attribute both mornings to this incident alone.

## Causal reconstruction

The reported cleanup used `Remove-Item -Recurse` on the worktree side of the
junction.  The reconstructed mechanism is that recursive removal traversed
the junction and deleted the contents of its target, the principal clone's
`.lake/packages` directory.  That account explains the shared timing and the
observed empty cache, but it remains causal inference because the destructive
command and pre/post directory listings were not preserved as a versioned
transcript.

## Recovery, as reported

`C:\Users\lluis\.cache\mathlib` still held the `.ltar` archives.  Running
`lake exe cache get` reconstructed the local cache from those surviving
archives, without downloading the Mathlib cache again from the network.
Recovery does not retroactively certify the unversioned measurements above.

## Rule bought by the incident

Between worktrees, copy `.lake/packages` with `robocopy`; never share it through
a junction.

If a junction already exists, first identify the exact link path and remove
only the link with:

```bat
cmd /c rmdir <link>
```

Do not add `/s`.  Never remove a junction with `Remove-Item -Recurse`.

This rule is incorporated into the repository-wide
[Operational Governance Charter](OPERATIONAL-GOVERNANCE-CHARTER.md#1-worktree-cache-isolation).
