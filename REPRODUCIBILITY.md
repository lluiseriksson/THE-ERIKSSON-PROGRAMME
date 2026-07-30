# Reproducibility — rebuilding and re-verifying the exact state

This repository is **fully pinned**: a future reader can rebuild the
exact verified state and re-run every oracle check.

## What is pinned

* **Lean toolchain** — `lean-toolchain`: `leanprover/lean4:v4.29.0-rc6`.
* **Mathlib** — pinned to an **exact commit** in two places that agree:
  * `lakefile.lean`: `require mathlib … @ "07642720480157414db592fa85b626dafb71355b"`,
  * `lake-manifest.json`: mathlib `rev` and `inputRev` both that SHA.
* **All transitive dependencies** (batteries, aesop, Qq, proofwidgets,
  importGraph, Cli, plausible, LeanSearchClient) — pinned to exact
  `rev` commits in `lake-manifest.json`. Some inherited `inputRev` fields
  still record upstream branch names such as `main`/`master`; the effective
  checkout is the fixed `rev`, which is what Lake uses to reproduce the build.

Because every dependency is pinned to a commit SHA (not a moving branch),
`lake build` reproduces the exact verified state.  Pinning Mathlib in the
lakefile (rather than `@ "master"`) means even `lake update` reproduces.
**Do not run `lake update`** unless you intend to move the pin.

## Rebuild

```sh
# 1. install the toolchain (elan reads lean-toolchain automatically)
# 2. fetch the pinned dependencies and the Mathlib build cache:
lake exe cache get        # downloads prebuilt Mathlib .olean (fast)
# 3. build the sound, self-contained verified core:
lake build YangMillsCore
```

At source checkpoint `0be45284` the literal terminal line is:

```text
Build completed successfully (8460 jobs).
```

That line records the thermodynamic-limit branch before integration.  The
merge checkpoint `71fc7701`, with `main` first parent `d370ddff` and
thermodynamic-limit second parent `8df8adc2`, was rebuilt as a single combined
core and terminated with:

```text
Build completed successfully (8463 jobs).
```

`origin/main` advanced once more to PAPER 12 v1.2 at `a00cea06` before
publication.  The final non-rebase integration checkpoint `7460e035` was
therefore rebuilt a third time; it also terminated with
`Build completed successfully (8463 jobs)`.

Both builds used the pinned Lean 4.29.0-rc6 toolchain and all nine manifest
revisions. On the ownership-mismatched Windows checkout, Git was given
`safe.directory = *` through a process-local configuration file only; no
dependency, pin, checkout, or global Git configuration was changed.

While the first merge was being published, `origin/main` advanced to
`418227b6` with the PAPER 12 v1.1 spatial-reflection corrections.  Those
commits were integrated by a second non-rebase merge at `93c8e521`.  The
combined L1+OS tree was rebuilt again and retained the same literal terminal
line:

```text
Build completed successfully (8463 jobs).
```

## Committed oracle transcripts

Full raw oracle outputs for recent checkpoints are committed under
`docs/oracle-transcripts/` with provenance headers (measured checkpoint,
toolchain, pins, script and output sha256, totals, parse convention), so
the recorded target splits can be inspected statically without a Lean
toolchain.  See ledger Addendum 479.

## Re-verify the oracle discipline (no sorry, no project axioms)

Every headline result must print exactly
`[propext, Classical.choice, Quot.sound]`.  To check a result:

```sh
# create a scratch file:
#   import YangMillsCore
#   #print axioms YangMills.RG.lattice_mass_gap_of_cluster_and_coupling
lake env lean <scratch>.lean
```

The standing oracle script is `oracle_check.lean` (covers the headline
results).  Run it with `lake env lean oracle_check.lean`.

The complete merged script was run on published `main` checkpoint
`f0720ba7` after the final 8463-job build.  The command terminated `exit 0`
after 1575.8 seconds and produced 5083 output lines.  The appended
thermodynamic-limit, integer-translation, and spatial-reflection endpoints
each reported exactly `[propext, Classical.choice, Quot.sound]`; the
pre-existing oracle body retained its previously audited standard or
axiom-free outputs.

For the lightweight CI-style source scan, run:

```sh
python scripts/check_consistency.py
```

A reachable declaration that printed any other axiom (e.g. `sorryAx`, or
a project-specific `axiom`) would violate the project's iron rules
(`CLAUDE.md`); none do.

## What "verified" means here (scope)

`lake build YangMillsCore` checks only the **sound core**
(`YangMillsCore.lean` import closure): lattice gauge theory, the Gibbs
measure, the SU(N) Haar/Schur layer, the Kotecký–Preiss cluster
expansion, the strong-coupling **area law** and **exponential clustering**
(finite-volume / fixed-lattice), and the **conditional** Bałaban-RG
infrastructure.  It deliberately **excludes** the legacy
`ClayCore/BalabanRG/**` sprawl and the vacuous `∃ m > 0` terminal chain
(see `FOUNDATIONS.md` / `CLEANUP_PLAN.md`).

**No continuum limit, no Osterwalder–Schrader/Wightman reconstruction,
no continuum mass gap** are claimed or formalized.  Distance to the Clay
Yang–Mills problem is **~0% (<0.1%)**; see `README.md` and
`HYPOTHESIS_FRONTIER.md`.
