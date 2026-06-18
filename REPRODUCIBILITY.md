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

Expected: `Build completed successfully (8263 jobs).` (the job count is
recorded in `CLAUDE.md` rule 7 and updated on every core change).

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
