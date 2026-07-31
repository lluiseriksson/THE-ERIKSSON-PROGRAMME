# Canonical project state

`project-state.json` records the small set of stable, machine-checkable facts that were
previously repeated across several status documents:

- the Lean source checkpoint supporting the recorded build/oracle pair;
- the pinned Lean toolchain and Mathlib commit;
- the build checkpoint, oracle checkpoint, their source-identical relation,
  the recorded build size, and their ledger;
- the standard axiom oracle;
- the live theorem-hypothesis frontier;
- the unchanged continuum boundary.

It deliberately does **not** record the current repository HEAD. A file cannot contain the
hash of the commit that contains itself without a circular update. Instead,
`lean_core.source_checkpoint` is required to exist and be an ancestor of the checkout.

It also excludes architectural completion percentages and the active Surface Theorem desk.
Percentages are editorial judgments, not mechanically derivable facts. The paper track has
its own acta and must not be overwritten by the Part II control plane.

Validate the file with:

```powershell
python scripts/validate_project_state.py
```

The validator compares the state against `lean-toolchain`, `lakefile.lean`,
`lake-manifest.json`, Git history, and the named evidence files. Updating prose documents
from this file is a separately reviewed step.  The current canonical pair is
the **8463-job build at `7460e035`** and the subsequent complete oracle at
`f0720ba7`.  The child changes documentation only, so it inherits the same Lean
source graph; it does not retroactively relocate the build transcript.  Both
records are in `docs/VERIFICATION-LEDGER.md`.
