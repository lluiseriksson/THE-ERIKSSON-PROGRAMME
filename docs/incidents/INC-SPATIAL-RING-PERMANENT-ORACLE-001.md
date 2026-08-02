# Spatial-ring permanent oracle ordering failure 001

Status: **VERIFIED failure**. The permanent repository oracle was not executed.

## Immutable inputs

- Repository SHA checked out: `d2966688d52bb0217f2165f544d0b95e5749a4d9`.
- Notebook preregistration commit: `c7d2a63c`.
- Lean: `4.29.0-rc6`, commit `00659f8e6071d7e46131ed643bf8003b99b044e9`.
- Mathlib: `07642720480157414db592fa85b626dafb71355b`.
- Isolated Google Colab high-RAM CPU runtime; no local Windows elaborator was launched.

The SHA, toolchain, and Mathlib prechecks passed.  The official cache was
obtained in the isolated runtime and `lake build YangMills.OS.SpatialRing`
returned exit 0.

## Failed command

```text
lake env lean /tmp/spatial-ring-sector-348y54yc/repo/oracle_check.lean
```

Lean exited 1 with:

```text
error: unknown module prefix 'YangMillsCore'
No directory 'YangMillsCore' or file 'YangMillsCore.olean' in the search path
```

The root oracle imports `YangMillsCore`, whereas the notebook ordered the root
oracle before `lake build YangMillsCore`.  Therefore the failure is a verifier
dependency-order defect, not a declaration, axiom, or theorem failure.  The
consistency judge, core build, archive, and PASS marker did not run in this
attempt.

## Bounded correction

The notebook will run and capture `lake build YangMillsCore` before executing
the permanent oracle, then run the 24-marker check and consistency judge.  The
core command will not be duplicated.  The target repository SHA, source,
toolchain, Mathlib pin, allowed axiom set, and declaration list remain unchanged.
