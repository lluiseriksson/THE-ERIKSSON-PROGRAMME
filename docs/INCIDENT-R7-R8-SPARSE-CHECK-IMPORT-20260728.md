# R7/R8 sparse checker import incident (2026-07-28)

The first production invocation under the alternate Spyder Python
3.8/SymPy 1.12 runtime terminated before entering the derivation:
`derive_surface_remainder_delta0_r7_design` was not on `sys.path`.

The traceback is preserved as
`outputs/surface-r7-r8-sparse-exact-target-FAILED-IMPORT-20260728.stderr.txt`;
stdout is empty.  This is an execution-harness failure, not mathematical
evidence and not a failed target identity.

The checker now inserts its resolved `scripts/` directory before importing
the sparse engine.  Production restarts from an empty authoritative output.
No gate or manuscript claim changes.
