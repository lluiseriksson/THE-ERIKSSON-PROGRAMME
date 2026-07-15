# Independent static audit of the five-family half-line design

**Date:** 2026-07-15
**Scope:** G5, `beta>=125`, `0<=lambda<=3/2`
**Auditor:** Claude Fable 5, high effort, read-only
**Verified metadata:** `is_error=false`; `modelUsage` contains
`claude-fable-5`; no Opus fallback; session
`0dfb0e33-32aa-4c6a-92df-36c8a8537a98`.

## Verdict

`PASS_DESIGN_NOT_CERTIFIED`.

This is the auditor's static verdict only.  A subsequent clean-process
execution made upper row 74 indeterminate, so the global design-pass claim
has been withdrawn under
`incidents/INC-G5-HALFLINE-NONREPRODUCIBLE-DESIGN.md`.

The auditor independently rederived the divided-difference identity, the
five-family scaling, all four moving charts, the Bessel derivative chains,
the integral-form companions, the near- and far-tail measures and factors,
the rational exterior gap, the `delta=0` treatment, and the exact 75-box
lambda coverage.  No mathematical error was found.  The five tail budgets
were reproduced manually to three or four significant figures.

The auditor could not execute Python in its sandbox.  Consequently it did
not independently reproduce the reported worst row-63 margin.  The audit is
independent static falsification, not the required independent production
rerun.

## Findings and disposition

1. The rational sinc floor was not mechanically tied to the actual chart
   edge.  Fixed: the geometry verifier now encloses the exact sinc at
   `pi/8+shift/2` before using the `4/3` Gaussian rate.
2. The dependency ledger omitted transitive numerical modules.  Fixed: the
   cover ledger includes the hull, delta-zero geometry, centered-prefactor,
   carrier-jet, and L2-core modules.  A separate AST audit now requires the
   declared ledger to equal the exact transitive closure, so a later local
   import can neither escape the hashes nor leave a stale ledger entry.
3. The CONFIG line omitted the mixed grids.  Fixed: every mixed grid is now
   printed explicitly.
4. The Fourier oracle was not connected to a cover row by a regression.
   Fixed: `verify_surface_right_edge_five_family_cover_oracle.py` requires
   the five families, `P0`, and `H` at beta 125 and lambdas 1.26, 1.27, 1.28
   to lie inside the adversarial row-63 Arb box.
5. A divided-difference contract still said `lambda<=1`.  Fixed to
   `lambda<=3/2`.
6. The far-tail length uses a conservative factor two.  Documented: length
   `pi` is charged although the actual exterior length is `pi/2`.

## Remaining production blockers

- freeze the scripts and complete dependency closure in one commit;
- rerun all 75 rows to an immutable transcript from that commit;
- validate adjacency, modes, hashes, positive `B0`, positive `P0`, and the
  terminal worst margin;
- reproduce the production transcript in a genuinely separate execution
  role.

Until all four items pass, the half-line result remains a design theorem and
G5 remains open.
