# R7/R8 sparse exact target check — preregistration (2026-07-28)

The expression-level checker was nonterminal.  This replacement check uses
the pre-existing sparse coefficient-list engine
`derive_surface_remainder_delta0_r7_design.py`; it does not claim algorithmic
independence from that engine.

Acceptance requires:

- exact `B(0)=0` inside the derivation;
- exact equality of all eight returned coefficients with the targets
  preregistered in
  `SURFACE-REMAINDER-R7-R8-EXACT-HEAD-PREREG-20260728.md`;
- no SymPy `Float` in any coefficient;
- production and replay with identical `Y0,...,Y7` lines;
- full script, dependency, Python, SymPy, and Git provenance.

A pass promotes the formulas only to **single-engine exact / replayed**.
Independent numerical corroboration at `t=2.9` remains mandatory before the
degree-eight circle result is used in the K2 budget.  True companions,
exterior, K2, and the manuscript remain open.

## Result

Production and replay under Python 3.8.10 / SymPy 1.12 each print exactly
eight exact heads and terminate
`R7/R8 SPARSE EXACT TARGET CHECK PASS`.  Both stderr files are empty and the
stdout files are byte-identical, with SHA-256

```text
C8C646B210CBA59616C077022D57D886F47EA7202A136564B72A576E6E378DCF
```

The result has exactly the preregistered status: single-engine exact and
replayed.  Independent numerical corroboration and every K2 error patch
remain open.
