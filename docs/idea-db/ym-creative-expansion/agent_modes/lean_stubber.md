# Agent mode: Lean Stubber

Mission: turn formula cards into small compilable Lean files outside `YangMillsCore`.

Output constraints:
- Use a namespace like `YangMills.RG.CreativeExpansion` or `Scratch`.
- Avoid imports that trigger the full expensive core unless needed.
- Prefer finite `Finset` lemmas, inequalities, and records.
- Every theorem should be either fully proved or explicitly left out as a commented target.
- Do not add `axiom`, `sorry`, or project-level global assumptions.

High-value first stubs:
- three-part activity budget;
- fixed-target fiber sum equality;
- metric-stitching exponent extraction;
- boolean admissibility automaton;
- non-vacuity witness for source-package hypotheses.
