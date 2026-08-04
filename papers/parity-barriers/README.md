# Parity Barriers for Decoupling Inequalities (v4 - FINAL, submitted to viXra)

Why no comparison functional of bounded marginal order can CERTIFY uniform decoupling.

Contents: parity_barriers.tex/.pdf (4pp), ParityBarrier.lean, verify_parity.py,
LEAN-VERIFICATION-LOG.txt, and ARTIFACT-TOOLCHAIN.json.

Toolchain quarantine: the recorded Lean pass belongs only to Lean
`4.30.0-rc2` with Mathlib `cd3b69baae9cd81a572a3720f2372655eca39038`.
The repository root currently pins Lean `4.29.0-rc6` with Mathlib
`07642720480157414db592fa85b626dafb71355b`.  The source has not been
reproduced on that root pin, and its presence is not evidence of a materialized
`.olean`.  See `ARTIFACT-TOOLCHAIN.json`; migration remains unauthorized until
the frozen source blob passes on the root pins without a statement change.

Honest scope: the parity example (even-parity set is r-wise independent but maximally coupled) is CLASSICAL - parity-check codes are the standard k-wise independence construction (Joffe 1974; Alon-Babai-Itai 1986; Alon-Goldreich-Mansour 2003) - and no priority is claimed for it. The contribution is (i) the comparison-functional formalization with an explicit CERTIFICATION condition (RHS vanishes on product measures with single-coordinate f - this closes the vacuous-bound reading), (ii) the barrier theorem, (iii) the corollary explaining the order-1 failures found in the 2602-series audit.

Machine verification: PARAMETRIC-in-r Lean theorems for all n (sum_chi_eq_zero, parity_kwise, parity_support) + the abstract certifying_barrier_schema + decide kernel instances r=1..4 + exact rational arithmetic r=1..6. Oracle: [propext, Classical.choice, Quot.sound] for every theorem; no sorry.

Review trail: v2 (internal) -> v3 (k-wise literature cited, Lean executed) -> 7.2->8.0->8.35->8.65 sibling-paper pipeline -> this paper: 8.25 -> v4 (certification condition + parametric Lean + schema) -> 8.85.
