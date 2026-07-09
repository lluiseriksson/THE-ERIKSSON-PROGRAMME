# Parity Barriers for Decoupling Inequalities (v4 - FINAL, submitted to viXra)

Why no comparison functional of bounded marginal order can CERTIFY uniform decoupling.

Contents: parity_barriers.tex/.pdf (4pp), ParityBarrier.lean, verify_parity.py, LEAN-VERIFICATION-LOG.txt.

Honest scope: the parity example (even-parity set is r-wise independent but maximally coupled) is CLASSICAL - parity-check codes are the standard k-wise independence construction (Joffe 1974; Alon-Babai-Itai 1986; Alon-Goldreich-Mansour 2003) - and no priority is claimed for it. The contribution is (i) the comparison-functional formalization with an explicit CERTIFICATION condition (RHS vanishes on product measures with single-coordinate f - this closes the vacuous-bound reading), (ii) the barrier theorem, (iii) the corollary explaining the order-1 failures found in the 2602-series audit.

Machine verification: PARAMETRIC-in-r Lean theorems for all n (sum_chi_eq_zero, parity_kwise, parity_support) + the abstract certifying_barrier_schema + decide kernel instances r=1..4 + exact rational arithmetic r=1..6. Oracle: [propext, Classical.choice, Quot.sound] for every theorem; no sorry.

Review trail: v2 (internal) -> v3 (k-wise literature cited, Lean executed) -> 7.2->8.0->8.35->8.65 sibling-paper pipeline -> this paper: 8.25 -> v4 (certification condition + parametric Lean + schema) -> 8.85.
