# Parity Barriers for Decoupling Inequalities (v4 - FINAL, submitted to viXra)

Why no comparison functional of bounded marginal order can CERTIFY uniform decoupling.

Contents: parity_barriers.tex/.pdf (4pp), ParityBarrier.lean, verify_parity.py,
LEAN-VERIFICATION-LOG.txt, and ARTIFACT-TOOLCHAIN.json.

Historical toolchain provenance: the submitted artifact's recorded Lean pass belongs to Lean
`4.30.0-rc2` with Mathlib `cd3b69baae9cd81a572a3720f2372655eca39038`.
The repository root currently pins Lean `4.29.0-rc6` with Mathlib
`07642720480157414db592fa85b626dafb71355b`.  On 2026-08-04 the exact source
blob reproduced unchanged on those root pins in an isolated Colab CPU runtime;
an explicit second command also materialized its `.olean`.  No statement or
proof edit was required, so technical migration is authorized.  See
`ARTIFACT-TOOLCHAIN.json` and `MAIN-TREE-REPRODUCTION-LOG.txt`.  The historical
record is retained because source presence alone was not proof of compatibility.

Honest scope: the parity example (even-parity set is r-wise independent but maximally coupled) is CLASSICAL - parity-check codes are the standard k-wise independence construction (Joffe 1974; Alon-Babai-Itai 1986; Alon-Goldreich-Mansour 2003) - and no priority is claimed for it. The contribution is (i) the comparison-functional formalization with an explicit CERTIFICATION condition (RHS vanishes on product measures with single-coordinate f - this closes the vacuous-bound reading), (ii) the barrier theorem, (iii) the corollary explaining the order-1 failures found in the 2602-series audit.

Machine verification: PARAMETRIC-in-r Lean theorems for all n (sum_chi_eq_zero, parity_kwise, parity_support) + the abstract certifying_barrier_schema + decide kernel instances r=1..4 + exact rational arithmetic r=1..6. Oracle: [propext, Classical.choice, Quot.sound] for every theorem; no sorry.

Review trail: v2 (internal) -> v3 (k-wise literature cited, Lean executed) -> 7.2->8.0->8.35->8.65 sibling-paper pipeline -> this paper: 8.25 -> v4 (certification condition + parametric Lean + schema) -> 8.85.
