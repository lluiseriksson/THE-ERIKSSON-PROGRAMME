# Parity Barriers for Decoupling Inequalities (v3)

Why no comparison functional of bounded marginal order can certify uniform decoupling.

Honest scope: the parity example (even-parity set is r-wise independent but maximally coupled) is CLASSICAL - parity-check codes are the standard k-wise independence construction (Joffe 1974; Alon-Babai-Itai 1986; Alon-Goldreich-Mansour 2003) - and no priority is claimed for it. The contribution is the comparison-functional formalization, the barrier theorem, and the corollary explaining the order-1 failures found in the 2602-series audit.

Contents: parity_barriers.tex/.pdf (4pp), ParityBarrier.lean (decide proofs r=1..4, oracle = 3 standard axioms, see LEAN-VERIFICATION-LOG.txt), verify_parity.py (exact rational r=1..6).

Review trail: v2 (internal) -> v3 2026-07-09: k-wise literature cited, Lean claims made consistent and actually executed, framing corrected.
