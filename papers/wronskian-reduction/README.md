# A Wronskian Identity for Antisymmetrized Sine Sums (paper 4, v1)

The surface-positivity double sum collapses EXACTLY to a Wronskian: W(t) = 2[F_A'(t)F_B(t) - F_A(t)F_B'(t)], F_X(t) = Sum X_m sin(mt). Two-line proof (product-to-sum + antisymmetrization).

Consequences: (1) the open asterisk is equivalent to GLOBAL sine-series ratio monotonicity on (0,pi) (numerics: all beta tested); (2) hand-checkable counterexample - a=(3,4,3), b=(3,2,1), phi=(1,2,3) increasing, b decreasing (F_b>0 by Fejer-Gronwall), Wronskian(2pi/3) = 3sqrt(3)/2 > 0 - so NO Biernacki-Krzyz analogue for sine series: coefficient-ratio monotonicity cannot certify the sign; (3) precise global Conjecture + the promising route (kernel/integral representations of F_A, F_B).

Verification: sympy symbolic K<=5, exact rational K=7, mpmath K=90 vs direct sum; counterexample values exact algebraic. Lean formalization of the identity = declared target of the satellite, NOT claimed.

Companions: papers/phi-lemma (c_mn<0), papers/bessel-amos-fh, papers/parity-barriers; attack log docs/BF2-ATTACK-NOTES.md.

v2 (8.55/10 review applied): Conjecture equivalence correctly conditioned on F_B>0; Bessel-array summability made explicit (DLMF 10.41.1); and the identity is now MACHINE-CHECKED - WronskianIdentity.lean proves bracket_eq_two_G, double_sum_eq_wronskian, pair_sum_eq_double_sum and wronskian_identity (finite form, arbitrary K), oracle standard x4, no sorry (see LEAN-VERIFICATION-LOG.txt).
