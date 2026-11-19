# Failure of both auxiliary critical controls, with an exponentially recovering spectrum

This follow-up concerns the single open question at p = 15/7. It is outside the frozen working paper and its assessment.

Fix p = 15/7. Let M = 2^m, r = M-1 and L = 2r. Form a binary m by L matrix A whose columns list every nonzero binary m-vector twice. The two lists supply disjoint full column bases. The map onto the syndrome group sends uniform measure to uniform measure. Every nonconstant syndrome character pulls back to a Walsh character of weight exactly M, because half of all m-vectors pair to one with any fixed nonzero character. Consequently the ambient noise P of correlation 1/2 acts on every syndrome potential H by the exact formula PH = a + t(H-a), where a is the uniform mean of H and t = 2^(-M).

Take H equal to exp(-M) on half the syndromes, M^(1/p) on one of the remaining syndromes and 1 elsewhere. Its mean tends to 1/2. Its p-th moment stays bounded, hence so does its second moment. Set G = PH and Z = E(HG) = a^2 + t Var(H). Then G converges uniformly to a at rate O(t M^(1/p)), and the stationary density pi = HG/Z is uniformly comparable to H. In particular pi matches all ambient marginals through degree M-1, has bounded p-th moment and its uniform mean logarithm tends to minus infinity. Its p-th powers are not uniformly integrable: the unique high syndrome has uniform mass 1/M and contributes a quantity bounded below by a fixed positive constant to the p-th moment. Both failures hold in the same sequence, although its matching order is asymptotic to L/2.

The complete spectrum in this example recovers exponentially. Write U = H/G and Q = P_(1/sqrt(2)). Uniformly,
|U-pi| = H |Z-G^2|/(G Z) = O(t M^(2/p)).
This bound uses the lower bound on a and G, the bounded variance of H and the exact expression for Z. Also ||pi-1||_infinity = O(M^(1/p)). Let D be the projection onto degrees at most d = floor((M-1)/2). Every product of two Walsh characters in that subspace has degree at most 2d < M, hence D M_(pi-1) D = 0. On its orthogonal complement Q has norm 2^(-(d+1)/2). Expanding with these two projections bounds ||Q M_(pi-1) Q|| by 3 ||pi-1||_infinity 2^(-(d+1)/2). Together the two estimates show that ||Q M_U Q - P|| is exponentially small in L. The reversible conjugate of the Doob kernel and Q M_U Q have the same eigenvalues by the two Gram products, so min-max proves the ordered recovery.

The construction disproves the deduction of either auxiliary hypothesis in critical-order-followup.md from bounded critical moment and linear-degree matching. It does not supply a counterexample to recovery at equality: both conclusions about its spectrum go in the recovering direction. Its simple syndrome law displays why controlling a global logarithmic mean can lose the information supplied by noise smoothing. The remaining question is whether the actual, localized exceptional quadratic form can persist at critical order. This is an analytic argument, without a Lean check or a separate literature-wide originality claim.


The binary simplex generator is classical. See [On some batch code properties of the simplex code](https://arxiv.org/abs/2110.07421).
