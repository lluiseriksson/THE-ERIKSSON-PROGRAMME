# What survives when some triples are forbidden?

Supplementary proof and exact witness for the balanced-subset theorem. Same research record as the parent manuscript and its full-support supplement. This note was written after those PDFs and is outside their assessments.

The coefficient formula for forward KL survives on the support of a balanced target P with zeros. Its implication from zero coefficient to exact sampling does not. Here balance is relative to all k-subsets of a d-item catalog, including those given probability zero. The proposal remains uniform and the sampler redraws a pool if it contains no supported k-subset.

## Extension of the limit

Use the full-support supplement's notation and condition first on the permutation-invariant event E that the pool has at least k distinct labels. Let F be actual target success. Fix any positive target set S0. Missing one of its items has probability at most k(1-1/d)^N, so Pr(F^c|E) is exponentially small for fixed d,k. The exact exchangeable identity E_E[y_S x]=lambda_N h_S uses only the event E, and is unchanged.

For a supported S the ratio y_S/(1+x) on F is at most 1/P(S), since P(S) times that ratio is a conditional probability. Set it to zero off F. To compute the marginal, divide its conditional-on-E expectation by Pr(F|E). Expand 1/(1+x)=1-x+x²/(1+x) on F. Both y_S and x are globally bounded on E. In the first two terms adding the omitted event F^c changes the expectation only exponentially. The last term times y_S is bounded on F by max |h|²/P(S). On the fixed high-probability neighborhood max |delta_i|<=1/2, F holds, 1+x tends to one and the uniform-integrability argument from the supplement applies. Thus for every supported S the limit remains N^k(Q_N(S)/P(S)-1) -> (d^k/M)(E_U h²-h_S). The forward KL limit remains (d^k/M)^2 Var_P(h)/2 because both laws live on the target support.

If P is uniform on a proper balanced support, h is constant P-almost surely. The coefficient vanishes, giving KL=o(N^(-2k)). This is a statement about the limiting rate. Exactness for each N is a stronger requirement.

## Finite counterexample

Use residues 0,...,8 modulo 9. The 36 supported triples are all cyclic translates of {0,1,2}, {0,1,4}, {0,2,5}, {0,2,6}. Each of the 36 pairs occurs in exactly three supported triples. Give every supported triple mass 1/36. Thus the inclusion balance holds at order two and Var_P(h)=0.

With four independent uniform candidates, 4,320 of the 6,561 ordered pools contain a supported triple. Redraw the rest. Each triple T receives weight 36 from pools with a repeated label, since the repeated label may be any of its three labels and there are twelve orders. A four-distinct window W containing T adds 24/m(W), where m(W) is the number of supported triples in W. Dividing these total weights by 4,320 yields two marginal probabilities, 29/1080 and 31/1080, straddling the target 30/1080. The checker independently enumerates all ordered pools, samples by supported occurrence triples, and compares every probability with the window calculation. This resolves the necessity of full support for the exactness characterization in the full class of subset laws. The example is not asserted to have a determinantal representation.

Source and machine-readable witness accompany this note. No result about actual model-generated interview questions, clinical decisions or other deployed tasks follows from this example.
