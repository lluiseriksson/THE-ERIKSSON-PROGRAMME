# Worst growth over every normalized diagonal error box

This supplement to the fixed 48-product scheme study concerns independent errors in nine log scales. It uses the same balanced center, coefficient file and fourth-coordinate normalization as the manuscript at commit 876f0c7c. The error variables range from −log(t) to log(t), where t ≥ 1. This is a deterministic worst-case model of scale choice. It does not model a distribution of machine roundoff or changes to the decomposition.

Convexity of each of the 16 output sums implies that the maximum over the box is attained at a vertex. Index the 512 vertices by the lexicographic order of their nine signs, with minus first and the three X signs followed by three Y and three Z signs. The fourth coordinate of each block is zero. A profile has index 512 times the zero-based output number plus the vertex index. Its value equals a polynomial of degree at most twelve divided by t⁶. Coefficients belong to the real field Q(√955614).

| Range of t | Maximizing profile | Output (one-based row, column) |
|---|---:|---|
| 1 < t < t₁ | 2420 | (2,1) |
| t₁ < t < t₂ | 2922 | (2,2) |
| t₂ < t < t₃ | 2898 | (2,2) |
| t > t₃ | 4532 | (3,1) |

The transition factors are approximately 1.329115585564, 1.329118118163 and 4.554338481285. At each transition the neighboring profiles tie. All profiles coincide at t=1. The two profiles with output (2,2) correspond to different perturbations. The first of those perturbations wins on a window only about 0.000002533 wide. Another pair of polynomials crosses inside that window, below the maximum. Counting every polynomial root as a change of the worst perturbation would give an incorrect result.

**Certificate.** From each nonzero product of factor coefficients form the signed exponent vector of its diagonal scaling. At a vertex its dot product with the sign vector is an integer between −6 and 6. Multiply each profile by t⁶, and tabulate rational and radical parts over a common positive denominator. For a finite interval with endpoints p/q and r/s, the substitution t=(p+rz)/(q+sz), z>0, followed by multiplication by (q+sz)¹² preserves the sign of a difference. For the last interval use r=1 and s=0. Nonnegative coefficients, at least one positive, certify strict dominance on the interior. Exact endpoint evaluations cover the subdivision boundaries.

Where this comparison leaves competing polynomials, the signs of their transformed coefficients bound the number of positive roots by Descartes' rule. One sign variation with opposite endpoint behavior gives exactly one interior root. Rational bisection with exact quadratic-field comparisons isolates it. The four pairwise crossings, including the inactive crossing, their isolating endpoints, the subdivision tests and the surviving polynomials are in `polish.json`. Its `unresolved` field records intervals from the **initial dominance pass**; the subsequent `events` list resolves those intervals.

**Reproduction.** Use normal Python 3 with NumPy and SymPy. The scripts use assertions and require optimization to be disabled. Place the coefficient file identified by the parent study's `sources.json` in the working directory under the name `scheme.json`. The SHA-256 is b82a3cef30dacb9ee08be73d13449123bb073716888a081d52bfae0a0205b4ee. Run `python3 radii_polish.py` and compare the decoded JSON with `polish.json`. With that certificate present, `python3 check_radius_direct.py` separately evaluates the original factor norms at eight rational scales. It uses rational interval bounds for the balanced basis and compares all 8,192 output/vertex combinations at each scale. Its strict lower bounds on winner separation are in `direct.json`.

Chen's [construction and qualitative orbit certificate](https://github.com/jeffchen006/tensor-rank-4x4/blob/822b2281116ae29b0ca3b947dfa4544b69258c0e/agents/hmz20-B2/ORBIT_CERTIFICATE.md) supply the underlying scheme and balanced optimum. The box envelope and transition tests are supplementary computations. The PDF assessment attached to the earlier manuscript applies to that PDF.