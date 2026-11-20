# An expanding band at the full-success endpoint

Let \(f=mn-k\) be the total failures on a full stratum. In the common-cap independent experiment of profile-transport.md, the stratum deficit is nonnegative throughout an expanding upper band. For \(n\ge3,\ f\ge n,\ k\ge m\), sufficient integer conditions are
\[
 m\ \ge\ 2 f^2,\qquad
 m\ \ge\ 2 f^n [n(f+2)]^{2(n-2)}(n+1)^{2n}.
\]
For each fixed common cap \(n\ge3\) these include all \(f\le c_n m^{1/(3n-4)}\) for a suitable positive constant and sufficiently large \(m\). If \(f<n\) the score equals one on the stratum. At cap two all strata already satisfy the comparison. The estimate is a sufficient band and does not claim sharp constants or an optimal growth exponent.

**Proof.** In failure odds, each unordered failure profile \(y\) represents \(N_y=d_y\prod_i\binom{n}{y_i}\) labelled outcomes, with \(d_y\) the number of distinct permutations. Each exhausted-task orbit supplies \(N_y\), and every all-hit orbit demands the total of \(w_s-1\) over its paths. Since \(m\ge f\), \(B=(1,\ldots,1,0,\ldots,0)\) with \(f\) ones is a least profile for majorization. Any remaining supply can go there. We construct a transfer paying for all other demand first.

For \(s\le f\), a uniform unrestricted weak composition of \(s\) into \(m\) parts has probability at most \(m(f/m)^n\) that some part reaches \(n\). Indeed the probability for a fixed part is zero when \(s<n\) and otherwise equals \((s)_n/(m+s-1)_n\le(f/m)^n\). This upper bound is at most \(1/2\) since \(n\ge2,\ m\ge2 f^2\). As \(w_s\) is the reciprocal of the cap-compliance probability, the demand \(D_y\) of any all-hit orbit satisfies \(D_y\le 2f^n m^{1-n}N_y\).

For every nonbalanced all-hit profile, take a largest entry \(t\ge2\) and move one failure at a time from other positive entries into that entry until it equals \(n\). The total \(f\ge n\) ensures completion. Fix a deterministic choice among donor values, for example the smallest available positive value. This makes the assigned exhausted profile \(x\) a function of \(y\); it majorizes \(y\). There are \(u=n-t\le n-2\) moves. If \(j,b\) are the numbers of nonzero entries before and after, at most \(u\) slots disappear, so \(j-b\le n-2\).

We bound the loss of orbit multiplicity. In one move from donor \(a\) to recipient \(t'\), the ratio of old to new products of binomial factors is at most \(n^2\). For permutation multiplicities this ratio is the product of the new frequency factorials divided by the old ones. After removing both old entries, insert their new values. Removal costs at most one per removed unit in this ratio. Each insertion of a positive value costs at most \(f+2\), and each insertion of zero costs at most \(m\). A zero is inserted exactly when a donor disappears. Multiplication across all moves proves
\[
 N_y/N_x\le m^{j-b}[n(f+2)]^{2u}.
\]
A given \(x\) has at most \((n+1)^{2n}\) possible assigned predecessors: for each of at most \(n-2\) reverse moves it is enough to specify the two entry values, giving at most \(\sum_{u=0}^{n-2}(n+1)^{2u}\) different paths of all lengths. Thus the sum of assigned demands for this \(x\) is at most
\[
 N_x\,\frac{2f^n[n(f+2)]^{2(n-2)}(n+1)^{2n}}m .
\]
The hypothesis makes this at most \(N_x\). Match each nonbalanced demand to its assigned source and send all leftover supply to \(B\); supply equals demand by homogeneous calibration. Each edge respects majorization, so the result holds on the full probability cube as in profile-transport.md. Finally \(f+2\le 3f\) for \(f\ge1\); the displayed sufficient bound has degree \(3n-4\) in \(f\) at fixed \(n\).

**Scope.** The proof is analytic and concerns the coefficient for a fixed total count. It complements the lower band around \(k=m\). The middle strata and the sign after arbitrary heterogeneous averaging across all strata are not resolved by the two bands.
