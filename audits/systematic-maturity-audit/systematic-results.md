# How many industrial pilots could a systematic audit miss?

In the archived review of AI in mechanical product development, 160 primary studies were coded and a second rater evaluated 60. We call a rating positive when it is “Industrial pilot” or “Operational deployment”. All statements below concern that classification. They do not establish actual industrial use. Source: [versioned review files](https://doi.org/10.5281/zenodo.24095165).

## Reconstructing the denominator

Of the 160 studies, 16 single-stage studies had been adjudicated earlier and lay outside the blind audit frame. Among the remaining 144, sample A drew 32 of 127 single-stage studies and eight of 16 multi-stage studies using stratified systematic selection with a random start. The single closed-loop study was included in purposive sample B, along with the eight remaining multi-stage studies and the 11 highest-priority remaining single-stage studies. The weights therefore represent 143 studies. For the 16 multi-stage studies we have a census: two positives in A and one in B. The closed-loop study received a negative maturity rating. All 43 audited single-stage studies received negative ratings. Here “negative” includes an unreported maturity level.

Fix the observed ratings and let missing second-rater labels vary freely. The possible positive totals are every integer from 3 to 103. Substituting the second rater's decisions on the 60 observed rows yields seven positives when published codes are retained elsewhere. Four of the other 100 studies have positive published codes and 96 have other codes. Under a budget of at most b changes outside the audit the exact interval is [7−min(b,4), 7+min(b,96)]. A strict majority requires 74 changes from that baseline. If subsequent blind checks return only negative ratings on distinct, previously unobserved studies, 23 such checks are necessary and sufficient to exclude a strict majority without assumptions about sampling.

## Sharp miss probability under a specified systematic design

Consider a fixed ordered frame with N units, sample size n, and uniform random start U on [0,N/n). Sample positions floor(U+jN/n) for j=0,…,n−1. Set g=gcd(N,n), L=N/g and d=n/g. If m≥1 units are positive, the maximum over all arrangements of those units of the probability of observing zero positives is

    max(0, L − d − ceil(m/g) + 1) / L.

For m=0 the probability is one. To see this, write s=floor(nU), uniform on 0,…,N−1. Unit i is selected for the n consecutive phases starting at i·n modulo N. After collapsing phases into groups of g consecutive residues, this is a length-d interval of the L-cycle. Each interval origin is represented by exactly g units. The m positives therefore occupy at least k=ceil(m/g) distinct origins. Extending a nonempty proper subset of a cycle by its unit shift adds at least one point. After d−1 extensions the covered phase union has size at least min(L,k+d−1). Consecutive origins realize equality. Fill up to g units per origin to construct an extremal placement for every m. This is an order-free worst case. The archive's design note specifies systematic selection with random start but does not establish this exact phase implementation or the historical order used to draw the sample.

For N=127 and n=32, a zero count on the 32 alone allows an order-free upper limit of 89 positives at one-sided 95% confidence under this design. A total of 89 has miss probability 7/127; 90 has miss probability 6/127. The 11 additional observed negatives already give the stronger deterministic cap of 84. That extremal population can jointly produce zero positives in A and in all 11 priority follow-ups on 12 of the 127 starts when the 43 negatives have highest priority. This is a constructed frame and priority ordering, not the review's recovered order.

A strict majority of the 160 requires at least 62 positives in the 127-unit stratum even if all 16 outside-frame studies are positive. A single start can miss all 62 with probability 34/127. Under a prespecified plan of r independent starts on the same ordered frame, the sharp probability of all zeros is its r-th power: two starts still exceed 5%, three fall below 5%. A prospective plan conceived after observing an initial zero should distinguish fresh draws from a precommitted sequence.

The archived systematic design does not justify substitution of simple random sampling without replacement on the basis of weights alone. Lillian H. Madow studied the distinction between designs in 1946, and the coverage formula here is an elementary cyclic-interval result. No priority claim about systematic sampling in general is made. [Primary methodological reference](https://doi.org/10.1080/01621459.1946.10501864).

## Reproduction

Run mechanical-bounds.py and mechanical-strata.py with fuente.json in the working directory and openpyxl 3.1.5. They verify the workbook checksum, compare the master and audit rows, and expose the design notes. The hypergeometric candidate in mechanical-strata.py is retained as a failed design model and must not be interpreted as a confidence limit for the review. Run systematic-zero.py with standard Python to enumerate every marked subset for N≤12, to verify extremal placements for every m in the 127-unit case, and to check the finite example with priority follow-ups.
