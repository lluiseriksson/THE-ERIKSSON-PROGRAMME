# A marginal net seller can invalidate the zero-price prediction in a consignment auction

## Model and claim tested

Consider a one-shot auction with divisible supply m, two bidders, constant marginal values v1 > v2 > 0, and one nonnegative bid per bidder for her entire capacity qi. Assume 0 < qi < m and q1 + q2 > m. An initial endowment ei is consigned, 0 ≤ ei < qi and e1 + e2 ≤ m. The last accepted bid sets the common price p. Payoff from allocation x is vi x + (ei − x)p. The lower bidder receives ri = m − qj, the higher bidder receives qi. Write d = q1 + q2 − m, so qi − ri = d. Both receive positive quantities. A tie rule is needed only for the positive equilibrium below.

Section 3, step [2-1] of Kiho Yoon's July v1 predicts a zero price in the family below. The author withdrew the paper in November after identifying an error in that section. The withdrawal does not identify an example or establish which step was responsible. This note supplies a direct test of the stated rule. [Original model and algorithm](https://arxiv.org/html/2607.03648v1) · [Withdrawal](https://arxiv.org/abs/2607.03648v2)

## Strict counterexample

Take m = 10, (q1,q2) = (8,6), (v1,v2) = (10,4), and (e1,e2) = (1,3). Both endowments are positive, less than capacity, and together account for four units. The first-round uncapped thresholds of v1 equation (1) are 40/7 and 16/3. After the value cap the thresholds are 40/7 and 4. Bidder 2 uniquely attains the minimum through the cap. Because q1 < m, case [2-1] prescribes b2 = 0, b1 ≥ 4 and allocation (8,2).

Bidder 2 can bid 1. At every prescribed b1, bids are strictly ordered before and after. The allocation is still (8,2). The last accepted bid goes from 0 to 1. Bidder 2's gross consumption value is 8 in both cases. Her payment changes from 0 to 2 and her consignment proceeds from 0 to 3. Her net payoff rises from 8 to 9. Neither the tie convention nor the admissibility of bids above value matters.

Even other bids cannot implement the predicted allocation and price as a pure equilibrium in this example. If b1 > 0 the marginal bidder must bid zero and can raise by any amount below both b1 and v2. If both bid zero and the tie awards bidder 2 only two units, she can take six by bidding 1 and still pay zero per unit, since bidder 1 also wins. Her payoff becomes 24.

## An open family and a replacement equilibrium

Assume e1 < r1, e2 > r2 and T1 = d v1/(q1 − e1) > v2. Then the first uncapped threshold is T1 and the second is d v2/(q2 − e2) > v2. Also T1 < v1. The same branch therefore stops with b1 ≥ v2 and b2 = 0. Raising the lower bid to any t strictly between 0 and v2 produces a gain (e2 − r2)t with no change in allocation. All strict inequalities persist under small changes in the example's parameters.

Give bidder 1 priority at an exact tie, consistent with the higher-priority allocation convention for a limiting pair of bids. At (v2,v2) allocations are (q1,r2) and price is v2. If bidder 2 undercuts to t < v2 her payoff falls by (e2 − r2)(v2 − t). If she jumps above v2, the price stays at v2, so the additional d units have zero net value. Bidder 1 gains nothing from raising. If she undercuts to t < v2 her payoff is r1 v1 + (e1 − r1)t ≤ r1 v1. Her current payoff exceeds that bound by d v1 − (q1 − e1)v2 > 0. These cases prove pure Nash equilibrium even when overbids are allowed.

If bids are additionally bounded by the bidders' respective values, the equilibrium *outcome* is unique for the stated tie rule. With b1 > b2 and b2 < v2, bidder 2 can increase her bid strictly below b1. At b1 > b2 = v2, bidder 2 already bids her cap. The complete set under the value caps is (b1,v2) with v2 ≤ b1 ≤ v1. For any such pair the preceding undercut bound still applies to bidder 1, and bidder 2 can only lower her payoff by shading. If b1 < b2 ≤ v2, bidder 1 can overtake legally, obtain q1 and pay b2. This gives at least q1 v1 − (q1 − e1)v2 > r1 v1, an upper bound on her old payoff. Finally at any tie p < v2, bidder 2 can jump above p and acquire d further units at p, gaining d(v2 − p). This exhausts all cases. Without the cap the positive equilibrium proved above still exists; uniqueness is not asserted.

Numerically, the positive equilibrium keeps the same allocation and changes regulator revenue from the predicted 0 to (10 − 1 − 3) × 4 = 24. This concerns a model comparison with fixed primitives, not an estimate for an operating permits market.

## Relation to previous work

The incentive to raise consignment proceeds is known. For example, Liu and coauthors study strategic demand in a divisible auction with bid functions. Our limited contribution is the explicit failure of the withdrawn step under its single-bid rules, a family defined by strict inequalities, and an exact pure-equilibrium description for that family with value caps and specified priority. We have not established priority for the equilibrium description. [Consignment Auctions Revisited](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=3573819)

