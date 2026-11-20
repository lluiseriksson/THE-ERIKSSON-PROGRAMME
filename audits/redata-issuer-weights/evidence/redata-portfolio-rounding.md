# What the rounded portfolio totals can certify
Working supplement to the REDATA sensitivity analysis at commit 571e7dc6260709eaa28a80e6f3a7af4aa4eec36a. All quantities below are in percentage points. The inputs are the four pairs of event summaries in the versioned deposit [10.5281/zenodo.24405076](https://doi.org/10.5281/zenodo.24405076).

## When a portfolio total constrains the issuer cells
The deposited script event_study_v2.py takes a cross-sectional mean of available residuals each day, then sums over three sessions. Separately, it sums available residuals for each issuer. Write n_t for the number observed on day t and S_t for the sum of the observed residuals in percentage points. When n_t > 0 every day, the reported portfolio before rounding exceeds the arithmetic mean of stock CARs by
\[
\sum_{t=1}^3 (1/n_t-1/8)S_t .
\]
This follows by interchanging two finite sums. Complete data in those three sessions suffice for equality even if estimation-window availability varies. Missing event-day observations permit cancellation, so agreement between the printed portfolio CAR and a rounded cross-stock mean cannot establish completeness. The deposit supplies an acquisition script but does not include the underlying daily price files. The additional bounds below assume equality before rounding.

## A sharp bound on all diversified weights
Let Delta be 0.005, the half-width of an issuer cell. In the box 0.05 <= w_i <= 0.20, with eight weights summing to one, the vertices have four weights of 0.20 and four of 0.05. For any choice of rounding errors a linear objective in w has a minimum at a vertex. A global minimum over the two compact sets can therefore also be found at a vertex. The separately rounded equal-weight portfolio restricts the sum of the eight errors to [8(p-m-Delta),8(p-m+Delta)], where p is the printed portfolio and m is the arithmetic mean of the printed issuer returns. Intersect this interval with [-8 Delta,8 Delta].

To minimize a weighted event error start with all eight errors at -Delta. If the lower sum limit requires a total increment t, assign it first to the four smaller weights (capacity 0.04), then to the larger weights. The cost above -Delta is 0.05 min(t,0.04) + 0.20 max(0,t-0.04). For maximization start at +Delta and perform the corresponding reductions. An exchange from a higher to a lower weight proves optimality. This correction is identical at every vertex. The minimizer of the printed linear form therefore remains an attaining weight vector in the closed-cell model.

| Model | Mean of printed B1, B4 | Reported B1, B4 | Minimum B1 minus B4 | Minimum B1 plus B4 |
| --- | --- | --- | --- | --- |
| Market | 1.52875, 0.81375 | 1.53, 0.81 | 0.0755 | 1.4855 |
| Market and SMH | 1.6525, 0.835 | 1.65, 0.83 | 0.2290 | 1.6375 |

For the market model, minimizing B1 requires a total increment of 0.01 above the all-low assignment, while maximizing B4 requires a total reduction of 0.03 below the all-high assignment. For the two-factor model those quantities are zero and 0.04. Both B4 minima permit the all-low assignment. Combine with the four printed minima (0.0835, 1.495, 0.2370, 1.6475). The stock-only worst-case lower bounds on the differences were 0.0735 and 0.2270. The separately rounded portfolio totals improve each by precisely 0.0020 conditional on the aggregation identity. These are deterministic worst cases. Ties at rounding boundaries are included; for a specified half-open rounding convention read the entries as infima when an endpoint is excluded.

The open empirical question is whether all eight issuer residuals were observed in each of the event windows in both designs. A source with the missingness masks, or exactly reproducible source vintages, can test that assumption. Prices and inference about investor expectations are outside this supplement.
