# What first-hit records identify under finite-bank sampling

The [EvalPerf replay](evalperf-replay.md) compares two quantities for a fixed panel. The full target is the chance of at least one hit per task **on average across the panel** (at least $m$ hits in total for $m$ tasks). The reported statistic sees a task only until its first hit. Here we quantify the effect of drawing distinct candidates, construct a finite bank on which the usual score errs in the opposite direction, and give a design-unbiased alternative from exactly the same observations.

## How much can drawing distinct candidates change the comparison?

Consider a task with $c$ passing candidates in a bank of size $D$, $q=D-c$, and at most $n\le D$ draws. With $0<c<D$, the ratio of probabilities of seeing the first hit immediately after $\ell$ misses, without versus with replacement, is
\[
r_\ell=\frac{(q)_\ell c}{(D)_{\ell+1}}\frac{D^{\ell+1}}{q^\ell c}
\le \left(\frac{D}{D-1}\right)^\ell .
\]
Parenthesized subscripts denote falling factorials. At feasible lags the successive multiplier is $D(q-\ell)/[q(D-1-\ell)]$, which is increasing in $q$ and at most $D/(D-1)$ since $q\le D-1$. Impossible lags have ratio zero. Equality holds at every lag for a bank with a single pass. A perfect bank always hits immediately under both designs.

For two attempts the first-hit ratios are exactly 1 and $D/(D-1)$ for all mixed banks. Consequently any **nonnegative** score supported on seeing a hit in every task has mean under distinct draws between its with-replacement mean and $(D/(D-1))^h$ times that mean, where $h$ is the number of mixed tasks and tasks are sampled independently. For the full record of two binary outcomes the mixed outcome pairs have the same upper ratio. The two equal-outcome pairs have ratio at most one (drawing the same label a second time is less likely after removing a candidate of that label). The full probability of any event, including missing the panel target, therefore has the same multiplicative upper bound, without a corresponding universal lower bound.

On the 118-task EvalPerf panel, $D=h=100$ and $(100/99)^{100}<3$. The with-replacement calculation alone then gives a distinct-draw mean stopped score below $4.13\times10^{-13}$ and full miss probability below $3.96\times10^{-27}$. Thus even these conservative bounds put the **full success probability divided by the expected score** above $2.4\times10^{12}$. Direct calculation gives approximately $5.56\times10^{12}$. The full miss probability and the score are not estimates of the same event. These calculations concern the stated retrospective randomization.

## A finite bank with bias of the opposite sign

Let each of $m$ independent banks contain exactly one passing candidate among $D$. Draw $n\le D$ distinct candidates in random order per bank. To obtain $m$ pooled hits every bank must supply its single pass, so the full success probability is $F=(n/D)^m$. For comparison, let $S$ be the canonical homogeneous Bernoulli first-hit score. It vanishes unless every bank records a hit. If the observed total number of misses before those hits is $j$, its weight is $\binom{m+j-1}{j}/A_j$, where $A_j=[x^j](1+\cdots+x^{n-1})^m$.

For each vector of hit positions the unconditional probability is $D^{-m}$. Summing over the $A_j$ possible vectors cancels the denominator of the score. The hockey-stick identity gives
\[
\mathbb E S=D^{-m}\sum_{j=0}^{m(n-1)}\binom{m+j-1}{j}
=D^{-m}\binom{mn}{m},\qquad
\frac{\mathbb E S}{F}=\frac{\binom{mn}{m}}{n^m}.
\]
For $m=n=2,D=3$, the true probability is $4/9$ and the expected score is $2/3$. For $n=2$ the ratio grows as $2^m/\sqrt{\pi m}$. Identical banks can therefore yield arbitrarily large relative overestimation when distinct candidates are sampled. Independent Bernoulli attempts within a bank are essential to the scope of homogeneous calibration.

## Recovering the full target by randomizing the order

Fix **any** complete panel of binary outcomes, with $n_i$ slots in task $i$ and $k_i$ failures. Uniformly and independently permute the slots within each task, and observe only the initial run $u_i$ of failures (including $u_i=n_i$ if all fail). One may first sample a panel from a larger bank and then apply this design. Keep task identities and caps. Define
\[
H_i(z)=\sum_{j=0}^{u_i}\binom{n_i}{j}(z-1)^j .
\]
For $j\le n_i$, the probability that the first $j$ slots all fail is $\binom{k_i}{j}/\binom{n_i}{j}$. Hence, conditional on the complete panel,
\[
\mathbb E H_i(z)=z^{k_i},\qquad
\mathbb E\prod_i H_i(z)=z^{\sum_i k_i}.
\]
Summing coefficients of the product through degree $\sum_i n_i-m$ gives an unbiased estimate of the indicator of at least $m$ total hits. Averaging over an arbitrary distribution of panels preserves unbiasedness, even if the task counts move together. This removes both within-task Bernoulli independence and independence of the latent task counts; the known randomization of order is the operative hypothesis. Fixed historical ordering or adaptive generation of subsequent candidates need not satisfy it.

The deterministic correction is unique if unbiasedness is required for **every** vector of complete counts. In each task the conditional matrix of prefix indicators against $k=0,\ldots,n$ is lower triangular, with diagonal $1/\binom{n}{k}>0$. The prefix indicators are themselves a basis for functions of the stopped observation. Taking tensor products therefore yields an invertible conditional expectation operator. Since independent heterogeneous Bernoulli trials are a submodel, the correction agrees with the previous [heterogeneous signed score](cost-and-signed-scores.md) on every stopped record. Its coefficients can be negative, and this argument supplies no low-variance guarantee.

## Variance at the decision boundary

Write $t=\sum_i n_i-m$ and let $Z$ be the signed tail estimate. If the panel truly meets the target, $\sum_i u_i\le\sum_i k_i\le t$. The coefficient sum defining $Z$ includes the entire polynomial and equals its value at one, exactly 1. All conditional randomization variance is therefore incurred on panels that miss.

Suppose a panel has exactly $t+1$ failures. Unless every task places all its failures first, the product has degree at most $t$ and $Z=1$. The exceptional order occurs with probability $1/B$, where $B=\prod_i\binom{n_i}{k_i}$. In that order the highest coefficient is $B$ and $Z=1-B$. This yields the exact conditional variance $B-1$, also when $B=1$. For cap two, a panel with one all-failing task and $m-1$ tasks with one hit each has variance $2^{m-1}-1$. The unbiased rule can therefore be poorly concentrated even though it reconstructs every successful panel exactly.

For the empirical replay, an exact second moment is available before performing the randomization. Put $L_i(z)=z^{n_i}H_i(1/z)$, the analogous polynomial indexed by hits. For independent tasks let $M(x,y)=\prod_i\mathbb E[L_i(x)L_i(y)]$. The sum of its coefficients over $0\le a,b<m$ is the second moment of $1-Z$. Subtract the squared full miss probability to obtain $\operatorname{Var}Z$. This computation uses the whole stopped-record law rather than just the panels one hit short. [Exact variance calculation](finite-bank-variance.py).

| Panel | Draw design | Variance of signed score | Variance divided by full-indicator variance |
|---|---|---:|---:|
| All 118 | With replacement | 2.59518e-11 | 1.96862e+16 |
| All 118 | Without replacement | 1.56837e-11 | 2.76332e+16 |
| Mixed 100 | With replacement | 398181 | 1.41328e+19 |
| Mixed 100 | Without replacement | 396060 | 2.00952e+19 |

All four exact miss probabilities agree with the previously archived outward-rounded intervals. Variances refer to the specified resampling of fixed labels. [Exact fractions and boundary contributions](finite-bank-variance.json).

## Scope and verification

The finite-population prefix identity uses classical inclusion probabilities. Hypergeometric/binomial density ratios and the ordinary single-task pass-at-k statistic have established literatures. The contribution here is their application to this specific pooled first-hit score, the explicit opposite-sign family, and identification conditional on every complete panel. Priority beyond the works compared remains unestablished. [Horvitz and Thompson](https://doi.org/10.1080/01621459.1952.10483446) · [Dümbgen, Samworth and Wellner](https://arxiv.org/abs/1905.03009) · [Chen et al.](https://arxiv.org/abs/2107.03374).

[Verification code](finite-bank-transport.py) enumerates labelled within-task permutations, checks each coefficient on small panels including unequal caps, checks the single-pass family by summing observed scores, and verifies the one-task likelihood bound with rational arithmetic. This supplement postdates the assessment of the integrated v5 PDF.

