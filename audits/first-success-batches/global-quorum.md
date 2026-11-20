# Deciding the pooled target with fewer candidate checks

In the [finite-bank analysis](finite-bank-transport.md), the signed first-hit correction is unbiased under a specified randomization and can have high variance. If the evaluation order is still under the experimenter's control, one can instead determine the full-panel decision from a subset of the checks, without estimating the labels of the remaining candidates.

Select all candidate slots according to the stated design. Shuffle the slots uniformly, independently of their outcomes. For a panel of $T$ slots and threshold $m$, stop on the $m$-th hit or the $(T-m+1)$-st miss, whichever occurs first. Report one on the first event and zero on the second. This gives exactly the same indicator as evaluating all $T$ slots, for every fixed assignment of pass/fail labels. Before either boundary is reached, the unrevealed labels admit completions with either answer. Thus for a given inspection order an exact rule with no additional label information cannot stop sooner. The proof concerns the realized decision and requires neither independent labels nor known task success rates.

Conditional on $h$ total hits, the expected number of checks over the random order is
\[
C(T,h,m)=
\begin{cases}
m(T+1)/(h+1), & h\ge m,\\
(T-m+1)(T+1)/(T-h+1), & h<m .
\end{cases}
\]
For example, on a successful panel the $h$ hit positions divide the $T-h$ misses into $h+1$ exchangeable gaps. There are on average $(T-h)/(h+1)$ misses per gap before the $m$-th hit. Interchanging hits and misses gives the second case. This is the classical order-statistic expectation for sampling without replacement. Early stopping at a fixed acceptance or rejection boundary is classical curtailed inspection. [Girshick, Mosteller and Savage (1946)](https://doi.org/10.1214/aoms/1177731018). The result here compares two directly implementable evaluation protocols on the released task counts.

With two slots in each of $m$ tasks of size $D$ and $c_i$ passes in task $i$, the separate first-hit protocol uses $m+\sum_i(D-c_i)/D$ checks in expectation. For the shuffled protocol we average $C(2m,h,m)$ against the exact distribution of total hits obtained by convolving the individual two-slot laws. The comparison charges one unit per label inspection. It assumes candidate generation, any deduplication and layout of the candidate bank occur before inspecting labels. It does not establish a saving in model-generation time or wall time. Histories that only stored first hits cannot be retroactively queried using this rule.

| Panel | Draw design | Global exact decision | Separate first hits | Full inspection |
|---|---|---:|---:|---:|
| All 118 | With replacement | 159.1179 | 148.5500 | 236 |
| All 118 | Without replacement | 159.1166 | 148.5500 | 236 |
| Mixed 100 | With replacement | 143.8599 | 130.5500 | 200 |
| Mixed 100 | Without replacement | 143.8580 | 130.5500 | 200 |

The indicators from the global rule and exhaustive inspection agree on every panel. As a result their variances are identical across random panels. This does not make the forward order optimal among designs using additional task information. A smaller count of expected checks also does not imply a saving on every realization.

[Verification code](global-quorum.py) · [Exact costs](global-quorum.json) · [Released EvalPerf counts and sampling protocol](evalperf-replay.md). The computation checks the conditional cost formula by enumerating every hit-position subset through nine slots and cross-checks the full miss probabilities against the independently computed variance report. This supplement postdates the integrated v5 PDF and its assessment.

