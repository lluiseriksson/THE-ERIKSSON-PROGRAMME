# Finite calibration on the same task bank at three caps

For even $m=\ell^3$, half the independent Bernoulli tasks always succeed and half fail with probability $q=2/\ell$. The pooled probability of at least $m$ successes equals one for each cap $n=2,3,4$. The table encloses the expected stopped score. Each row uses exactly the same task probabilities across all three columns.

| Tasks | Two attempts | Three attempts | Four attempts |
|---:|---:|---:|---:|
| 64 | [0.000967594, 0.000967595] | [0.036415990, 0.036415991] | [0.188937693, 0.188937694] |
| 216 | [0.000197615, 0.000197616] | [0.050544803, 0.050544804] | [0.340788892, 0.340788893] |
| 512 | [0.000031346, 0.000031347] | [0.054662763, 0.054662764] | [0.442788443, 0.442788444] |
| 1000 | [0.000004619, 0.000004620] | [0.055872937, 0.055872938] | [0.517401671, 0.517401672] |
| 4096 | [1.2E-8, 1.3E-8] | [0.055695620, 0.055695621] | [0.656526332, 0.656526333] |

The sample-size limit for these columns is respectively zero, $\exp(-3)$ and one by the dilute-limit theorem. These finite values measure how slowly a limit may become numerically representative.

Let $a_{k,s}=[z^s](1+z+\cdots+z^{n-1})^k$ and $h=m/2$. A nonzero log has all $h$ uncertain tasks hitting. Its total wait $s$ has unconditioned mass $(1-q)^h q^s a_{h,s}$. The weights divide the unrestricted composition count by the capped count for all $m$ tasks. Thus the exact expected score is
\[
 (1-q)^h\sum_{s=0}^{h(n-1)}q^s\,a_{h,s}\binom{m+s-1}{s}/a_{m,s}.
\]
The recurrence for $a_{k,s}$ follows by differentiating $A=U^k$ and equating coefficients in $UA'=kU'A$. The program verifies exact integer divisions, reflection symmetry, coefficient sums, and direct enumeration on small cases. Each whole summand is enclosed by integer division at scale $10^{22}$ before adding the bounds. The table is rounded outward again to nine decimal places. The unrounded integer endpoints are in same-bank.json. This companion postdates the frozen PDF. It has no separate model assessment.
