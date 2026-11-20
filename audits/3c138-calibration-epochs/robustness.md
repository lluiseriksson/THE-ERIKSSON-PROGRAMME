# Stability of the six-period result

The 47-by-8 VLA table can be represented to 5% relative error using six consecutive spectral profiles and a free amplitude in every month. This supplement determines exactly how much its entries must be allowed to vary before a seventh profile can be forced. Each published entry F can change independently within [F/G, GF]. The approximation is judged against the changed table, and the six boundaries and profiles may be reoptimized after the change.

**For all changes up to and including G = G★, six profiles suffice. For any G > G★, some allowed table requires at least seven.** The sharp threshold is

    G★⁴ = 498301732819155321766211525003169 / 490655084183260845661760184425072
    G★  = 1.0038735774849628… .

Thus the upper perturbation is about +0.38736%, with reciprocal lower factor 1/G★. The inputs are the exact decimals in the linked CSV. This is deterministic sensitivity of the table representation. Assigning a probability to such changes, or interpreting them as telescope errors, requires a model that this calculation does not supply. [NRAO calibration guide and table](https://science.nrao.edu/facilities/vla/docs/manuals/obsguide/calibration)

## A common table that defeats all partitions

Let R=(1+.05)/(1−.05)=21/19. If a single profile fits an interval, the cross-ratio of any two dates and two bands in it is at most R², in either orientation. At the following seven dates multiply the listed bands by G and divide the other bands by G. Leave every other date unchanged.

| Date | Bands multiplied by G | Pair used up to next date |
|---|---|---|
| February 2021 | L | L/Q |
| February 2022 | S, Q | S/Q |
| February 2023 | L | L/Q |
| September 2023 | C | C/Q |
| February 2024 | L, Q | L/Q |
| July 2024 | Q | L/Q |
| December 2024 | none | — |

For each successive pair of dates take the earlier band ratio divided by the later one. At G★ five cross-ratios are already strictly above R². The September 2023–February 2024 C/Q cross-ratio is exactly R²; the perturbation multiplies its unperturbed value by G⁴. For G just above G★ all six cross-ratios exceed R² simultaneously. The six intervals have disjoint sets of possible cut positions, so any fit needs at least six cuts, hence at least seven periods. For any larger allowed radius the same near-threshold witness remains available. A separate full-table fit found exactly seven periods for a nearby explicit perturbation.

## Why every perturbation at the boundary still admits six

On one interval a profile exists if there are band corrections compatible with all per-month ratios. Eliminating the monthly amplitude gives a system of pairwise difference inequalities in log band offsets. An interval is infeasible precisely when it contains a simple directed cycle of bands whose product of observed ratios exceeds R to the power of the cycle length. The maximizing date for each edge can be chosen separately. This criterion includes cycles with more than two bands.

If a partition needs seven or more periods, the greedy longest-feasible-prefix construction produces six infeasible intervals whose successive endpoints coincide: append the first date of the next greedy block to the current block. The last interval can be extended to the final date. Conversely such a chain forces six cuts. This reduces the universal lower-bound proof to excluding every possible chain under one common array of perturbations.

The exact verifier first bounds each edge by its largest possible band ratio anywhere on the interval. Even allowing these edge maxima independently leaves just three chains that could violate the tolerance at G★. For these chains it enumerates simple band cycles, then the candidate dates for each edge. At a shared endpoint it keeps one variable per band for both incident intervals. All other perturbation variables belong to a single chosen inequality and can be maximized there. Terms with the same endpoint coefficients and the same interior exponent are dominated by the term with the strongest violation.

To rule out a combination, the verifier multiplies its strict cycle inequalities with nonnegative integer exponents. Every shared endpoint factor appears with its **net** exponent. If the largest allowed product is at most the product required for strict violation, the combination is impossible. The search visited 18 branches and certified 12 exclusions, covering all three chains. Taking fourth powers makes every comparison rational; no tolerance from a numerical optimizer enters this exclusion or the explicit upper certificate.

## Reproducibility

Run `python robust-seven.py` on Linux with the dependencies used by the two scripts in this package. It verifies the downloaded source checksum and generates `/content/archive.zip` containing `exact.json`. Compare the exact rational fourth power, chain indices, counts and six witness comparisons with `robust-seven.json`. The floating-point display of the fourth root is informational. The earlier manuscript PDF and review refer to science commit `2866945524b0ebd3697f6169d17112c1899e0c8a`; this supplement was produced subsequently.
