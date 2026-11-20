# Do unprinted kilometre rates reconcile the component disclosures?

**Result.** Even if every truck profile has its own unknown air-and-noise rate, held constant across sections, the fifteen A12 accounting sections cannot all share one section length per section across profiles at the reported precision. The first fourteen sections do admit such a representation jointly for the air/noise and carbon disclosures. The carbon disclosures alone also admit one for all fifteen. This tests a model of the published components. It does not imply an error in the posted toll amounts.

**A four-cell certificate.** Index the sections in the order of the annexes, starting at one. On section 10 (Schwaz to Vomp), the air/noise disclosures for the two-axle zero-emission profile and the four-or-more-axle Euro 0–III, carbon-class-1 profile are EUR 0.0150 and 0.3875. On section 15 (A12 Innsbruck Ost to Innsbruck Mitte), they are EUR 0.0085 and 0.2173. If both profiles had stable positive rates, the product on one diagonal of this rectangle would equal the product on the other. The largest possible ratio of the smaller diagonal to the larger one, allowing closed rounding intervals of EUR 0.00005 in either direction, is

    (0.01505 × 0.21735) / (0.38745 × 0.00845) = 6923/6929 < 1.

This four-cell argument makes no use of the displayed kilometre rates. A more precise unprinted rate for each profile cannot by itself resolve the contradiction. Differences in the scope or basis of the section disclosures remain possible.

**Constructive checks.** For each positive charge column let U denote the inverse of its unknown rate and let L denote the unknown length of a section. A charge within [lo,hi] requires L ≤ hi U and U ≤ L/lo when lo > 0. Multiplication around a directed cycle gives a contradiction if the product of factors is below one. A feasible assignment can instead be checked directly in all inequalities. The supplement contains exact positive assignments for each feasible fit, and cycles for the infeasible fits. Entirely zero columns admit rate zero. Lengths have an arbitrary common scale. Reproduction uses only Python's standard library and the sections.json data in the manuscript directory.

This analysis followed the first assessment of the PDF and is separate from that assessment.