# K2 covariance mass refinement — preregistration (2026-07-26)

The nominal covariance probe at grids 12 and 24 cannot form cell means because
its interval enclosure for the total mass contains zero. This follow-up tests
only that prerequisite at grids `48` and `96`, with `delta=0`, `t=2.90`, side
12, and Arb precision 140 bits. It does not claim a covariance or R3 result.

Acceptance requires a finite positive lower endpoint for `M` and finite
between/within covariance intervals. If `M` still contains zero at grid 96,
this midpoint-plus-Hessian covariance carrier is rejected for the stated
geometry; no further grid escalation is implicit.
