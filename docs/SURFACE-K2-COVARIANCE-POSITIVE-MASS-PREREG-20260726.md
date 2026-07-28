# K2 covariance positive-mass refinement — preregistration

The initial covariance probe lost cell masses because the midpoint-plus-
Hessian enclosure for `H d^2` crossed zero. This follow-up keeps the same
nominal point `delta=0,t=2.90`, side 12, and Arb precision 140 bits, but uses
the certified pointwise interval enclosure of the positive weight `H d^2`
for each cell mass (area times its lower/upper endpoints). The Hessian rule is
unchanged for `H d^2 a`, `H d^2 b`, and `H d^2 ab`.

Grids 12 and 24 are rerun. Acceptance requires every cell mass to have a
strictly positive lower endpoint and finite centered covariance output. This
is still nominal design evidence only; no tails or R3 budget are included.
