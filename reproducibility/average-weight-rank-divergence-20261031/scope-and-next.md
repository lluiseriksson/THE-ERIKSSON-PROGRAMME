# Closed-route target: actual nonlinear rank divergence under mean weights

For lattice size n+1, fixed finite d,Nc and fixed transverse directions i!=j,
use the actual nonnegative componentwise weights w_n and their actual mean
b_ij(n)=(n+1)^(-d)*sum_x w_n(i,(x,j)). Retain fixed c>0, C_n(0)=0,
Frechet differentiability at zero, locally upper-quadratic penalties and
local coercivity on actual divergence-free fields. Output spaces F_n and
K_n,delta_n,radius_n may vary, with no uniform bounds on these local data.

The new target derives the positive-frequency multiplier transport using
k.val=r.val+1+R as an integer lift in Fin(2R+1), sums squared bounds, proves
nonnegativity of the actual spatial mean, and composes the finite theorem:

    c*(2R-dim F_n) <= 8*pi^2*(1+b_ij(n))*R^3/(n+1)^2,   R<n+1.

Under (1+b_ij(n))/(n+1)^2 ->0, every fixed R eventually has RHS<c.
Integrality then gives dim F_n>=2R eventually, hence dim F_n tends to
infinity and no common finite output-dimension bound exists. The desired
cutoff, multiplier/trace comparison and low-band/kernel certificates are
not assumed. This closes the exact average-weight route proposed in unit047
if its exact source and two fresh clones pass; no prior verdict is inherited.

Scope is NONNEGATIVE finite-flat weights. This replaces a pointwise maximum
growth condition within that class; it does not cover arbitrary signed
weights from older cap theorems. Fixed positive c remains a premise.
This is rank divergence, not volume-density or a physical spectral gap.
No interacting/continuum producer or hRpoly hypothesis is discharged.
PR29 stays20/41,TermSource=0. Frozen public AIRR v3 is unchanged.

Preflight commit c4f7c419 was not executed. Source ac60c0df supplies an
explicit Fin bound and multiplication by positive c before the first run;
statements and six oracle criteria did not change. First driver076 was
pasted byte-for-byte into a normal new own Colab notebook after a GitHub
driver-ref404 during pending push. Its source SHA and LF guards were retained.
No new GitHub authorization, runtime sharing or grant/quota change occurred.
The exact first driver LF hash and transport recovery are in076-transport.json.
A UI-tool save delay/reset did not rerun or alter the mathematical execution;
the released notebook output was recovered and native-copied to D.

Primary context: existing proved stdAddChar_centered_bound uses integer
lifts and the classical complex exponential chord bound. The actual-family
parameter/tendsto interface was checked against CoexactSubquadraticFamily.lean.
Spielman's author-hosted Graphs, Vectors, and Matrices survey
https://cs-www.cs.yale.edu/homes/spielman/PAPERS/bull1557.pdf and Spectral
Graph Theory chapter provide classical weighted quadratic-form background.
No original-priority or independent-review claim follows from these sources.

After terminal verification, stop extending this route and consolidate the
closed finite/asymptotic theorems, quadratic boundary example, and penalty
counterexamples into the existing coarse-information manuscript. Use exact
source/PDF hashes, visual PDF review, full review context without inherited
ratings, and the existing author publication route. Do not create separate
small-corollary papers or infer expired access from a missing lookup.
