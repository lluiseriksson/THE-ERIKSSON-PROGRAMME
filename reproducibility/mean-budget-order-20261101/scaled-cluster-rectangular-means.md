# Stable rectangular means for scaled conductance clusters

Unit116,4November2026. An actual analytic construction in the existing
critical observation dossier. It treats growing intermediate-conductance
clusters, beyond the bounded-weak-value subclass of unit114. All geometric
and coefficient restrictions below are explicit additional restrictions;
they are NOT consequences of the original critical moment. No new paper,
PDF, Lean execution, numerical campaign, grade or independent review.

## 1. Precise positive result and its limits

Fix D>=3,Nc>=2,c>0,M>0,beta>=1. Let n>=1,m>=1 and the actual scalar
starting-vertex coefficients on X=(Z/nZ)^D satisfy

    1<=a(x)<=2m, mean(a)=m,
    sum_X a(x)^(-p)<=M*n^D/m^p,   p=D/2.                 (1)

Suppose additionally that pairwise-disjoint integer CUBES

    S_k=product_i[l_(k,i),r_(k,i)], side L_k>=1,
    k=1,...,J,

are non-wrapping in ONE common coordinate root [0,n-1]^D and satisfy

    (c/4)*L_k*(L_k-1) <= a(x) <= beta*L_k^2 on S_k,     (2)
    a(x) >= (c/4)*n*(n-1) off their union.               (3)

These are conditions on ACTUAL coefficients and explicit cubes, not an
assumed Poincare estimate, kernel gap, observation map or rank certificate.
The original a>=1 is retained; at L_k=1 the lower bound in (2) is zero and
no division by it is made. At n=1 (3) is likewise harmless.

There is an explicit actual normalized rectangular-mean map C_P with
Euclidean codomain dimension h*N, h=D*(Nc^2-1), such that for ALL cochains

    c||U||^2 <= E_a(U)+c||C_P(U)||^2,                    (4)
    E_a(U)=sum_(x,i,j) a(x)||U_j(x+e_i)-U_j(x)||^2,
    C_P(U)_(R,j)=sqrt(|R|)*mean_R U_j,
    J <= beta^p*M*n^D/m^p,
    N <= min(n^D,(2J+1)^D).                             (5)

For every fixed gamma>0, the HIGH-BUDGET regime m>=gamma*n^2 therefore
has the uniform bound

    dim F <= h*(1+2*beta^p*M/gamma^p)^D.                (6)

This attains the original target order in that restricted regime and
coefficient class, since max(1,n^D/(1+m)^p)>=1. The constant may depend on
beta and gamma, which are additional fixed class parameters. For gamma>=1
the original target maximum is exactly1.

There is a sharper geometric alternative: if the cubes' projections onto
ONE common coordinate axis are pairwise-disjoint integer intervals, then

    N <= 1+2D*J,
    dim F <= h*(1+2^(p+1)*D*beta^p*M)
                         *max(1,n^D/(1+m)^p),           (7)

for ALL m>=1, not only m>=gamma*n^2. Projection separation is an additional
geometric restriction, not merely disjointness of the cubes.

Neither (6) nor (7) proves that every original profile admits cubes obeying
(2),(3), or the necessary geometry. The original unrestricted critical
rectangular question remains ONE active question and remains OPEN.

## 2. The cluster count is derived from the original critical moment

The upper coefficient bound on S_k gives, because 2p=D,

    sum_(x in S_k) a(x)^(-p)
       >= L_k^D/(beta*L_k^2)^p=beta^(-p).

Disjointness lets these charges be added. Hence

    J/beta^p <= sum_X a^(-p) <= M*n^D/m^p,              (8)

which proves the J bound in (5). In particular neither a bound on J nor a
bounded cluster volume is assumed. The sizes L_k and values a on the cubes
can grow without a fixed W upper bound. For m>=gamma*n^2, (8) bounds J by
beta^p*M/gamma^p, uniformly in n.

The cluster upper bound beta*L_k^2 is essential to THIS charging proof.
Dropping it and still charging beta^(-p) per cube would be invalid. The
lower bound in (2) has a different role: it supplies actual energy control.
The critical moment alone does not supply that lower bound or the cubes.

## 3. Arbitrarily positioned disjoint cubes: explicit arrangement partition

For each axis i collect boundaries 0,n and all l_(k,i),r_(k,i)+1. Sort and
deduplicate them, and take the nonempty consecutive integer intervals.
There are at most 2J+1 intervals on each axis. Their Cartesian products
give at most (2J+1)^D nonempty rectangular cells partitioning X.

For any particular S_k, every cell is either wholly inside S_k or disjoint
from it: no interval crosses one of its boundary coordinates. Because the
cubes are disjoint, each cell is inside at most one cube. Thus every cell
has one of two types:

* inside S_k, with each side <=L_k and actual coefficients satisfying (2);
* outside every S_k, with each side <=n and actual coefficients satisfying (3).

This constructs the partition rather than assuming a covering certificate.
No separation of cluster projections, balanced tree or general BSP theorem
is used. The elementary arrangement bound is polynomial in J, not linear.
Its polynomial dependence is harmless for (6), because J has already been
proved bounded independently of n in that regime.

## 4. Actual internal-edge stability: no abstract kernel hypothesis

For a path of l vertices, counting variance equals

    (1/l)*sum_(r<s)|u_r-u_s|^2.

Path Cauchy--Schwarz bounds each pair by (l-1) times its path edge-square
sum. At each cut there are at most l^2/4 crossing pairs. Consequently

    Var_path(u) <= l*(l-1)/4 * sum_path_edges |du|^2.

Tensorize uniform product variance on a rectangular cell R whose sides
are <=L. Converting back to counting norms gives

    Var_R(u) <= L*(L-1)/4 * sum_internal_edges(R)|du|^2. (9)

There is no additional D factor; each coordinate-fibre energy is summed
once. For vector fields apply this to each actual real coordinate. The
classical product-variance input and its primary proof are specified below.

If R lies inside S_k with L_k>=2, every ORIGINAL internal forward edge
starts at a(x)>=(c/4)*L_k*(L_k-1). Apply (9) with L=L_k to obtain

    c*Var_R(U) <= E_a,R(U).

For L_k=1 the cell is a singleton, so Var_R=0 directly. For a cell outside
all cubes apply (9) with L=n and (3), obtaining the same inequality; n=1
is again a zero-residual singleton. This handles the zero lower-bound
edge case without division by zero.

Internal-edge sets of distinct cells are disjoint. Dropped crossing and
torus-wrap edges have nonnegative energy and are not reassigned. At n=2
the actual two parallel forward occurrences are kept or dropped according
to their original positions; no simple-graph substitution occurs.

Summing and using the EXACT normalized-mean decomposition

    ||U||^2=sum_R Var_R(U)+||C_P(U)||^2

proves the GLOBAL all-cochain inequality (4). In particular it is stronger
than a bound just on ker C, so it does not invoke the refuted fixed-penalty
implication of units108/112. Its restriction to actual divergence-zero
fields does not require the rectangular averaging operator to preserve
divergence. The original nonlinear data are explicitly C=C_P,
Phi(y)=c||y||^2,K=c and arbitrary positive neighbourhood radii.

## 5. Projection-separated clusters: a linear leaf count

Relabel axes so their first-coordinate intervals I_k are disjoint and
sort these intervals. Use their J strips I_k*[0,n-1]^(D-1), together with
the at most J+1 nonempty gap strips in the first coordinate.

Only S_k can meet its strip. Within that strip retain the whole S_k.
For each transverse coordinate i=2,...,D, retain its two possible outside
rectangles: first-coordinate I_k; transverse coordinates before i equal
their S_k intervals; coordinate i below or above its S_k interval;
later coordinates unrestricted in [0,n-1]. Discard empty rectangles.

The first transverse coordinate outside the cube's interval gives unique
membership, so these at most 2(D-1) rectangles partition the strip's
complement of S_k. Each is strong by (3). Gap strips are also strong.
Thus the total is at most

    J*[1+2(D-1)]+(J+1)=2D*J+1.

The same actual-edge proof (9) applies to whole weak cubes and strong
complement strips, proving (4) for this smaller partition. Finally (8)
and (1+m)/m<=2 give

    1+2D*J <= 1+2D*beta^p*M*n^D/m^p
            <= [1+2^(p+1)*D*beta^p*M]
                             *max(1,n^D/(1+m)^p),

as asserted. Adjacency, boundary-touching intervals, singleton cubes and
empty end gaps cause only empty rectangles to be removed, never a new
coercivity assumption. For J=0 retain the whole strong torus coordinate
box; the bound is N=1.

## 6. Compatibility with the closed all-threshold obstruction

The unit115 family has one cube of side t, n=t^2,m=gamma*n^2 and
gamma=max(1,c/4). Inside it b=gamma*n=gamma*t^2, so (2) holds with the
FIXED beta=gamma. Outside, A>=m>=c*n*(n-1)/4. Its exact mean, cap and
critical moment M=2 were already proved, not assumed here.

It therefore belongs to this scaled-cluster class for every t, despite
its weak coefficient growing without bound. That is why the unit114
fixed-W coefficient-gap subclass was insufficient to describe it. The
present construction uses cluster averages and is consistent with the
unit115 successful D+1 partition. Its safe counts (5),(7) need not be
optimal for that anchored single cube, for which D+1 was proved explicitly.

No claim is made that the cube decomposition is unique, recoverable by a
particular greedy threshold, or available for every critical profile. The
theorem can be applied to supplied explicit cubes obeying pointwise
inequalities, rather than to an assumed spectral/Poincare certificate.

## 7. Verification, primary context and one-question protocol

Analytic verification: critical exponent charge L^D/(L^2)^(D/2); actual
upper/lower bounds' distinct roles; arrangement coverage without crossing
cluster boundaries; product variance counting normalization; internal
starting-vertex weights; singleton/n=1/n=2/wrap cases; disjoint retained
edges; global fixed penalty; high-budget J bound; projection-separated
strip coverage and linear count; J=0 and empty gaps; conversion m to1+m;
unit115 benchmark and explicit limitations. No local executable
mathematical check, Lean, numerical experiment or runtime allocation.

Primary classical input checked4November2026: instructor Chihao Zhang,
scribes Xuanxuan Liu and Yuchen He, AA2025Lecture8, Theorem1 and its
conditioning/martingale/Jensen proof:
https://chihaozhang.com/teaching/AA2025/lectures/lec8/lec8.html . No
nonclassical tensorization or general geometric-complexity theorem is
claimed. The arrangement/strip counts and finite actual-edge adapters
are derived above. No exhaustive priority study or originality finding.

Same preparing Codex agent, served backend/effort unexposed. No independent
AI/human review, numeric score or old PDF-grade inheritance. Objections:
the scaled coefficient/cube assumptions are additional; high-budget (6)
does not cover all m/profiles; linear all-m bound (7) needs projection
separation; the general arrangement bound is polynomial in J; no Lean
certificate, sharp constants, optimal partition count or physical gap.
Group this proof with the existing critical dossier, not a separate paper.

ONE active original critical rectangular question remains unchanged.
This is the first actual scaled-cluster construction unit, without closure
of that general target. Previous mass-only/abstract-Schur routes stay
STOPPEDcounter3; single-global-threshold/per-vertex target route stays
STOPPEDafter2units by its proved all-threshold falsifier. No old counter
is reset. The concrete remaining issue is a coefficient-derived multiscale
cluster decomposition with stable original-edge averages and LINEAR total
rectangular count when total critical mass grows; (1) alone has not been
proved to give (2),(3) or the geometry. Do not assert this as a structure.
If three units of this route yield no substantial further reduction,
record that precise decomposition/count blocker and change route. A
falsifier of the original target must still defeat EVERY allowed partition.
PR29 remains20/41,TermSource=0; interacting/continuum gap is open. No new
AIRR/ai.viXra deposit, acceptance or publication occurs in this unit.
