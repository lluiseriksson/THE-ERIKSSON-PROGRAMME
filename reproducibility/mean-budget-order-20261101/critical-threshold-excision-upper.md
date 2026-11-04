# Actual rectangular means by threshold excision

Unit114,4November2026. One constructive analytic result in the existing
critical-moment dossier, together with its explicit loss and an obstruction to
the balanced-threshold algorithm. No new paper, PDF, Lean run, executable
diagnostic, originality certificate or independent review. The original
critical rectangular target remains the ONE active question.

## 1. Statement on the actual coefficients

Fix D>=3,Nc>=2,c>0, m>=1 and M>0. On X=(Z/nZ)^D, n>=1, suppose actual
scalar starting-vertex coefficients satisfy the original conditions

    1<=a(x)<=2m, mean(a)=m,
    sum_x a(x)^(-p) <= M*n^D/m^p,   p=D/2.

Use E_a(U)=sum_(x,i,j) a(x)||U_j(x+e_i)-U_j(x)||^2, counting norms and
h=D*(Nc^2-1) real field/internal coordinates. This is the actual flat energy,
not a covariant or interacting substitution. The known flat Hodge adapter
identifies it with Q_w in precisely this scalar subclass.

For EVERY tau>=1 there is an explicit partition P_tau into integer
axis-aligned rectangles such that the ACTUAL normalized means

    C_tau(U)_(R,j)=sqrt(|R|)*mean_R U_j

satisfy, on ALL cochains,

    c||U||^2 <= E_a(U)+c||C_tau(U)||^2,                    (1)
    dim F=h*N_tau,
    N_tau <= A*max(1,n^D/tau^p)+2D*#B_tau,               (2)
    B_tau={x:a(x)<tau},  A=(1+sqrt(c))^D.

The partition has at most n^D nonempty leaves as well. Its weak singletons
are supplemented by genuinely averaged complementary rectangles; it is NOT
the failed point-only observation of unit110. No kernel estimate, abstract
rank certificate, weak-region shape or separately assumed weak-site count
is an input to this theorem.

In particular tau=sqrt(m) and the critical moment give the unconditional
constructive upper bound

    dim F <= h*(A+2D*M)*max(1,n^D/m^(D/4)).              (3)

This does NOT attain max(1,n^D/(1+m)^(D/2)). Its decay exponent in m is only
D/4. It is a proved weaker spatial-average bound in the ORIGINAL coefficient
class, not an elimination of the original target's remaining difficulty.

## 2. A rectangle can isolate any selected vertex at constant leaf cost

Start with any rectangular grid partition into N_0 cells. Given a selected
vertex x in one current rectangle R=product_i[l_i,r_i], retain {x}. For
each i, also retain the nonempty rectangles

    {x_1}*...*{x_(i-1)}*[l_i,x_i-1]*product_(k>i)[l_k,r_k],
    {x_1}*...*{x_(i-1)}*[x_i+1,r_i]*product_(k>i)[l_k,r_k].

Every y in R other than x belongs to exactly one of them: choose the FIRST
coordinate where y differs from x and its lesser/greater side. They are
disjoint and cover R\{x}; all sides are subintervals of original sides.
Thus replacing R creates at most 2D+1 nonempty leaves, an increase <=2D.
If R is already a singleton there is no increase.

Process each vertex in B_tau in any fixed order, such as lexicographic
order. Previously isolated singletons cannot be split by processing a
different vertex. At termination every bad vertex is a singleton; every
remaining leaf contains only vertices with a>=tau. The final count is

    N_tau <= N_0+2D*#B_tau.                              (4)

This induction proves the count for ARBITRARY locations and shapes of the
bad set, without a balance condition or a logarithmic full-cube-tree cost.
It concerns isolated vertices, not disjoint extended rectangles in general
binary-space-partition complexity theorems. No such theorem is imported.

## 3. Strong leaves supply the actual global fixed-penalty estimate

If tau<c/4 use a singleton grid from the start: (1) is then the exact
identity observation and all residuals vanish. Otherwise put

    ell=min(n,floor(2*sqrt(tau/c))) >=1

and partition each coordinate interval into consecutive intervals of length
at most ell. Its grid count is N_0=ceil(n/ell)^D. Every final leaf still has
each side of length <=ell. Bad singletons have zero residual.

Here is the required PROVED inequality on a strong leaf R. On a one-sided
path with l vertices the exact counting variance identity and edgewise
Cauchy--Schwarz imply

    sum_{k=0}^{l-1}|u_k-mean(u)|^2
      =(1/l)*sum_{r<s}|u_r-u_s|^2
      <= l*(l-1)/4 * sum_{t=0}^{l-2}|u_(t+1)-u_t|^2.   (5)

Indeed each pair contributes at most (l-1) times its path's edge-square
sum. For edge cut t, at most (t+1)*(l-t-1)<=l^2/4 pairs cross it. Dividing
by l gives exactly the displayed safe coefficient. For l=1 both sides
are zero.

Variance tensorization for the uniform PRODUCT measure on R gives the sum
of these coordinate-fibre conditional variances. Converting probability
norms back to counting norms, (5) therefore yields

    Var_R(u) <= ell^2/4 * sum_internal_edges(R)|du|^2
             <= ell^2/(4*tau)*E_a,R(u).                (6)

There is NO extra factor D: the coordinate energies are already summed.
Tensorization can also be proved by successive conditioning/Jensen; its
classical statement is identified in the primary context below. The
starting-vertex weights on every retained internal edge are actual a(x)
and at least tau. No coefficient is reassigned or reflected.

By construction c*ell^2/(4*tau)<=1. Sum (6) over leaves and field/internal
coordinates. The retained internal-edge sets are disjoint; all omitted
crossing/wrap edges have nonnegative energy. The exact Euclidean identity

    ||U||^2=sum_R Var_R(U)+||C_tau(U)||^2

proves (1). This is a GLOBAL estimate for all U, not merely coercivity on
ker C, so it avoids the finite-cycle fixed-penalty failure. It restricts
to actual divergence-zero fields without requiring averages to preserve
divergence. The original nonlinear data are supplied by this linear C,
Phi(y)=c||y||^2 and arbitrary positive neighbourhood radii.

The coordinate root uses [0,n-1]; wrap edges are omitted, not rewired. At
n=2 both actual forward occurrences exist, but the path uses only its
internal occurrence and drops the other positive contribution. At n=1
all cells are singletons and the argument is immediate.

## 4. Proved count and what the moment actually pays for

When ell=n, N_0=1. Otherwise, for t=2*sqrt(tau/c)>=1,
floor(t)>=t/2 and ceil(n/ell)<=1+2n/t=1+n*sqrt(c/tau).
This gives N_0<=A*max(1,n^D/tau^p). In the separate tau<c/4 singleton case,
n^D<=(c/4)^p*n^D/tau^p<=A*max(1,n^D/tau^p), so the SAME bound holds.
Combine with (4) to prove (2).

Each bad vertex has a(x)^(-p)>tau^(-p). For a nonempty bad set this implies

    #B_tau <= M*n^D*tau^p/m^p.                          (7)

The weak cardinality bound is DERIVED, not assumed as a certificate or
moved into a structure. It is also true for an empty bad set. Insert
tau=sqrt(m)>=1 in (2),(7): both contributions scale as n^D/m^(p/2),
proving (3). The exact arithmetic mean and cap are compatible with this
proof but are not used beyond defining the original subclass; the moment
condition remains additional.

## 5. Target order on a stated coefficient-gap subclass

Suppose ADDITIONALLY that fixed W>=1 and theta>0 satisfy, for every x,

    a(x)<=W OR a(x)>=theta*m.                           (8)

This pointwise coefficient gap is a REAL EXTRA RESTRICTION; it is NOT
derived from the original mean, cap or critical moment. Take
tau=max(1,theta*m). If theta*m<1 then B_tau is empty since a>=1; otherwise
a<tau implies a<=W by (8). Consequently in either case

    #B_tau <= M*W^p*n^D/m^p.

Also max(1,n^D/tau^p)<=max(1,theta^(-p))*max(1,n^D/m^p).
Hence the SAME actual construction obeys the original target order

    dim F <= h*2^p*[A*max(1,theta^(-p))+2D*M*W^p]
                     *max(1,n^D/(1+m)^p).              (9)

Here (1+m)/m<=2 was used. This removes geometric restrictions on the weak
set and derives its allowed size, compared with the older single weak-box
escape. It does not remove the coefficient gap (8), so (9) is not a solution
of the unrestricted critical problem and not a new active question.

## 6. A useful falsifier for overstating this algorithm

The particular balanced-threshold rule tau=sqrt(m) can MISS the target even
on UNIFORM coefficients: take a=m=n^2 and fixed c>0. Then B_tau is empty,
tau=n, and for all large n the rule keeps its unrefined grid with

    ell=floor(2*sqrt(n/c))<n,
    N_tau=ceil(n/ell)^D >= (sqrt(c)/2)^D*n^(D/2).

The desired maximum is1. Thus this rule itself has an unbounded overhead;
the proof's loss cannot be described as attainment of the target. On the
same uniform profile a larger threshold such as tau=m already gives a
constant-size grid. This is NOT an all-partition counterexample, nor a
proof that every data-dependent choice of tau must fail. Improving (3)
uniformly needs a new way to retain averaged stability across intermediate
conductances, not relabelling its exponent or invoking spectral rank alone.

## 7. Primary context, verification and research protocol

Classical variance tensorization: Chihao Zhang's author-hosted Lecture8,
AA2025, Theorem1 and its conditioning/Jensen proof, checked4November2026:
https://chihaozhang.com/teaching/AA2025/lectures/lec8/lec8.html . Only this
standard product-variance input is used; the path coefficient, counting
normalization, finite isolation induction and actual-edge adapter are
derived explicitly here. Recursive axis cuts are elementary. A geometry
search identified much broader BSP literature, but no theorem on extended
rectangles was used or claimed verified. No exhaustive priority search or
originality claim; this construction is elementary in character.

Verification this unit is analytic: first-differing-coordinate cover and
disjointness; leaf increase; persistence of isolated points; coefficient
location on internal edges; uniform product counting conversion; singleton,
n=1/n=2, nondivisible grid and ell=n boundaries; separate tau<c/4 case;
strict threshold and empty bad set; critical exponent arithmetic; explicit
extra gap (8); original fixed penalty and all-cochain/physical distinction;
and the uniform-profile falsifier of the balanced rule. No local executable
arithmetic, Lean, numerical oven or fresh-runtime claim is made.

Same preparing Codex agent; actual served backend/effort unexposed. No
independent model/human review or inherited PDF/source grade. No numerical
assessment is assigned to this note. Material objections: (3) is weaker
than the target; (8) is substantial additional coefficient information;
the isolation construction is not kernel-verified; the product input is
classical; no general spatial optimality or originality established; no interacting or
continuum gap. Group with the existing dossier, not a micro-paper.

ONE active question remains the original critical rectangular target.
This unit changes mechanism to actual strong-cell refinement and proves
a general off-target bound plus a target bound under an explicit gap.
The previous mass-only and abstract-Schur/point-pivot routes stay STOPPED
with their existing counters3. This does not reset them. Record one unit
of this construction route without closure of the general target.
Mechanism: original-edge strong rectangles plus complementary averages;
falsifier for a target claim must defeat EVERY allowed partition. Abandon
mere balanced-threshold retuning if no new coefficient-adapted averaging
estimate is supplied: its uniform-profile failure is already proved above.
After three units without a substantial further reduction, document the
specific intermediate-conductance blocker and change route. PR29 remains
20/41,TermSource=0. No AIRR/ai.viXra deposit or publication occurs here.

## 8. Unit115: every single-threshold point-excision rule can lose the target

4November2026. This strengthens Section6 from one balanced rule on a
uniform profile to ALL choices of a single threshold on the SAME explicit
nonuniform family. It is a mechanism-level counterexample, not a
counterexample to every rectangular partition. No new PDF, grade, numerical
run or Lean verification. The prior unit114 statements remain unchanged.

### Exact family and quantifiers

Fix D>=3,Nc>=2,c>0 and put gamma=max(1,c/4), p=D/2. For integers t>=2 let

    n=t^2,   m=gamma*n^2,   b=gamma*n,
    S={0,...,t-1}^D,   s=|S|=t^D=n^p,
    f=s/n^D=n^(-p),   A=(m-f*b)/(1-f),
    a(x)=b on S, and A off S.                           (10)

Use sufficiently large t that n>4*gamma/c. For EVERY threshold tau>=1,
even chosen after reading the entire profile and depending arbitrarily on
t, the Section2--3 algorithm produces at least

    N_tau >= kappa*n^(D/2),
    kappa=(c/(4*gamma))^(D/2)>0.                        (11)

This holds for any translated initial coordinate grid, and any order of
singleton excisions. The algorithm retains its starting grid, only refines,
uses maximum initial side ell<=floor(2sqrt(tau/c)) when tau>=c/4, and
retains EACH a<tau vertex as a distinct singleton. The tau<c/4 branch is
the singleton grid. It does not permit subsequent coarsening, replacing
bad singletons by cluster averages, deleting outputs or changing the map.
Those operations would be different constructions and are NOT refuted.

Yet the very SAME profiles admit an explicit partition with only D+1
rectangles and the actual global all-cochain fixed-penalty inequality (1).
All family parameters D,c,Nc and the critical moment bound M=2 are fixed,
while the original target maximum is1 for every t.

### The original coefficient constraints are verified, not assumed

Since f<=1/2, b>=1 and b<=m, direct algebra gives

    A=m+f*(m-b)/(1-f) >=m,
    A<=m/(1-f)<=2m,
    1<=a<=2m,   mean(a)=f*b+(1-f)*A=m.

Moreover m/b=n and A>=m, so the EXACT critical moment satisfies

    mean((m/a)^p)=f*n^p+(1-f)*(m/A)^p <=2-f<2.           (12)

Thus M=2 works uniformly. Because gamma>=1,
max(1,n^D/(1+m)^p)=1. Unlike the fixed weak-box example of unit103, this
weak cube GROWS with t, and its weak coefficient b also grows: there is
no fixed W bounding a on S. The additional bounded-weak-coefficient gap
from Section5 is therefore not silently available.

### Why EVERY threshold loses: a complete two-case proof

If tau<=b, then B_tau is empty since A>=m>=b. For tau<c/4 the output is
the singleton grid, with n^D leaves. Otherwise ell=floor(2sqrt(tau/c)),
capped at n. Our choice n>4gamma/c implies

    2sqrt(tau/c)<=2sqrt(gamma*n/c)<n,

so the cap does not activate. Every initial cell has volume<=ell^D,
independently of translation or terminal-interval alignment. No bad point
is excised and no cell is coarsened. Hence

    N_tau >= n^D/ell^D
           >= n^D/(2sqrt(gamma*n/c))^D
            = kappa*n^(D/2).

The same bound holds in the singleton branch, since kappa<=1.
Equality tau=b belongs to this case because the bad threshold is STRICT.

If tau>b, every one of the s=n^(D/2) vertices of S belongs to B_tau.
They are distinct retained singleton leaves at termination, regardless
of what happens to the complement. Thus N_tau>=s>=kappa*n^(D/2).
This also covers tau>A, when all vertices are bad. It is a lower bound
on the ACTUAL retained leaves, not on an upper-bound formula in Section4.
This proves (11) for all finite tau>=1.

The chosen observation codomain is the literal h*N_tau-dimensional space
of all normalized block outputs. We do not turn the leaf-count statement
into a lower bound for arbitrary compressed observations on the physical
subspace. No nonlinearity or interaction claim is involved.

### A D+1-block averaged observation actually succeeds

Retain the WHOLE cube S as ONE block, not s singleton blocks. Partition
its complement into the D rectangles

    R_i=[0,t-1]^(i-1)*[t,n-1]*[0,n-1]^(D-i), i=1,...,D.

Every point outside S has a unique first coordinate outside [0,t-1],
proving coverage and disjointness. All these blocks are nonempty for t>=2.
On S the coefficient is b, so the SAME proved path/product estimate (5)
gives

    c*Var_S(U) <= [c*t^2/(4*b)]*E_a,S(U)
               = [c/(4*gamma)]*E_a,S(U) <= E_a,S(U).

On each R_i all internal edges start at coefficient A>=m=gamma*n^2,
and every side is <=n, so

    c*Var_(R_i)(U) <= [c*n^2/(4*A)]*E_a,R_i(U)
                   <= [c/(4*gamma)]*E_a,R_i(U)
                   <= E_a,R_i(U).

Apply these estimates coordinatewise to the actual field. Internal edges
of the D+1 blocks are disjoint; omitted crossing/wrap edges are positive.
With the exact orthogonal decomposition for normalized means this proves

    c||U||^2 <= E_a(U)+c||C_P(U)||^2 for ALL cochains,
    #P=D+1,  dim F=h*(D+1).                             (13)

This is an actual successful observation on exactly the family in (10),
not merely the spectral-existence theorem or an assumed kernel estimate.
It consequently holds on actual divergence-zero fields as a restriction.
No block-average divergence-preservation assertion is needed.

### Interpretation and verification limits

The D/4 decay scale of Section1 is sharp as a UNIFORM RATE FOR THIS
single-threshold point-excision algorithm family: along (10), n^D/m^(D/4)
is a fixed multiple of n^(D/2), matching (11). Any proposed larger decay
exponent in m for that family is contradicted by the same sequence. It is
NOT the optimal rate for unrestricted rectangular observations; (13)
already gives a constant number of blocks on these very profiles.

The obstruction is an intermediate-conductance cluster with b proportional
to its squared side length. A small threshold unnecessarily resolves the
whole torus at scale sqrt(b); a large threshold unnecessarily isolates
every vertex of the cluster. A stable cluster average avoids both costs.
Choosing a different global threshold, a translated grid or excision order
cannot fix THIS mechanism. The Section5 target bound under an extra fixed
coefficient gap remains valid and is not contradicted.

Analytic checks: t integer ensures n=t^2 and exact s=n^(D/2) even for odd D;
actual arithmetic mean/cap/lower bound; fixed M=2; gamma and n restrictions;
strict tau=b boundary, small tau, tau>A and capped-grid cases; actual-volume
leaf lower bound versus an upper formula; preservation of singleton outputs;
same-profile D+1-block coverage; strong starting-vertex weights and weak
cube normalization; all-cochain/fixed-penalty/physical restriction distinction.
No executable arithmetic, Lean or numerical check was run.

The only classical analytic input remains the variance tensorization cited
in Section7; its primary author-hosted statement and conditioning/Jensen
proof were rechecked this unit. The cube-plus-first-outside complement
geometry is adapted from the dossier's unit103, with growing weak size and
conductance and an additional ALL-threshold lower bound. No independent
novelty or exhaustive priority finding is claimed. Same preparing Codex
agent, actual served backend/effort unexposed; no independent/human review,
new numerical grade, PDF-score inheritance, deposit or publication.

Keep ONE active original critical rectangular question. This is unit2 of
the actual-excision route without general-target closure; it gives a useful
class-wide algorithm refutation. STOP single-global-threshold/per-vertex
excision as a route to that target now, rather than waiting for a third
retuning attempt. Keep its valid D/4 theorem. Old stopped-route counters3
remain unchanged and are not reset. The next mechanism needs actual stable
averages of intermediate-conductance CLUSTERS with a proved rectangular
count; (13) supplies a closed benchmark, not that general construction.
PR29 remains20/41,TermSource=0; interacting/continuum gap stays open.
