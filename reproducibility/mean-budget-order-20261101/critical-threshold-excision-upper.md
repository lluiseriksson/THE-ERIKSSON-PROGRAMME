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
classical; no optimality or originality established; no interacting or
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
