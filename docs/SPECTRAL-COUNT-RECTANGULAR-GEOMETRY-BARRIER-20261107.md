# A positive graph Laplacian with one low mode and a linear rectangular-mean cost

Hash context: based on programme main
`88f31a1981b757b9240a9076e2012545066b9028`; analytical unit175,
7 November2026. This is a research note for consolidation, not a new paper,
formal certificate, independent review or priority claim. The public v7 PDF
and its assessment are unchanged.

## Question and scope

The single active programme question concerns critical inverse-moment
profiles in the **actual nearest-neighbour flat lattice Hodge form** and
axis-aligned integer rectangular mean partitions. A global spectral
observation already has the desired rank order. Can eigenvalue counting
alone turn that global observation into rectangular means?

Here is a scoped negative answer to that abstract conversion, even for a
connected positive weighted graph Laplacian. For arbitrarily large vertex
sets, the mean-zero spectral subspace below the target has dimension one,
but every successful rectangular mean partition requires at least one
third of all vertices as cells. Every partition below that count fails,
not just a tree, grid or particular algorithm. An arbitrary finite penalty
on the means cannot cure this kernel failure.

The graph is deliberately **nonlocal**. It is not an admissible scalar
nearest-neighbour coefficient profile, not a divergence-free Hodge
construction, and not a counterexample to the original question. What is
eliminated is the stronger proposed implication using only spectral
dimension, positivity of graph weights and a graph Laplacian structure,
without the original locality or an additional geometric inequality.

## The construction

Let n be even, D>=1, X=(Z/nZ)^D and N=n^D. Use counting inner products
on R^X. Put e=N^(-1/2)1 and

    sigma(x)=(-1)^(x_1+...+x_D),   v=N^(-1/2)sigma.

Then e and v are orthonormal. Let 0<a<c<b and define

    L=b(I-ee*)-(b-a)vv*.

The constants have eigenvalue0, v has eigenvalue a, and the orthogonal
complement of span{e,v} has eigenvalue b. In particular, on H=e-perp
there is exactly one eigenvalue below c. One unrestricted scalar
observation C(f)=<v,f> repairs the target globally on H:

    <Lf,f>+(c-a)|C(f)|^2 >= c||f||^2.

This rank-one repair is an explicit equality on span{v}, not an assumed
certificate. Its coefficient c-a is finite and positive.

For x!=y the off-diagonal matrix entry of L is -w_xy, where

    w_xy=[b+(b-a)sigma(x)sigma(y)]/N.

Thus every edge has positive weight, either a/N or (2b-a)/N. L1=0,
so its diagonal is the sum of these weights and

    <Lf,f>=sum_{unordered {x,y}} w_xy (f(x)-f(y))^2.

For a=c/2 and b=2c, the two weights are c/(2N) and 7c/(2N):
the graph is connected and their ratio is only7. This does not make it
spatially local; long edges are essential to this example.

Even the full graph up to isomorphism does not determine its rectangular
observation cost in a supplied coordinate embedding. Replace sigma by
tau, equal to+1 on the half-slab 0<=x_1<n/2 and-1 on the other half.
Both sign classes have N/2 points, so a vertex permutation taking their
classes to the checkerboard classes conjugates the two Laplacians.
They have the same spectrum, edge weights and unlabelled weighted graph.
For the slab labelling, the two half-slabs form an allowed rectangular
partition with t=1 and K=c-a; its mean-zero observation rank is one.
The checkerboard labelling needs q>N/3 cells by the argument below.
The missing information is coordinate geometry, rather than another
unlabelled spectral invariant.

## Exact kernel angle calculation

Let a partition P consist of q nonempty disjoint cells covering X, and
let S be the span of the orthonormal vectors |R|^(-1/2)1_R. Write Pi
for the orthogonal projection onto S and put

    t=||Pi v||^2.

The zero-mean kernel of the cell observations is S-perp, since e belongs
to S. If t<1, the nonzero vector u=(I-Pi)v lies in that kernel and H,
and direct expansion gives

    ||u||^2=1-t,   <v,u>=1-t,
    <Lu,u>/||u||^2 = b-(b-a)(1-t) = a+(b-a)t.       (1)

Indeed this is the smallest Rayleigh quotient on S-perp: there the
quadratic form is b||f||^2-(b-a)|<u,f>|^2 and Cauchy-Schwarz is sharp
at f=u. If t=1 and the kernel is nonzero, its quotient is identically b.
If q=N the kernel is zero and no minimum quotient is asserted.

Consequently a necessary condition for target c on a nonzero kernel is

    t >= (c-a)/(b-a).                                  (2)

Uniqueness on the one-dimensional low eigenspace only requires Pi v!=0.
Equation(2) requires a fixed quantitative angle. These are different
claims, even when arbitrary finite penalty coefficients are allowed.

## Every rectangular partition below the bound fails

Now require R=I_1 x ... x I_D, with each I_j an integer cyclic interval.
An alternating sum over any such interval has absolute value at most1,
including wrapped intervals because n is even. Taking products gives

    |sum_{x in R} sigma(x)| <= 1.

It follows, with the same orthonormal observation convention as above,
that

    t = (1/N) sum_{R in P} (sum_R sigma)^2/|R|
      <= (1/N) sum_{R in P} 1/|R| <= q/N.              (3)

Combining(2) and(3), any target-c rectangular mean partition must have

    q >= N (c-a)/(b-a).                                (4)

In the particular positive-weight example a=c/2,b=2c, every q<N/3
partition has a nonzero mean-zero kernel vector with Rayleigh quotient
strictly less than c. Thus q>=ceil(N/3) is necessary. No sufficiency or
sharpness of this cell-count bound is claimed.
The full scalar cell map has rank q; its restriction to H has rank q-1.
Thus the distinction between cells and observation rank changes this
linear lower bound by one, not its order.

This rules out a dimension-only bound q<=F(k,c,a,b,D) independent of N:
k=1 on H is fixed while the required q tends to infinity.

For any penalty U with U(0)<=0, the means of su vanish for every real s.
Hence <Lsu,su>+U(0)<c||su||^2 for every s!=0 if U(0)=0, and also for
U(0)<0. The failure occurs arbitrarily close to0. In particular, any
penalty locally bounded above by K||y||^2, for any finite K, fails.
This addresses the original *free finite penalty* distinction; it is not
merely a failure of a prescribed value K=c.

## The finite-penalty endpoint is also explicit

For this example one can calculate the full endpoint, rather than assume
that nonnegative kernel margin is sufficient. Put d=b-c>0 and r=b-a.
On H, L-cI+KPi=dI+KPi-rvv*. For K>=0, the positive operator
B=dI+KPi is invertible. By Cauchy-Schwarz after the substitution B^(1/2)f,
B-rvv* is nonnegative if and only if r<v,B^(-1)v><=1. As Pi is a
projection, this condition is exactly

    r[(1-t)/d+t/(d+K)] <= 1.

Solving it gives the following exact criterion and minimum coefficient:

    some finite K exists  iff  rt>c-a;
    K_min=(b-c)(c-a)/[(b-a)t-(c-a)].                    (5)

At rt=c-a the first summand already equals1 and the second is positive
for every finite K. Thus the non-strict kernel endpoint in(2) cannot be
rescued. This is an explicit instance of the classical singular-Schur
compatibility issue, not a claim to a new Schur principle. A penalty
locally bounded above by K times the squared normalized means cannot
outperform this quadratic test; conversely the displayed quadratic
penalty attains it.

In particular, for a=c/2,b=2c, successful finite-penalty rectangular
data require t>1/3, hence q>N/3. The integer lower bound is therefore
floor(N/3)+1. The weaker kernel-only statement(4) remains valid.

## Hand checks and proof audit

* Two parity classes each have N/2 vertices. The weighted degree is
  ((N/2-1)(2b-a)+(N/2)a)/N=b-(2b-a)/N, precisely L_xx.
* A full even-sided cube has t=0 and witness v with quotient a<c.
* Singleton cells give t=1, and the observations see the entire space;
  this lies outside the nonzero-kernel minimum statement.
* For D=3,n=2,N=8,a=c/2,b=2c, every two-cell rectangular partition
  has t<=1/4 and the witness quotient is at most7c/8<c.
* On H, a single point evaluation uniquely determines a scalar multiple
  of v; on span{e,v}, two opposite-parity point samples are a uniqueness
  set. Neither observation fact proves full-domain target coercivity.
* The cell-count constant is not silently upgraded to1/2. On the 1D
  cycle of length16, take six consecutive singleton cells and the
  remaining interval of length10: q=7<N/2, t=6/16=3/8. For c=1,
  a=1/2,b=2, equation(5) gives K_min=8, so this partition succeeds.
  This is a hand-derived exact boundary check, not an executed replay.
* The proof uses no eigenvalue enumeration, asymptotic approximation,
  supplied geometry certificate, local Lean build or numerical verdict.
  It is an elementary analytic proof, not machine verification. A replay
  specification is retained separately for Linux/Colab if needed.

## Relation to primary literature and the programme

Pesenson's graph sampling paper describes uniqueness sets through
Poincare-Wirtinger inequalities and reconstructs bandlimited signals:
<https://arxiv.org/abs/1111.5896> (journal publication2008, arXiv2011).
This note does not contradict that theory. It explicitly separates
uniqueness within a low spectral subspace from coercivity on all H.

Pesenson and Pesenson, *Graph Signal Sampling and Interpolation Based on
Clusters and Averages* (2021), use cluster Poincare inequalities to
control averages and gradients. The institutional abstract is at
<https://authors.library.caltech.edu/records/4k4df-0v819>. Only its abstract
was verified here; no theorem from inaccessible full text is invoked.
Its geometric/Poincare input is exactly the sort of ingredient a
dimension-only conversion would discard.

Hundertmark, Kunstmann, Ried and Vugalter, *Cwikel's bound reloaded*,
<https://arxiv.org/abs/1809.05069>, supplies context for spectral counting;
it does not assert rectangular support for the spectral observations.
No new CLR result is claimed here.

Davydov, Kozynenko and Skorokhodov, *Optimal approximation order of
piecewise constants on convex partitions*,
<https://arxiv.org/html/1904.09005v2>, Sections1--3, adapts partitions to
individual Sobolev functions using polyhedral slices perpendicular to
their averaged gradients. Such a function-dependent, possibly oblique
partition is not a single axis-aligned partition controlling every
vector in the kernel of an observation map for a given coefficient.
This is a quantifier and geometry distinction, not a refutation of their
approximation theorem.

The search was targeted, not an exhaustive internet or novelty audit.
The projection algebra, checkerboard cancellation and distinction between
uniqueness and stability are elementary/classical ingredients. No claim
that this precise example is previously unpublished is made.

## Disposition

Close the locality-free spectral-count-to-rectangular-means shortcut now.
Do not spend three further units trying to obtain geometry from k alone.
Retain the narrower original nearest-neighbour critical inverse-moment
question as the only active question. A next constructive mechanism must
use actual local edge energy to derive a uniform observation angle or
kernel Poincare margin; merely moving such a margin into a structure is
not eliminating a hypothesis.

This note should be grouped with the existing trace-certificate and
spatial-localization obstructions if a later substantive manuscript
revision is warranted. It is not submitted as a separate small paper.
PR29 remains20/41, TermSource=0; the continuum Yang-Mills problem is open.
