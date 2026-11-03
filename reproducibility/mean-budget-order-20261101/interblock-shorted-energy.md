# Fixed mean penalty requires shorted energy, not kernel energy

3 November 2026. First analytic unit of the inter-block mechanism. Finite
linear algebra and an exact weighted cycle example; no Lean, numerical run,
independent review, endpoint closure or new paper. This is a classical
Schur-complement adapter with a concrete diagnostic, not an originality claim.

## 1. Exact finite reduction

Let L be a positive semidefinite self-adjoint operator on a finite real
Euclidean vertex space. A partition into nonempty blocks defines
C u = (sqrt(|B|) mean_B u)_B. Then C C* = I, P=C*C is the orthogonal
projection onto block constants, and Q=I-P. The proposed FIXED penalty is
c||Cu||^2. Consequently the desired inequality for ALL u is exactly

    <u,Lu> >= c||Qu||^2.                                      (1)

Write u=p+v in M=ran P and N=ran Q, and put

    A=PLP|M, B=PLQ:N->M, D=QLQ|N.

If k is in ker A, positivity implies Lk=0: the nonnegative quadratic
polynomial <k+t z,L(k+t z)> has zero constant term, so its linear term
vanishes for every z. Hence <k,Bv>=0 and Bv belongs to ran A. In finite
dimension let A^dagger invert the positive eigenspaces and vanish on ker A.
Completing the square, with no invertibility assumption, gives

    <p+v,L(p+v)>
      = <p+A^dagger Bv,A(p+A^dagger Bv)>
          + <v,(D-B* A^dagger B)v>.                         (2)

Thus (1) is equivalent to

    S := D-B* A^dagger B >= c I_N.                           (3)

The infimum over p is attained at -A^dagger Bv, up to ker A. Positivity of
L also proves S>=0. A bound D>=c I_N only tests u in ker C and omits a
nonnegative correction. It is insufficient at the SAME fixed c.
Correction rank is at most rank A. For a connected positive-weight graph,
ker A consists exactly of global constants, so rank A=number of blocks-1.
This rank bound alone supplies no lower bound on S.

This is not the result for arbitrary freely enlarged penalty K||Cu||^2.
For K different from c the M block becomes A+(K-c)I; that is a different
criterion. No conclusion about the broader nonlinear observation class is
inferred from failure of the fixed penalty.

## 2. What remains of inter-block edges

For a weighted graph, split edges into internal and crossing edges.
Internal energy is unchanged by adding block constants. If z(v) is the
oriented vector of crossing differences of v, H maps block values to their
oriented crossing differences, and W contains positive crossing weights,
then the exact minimization is

    <v,Sv> = E_internal(v)
       + ||(I-Proj_ran(W^(1/2)H)) W^(1/2) z(v)||^2.          (4)

Indeed crossing energy is ||W^(1/2)(z(v)+H alpha)||^2; least-squares
projection proves (4). Every block-constant p corresponds to some alpha,
so no mean variables were omitted. Repeated edges between a pair of blocks
are retained as distinct rows of H. A connected quotient MULTIGRAPH that
is a tree has number of crossing edges=blocks-1 and H is onto edge space;
then the second term is zero. Thus counting all crossing energy before
minimizing block means can overestimate the usable coercivity. Parallel
face edges/cycles are precisely where a nonzero residual can remain.
This does not say that a lattice partition has a tree multigraph.

## 3. Exact four-cycle: kernel bound passes, full inequality fails

On vertices0,1,2,3, give oriented forward cycle edges respective weights
(1,6,4,1). Partition into {0,1} and {2,3}. The weights have minimum1,
mean m=3 and maximum6=2m. Every v in ker C is (x,-x,y,-y), so

    ||v||^2 = 2(x^2+y^2),
    E(v) = 4x^2+16y^2+7(x+y)^2.

At c=19/5 the restricted difference is

    E(v)-c||v||^2
      = (17/5)x^2+14xy+(77/5)y^2
      = (17/5)(x+(35/17)y)^2+(84/85)y^2 >=0.                (5)

In contrast, the two crossing edges contribute, after allowing difference
delta of block constants,

    6(delta-x-y)^2+(delta+x+y)^2.

Its minimum occurs at delta=5(x+y)/7 and equals (24/7)(x+y)^2.
Thus the actual shorted form is

    <v,Sv> = 4x^2+16y^2+(24/7)(x+y)^2.                     (6)

Choose v=(1,-1,0,0), block constants p=(5/14,5/14,-5/14,-5/14),
and u=v+p=(19/14,-9/14,-5/14,-5/14). The original energy is

    E(u)=4+6*(2/7)^2+(12/7)^2=52/7,
    ||Qu||^2=2,
    E(u)-c||Qu||^2=52/7-38/5=-6/35 <0.                    (7)

Equivalently ||Cu||^2=25/49 and ||u||^2=123/49, giving the same failure
of E(u)+c||Cu||^2>=c||u||^2. This checks both normalized observations and
the full original scalar quadratic form, not a proposed certificate.

The example refutes the general implication from kernel coercivity to the
same fixed-penalty inequality, even with the stated scalar weight cap.
It does not defeat every partition: singleton blocks have Q=0.

## 4. Actual lattice witness and exact limits

For fixed D>=3 on (Z/4Z)^D, set the actual scalar-start coefficient
a(x)=(1,6,4,1) according to x_1. It satisfies 1<=a<=2m, mean a=m=3,
and its normalized critical inverse moment, p=D/2, is exactly

    M_D = [2*3^p+(1/2)^p+(3/4)^p]/4.

Use the two axis-aligned slabs {0,1} times the other coordinates and
{2,3} times the other coordinates. Put u(x_1) from (7) into one internal
real direction of cochain component2; set all other components zero.
It is actual flat divergence-free because independent of x_2. Actual
scalar total stiffness equals the weighted forward-gradient energy here.
Every displayed norm/energy is multiplied by 4^(D-1), including the
normalized slab-mean penalty. Thus THIS partition fails the desired
full inequality on an actual admissible divergence-zero field.

However (5) only establishes the restricted-kernel estimate in the
four-cycle (equivalently transverse-constant sector). It is NOT a proof
that the full D-dimensional kernel passes: transverse modes were not
tested and can violate that stronger assertion. Nor is this fixed-size
example an asymptotic rank lower bound, an all-partition falsifier, or
an obstruction for arbitrary penalty K. Those claims are not made.

## 5. Prior art, audit and next falsifiable step

The shorted-operator mechanism is classical. Primary source checked:
W. N. Anderson Jr. and G. E. Trapp, Shorted Operators. II, SIAM Journal on
Applied Mathematics28(1),60-71(1975), DOI10.1137/0128007,
https://epubs.siam.org/doi/10.1137/0128007 . Its accessible abstract and
metadata identify the positive-operator/network construction; the full
article was not accessed. Equations(1)-(7) above are proved directly,
not attributed as a newly verified theorem in an inaccessible full text.
The primary source establishes relevant prior art, not exhaustive novelty.

Verification: analytic completion of squares with singular A; exact
orthogonal observation normalization; least-squares crossing minimization;
cycle determinant/completed square84/85; minimizer5/7; witness energy52/7;
full defect-6/35; counting norm123/49; observation norm25/49; scalar cap
and mean; critical moment; transverse multiplicity and actual divergence.
No executable arithmetic, numerical campaign, Lean or independent audit.

FIRST exact-note self-assessment4/10 by the preparing Codex agent, backend
identity/effort unexposed. Qualitative rubric: derivation7, originality1,
dossier relevance5, formal/general maturity2. Not AIRR's rating scale.
Objections: (i) classical reduction, no novelty established; (ii) no uniform
partition count or critical estimate for S; (iii) kernel-pass statement
only cycle/sector, not full physical kernel; (iv) prescribed partition only;
(v) fixed penalty c, not arbitrary K; (vi) no formal/executable verification;
(vii) no independent assessment or physical/continuum result. All retained.

ONE active question remains the critical-moment rectangular rank target.
The next mechanism must bound the residual crossing term in(4) or prove
S>=cI for an actually constructed partition with target count. Writing S
into an assumed structure eliminates no hypothesis. Useful falsifier must
defeat EVERY permitted rectangular partition. This is mechanism unit1
without a global endpoint advance; preserve old-route counter3. After
three such units identify a concrete obstruction or change route. No new
PDF/paper/AIRR deposit, no inherited score. PR29 remains20/41,TermSource=0.
