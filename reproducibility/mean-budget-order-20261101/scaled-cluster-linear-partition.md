# Linear rectangular means for arbitrarily placed scaled clusters

Unit117, 4 November2026. Analytic extension of
`scaled-cluster-rectangular-means.md` (unit116). Same critical dossier;
not a separate paper. No Lean/numerical verification or new PDF review.

## 1. Result and unchanged coefficient restrictions

Let D>=3, p=D/2, h=D(Nc^2-1), c>0, m>=1 and beta>=1. On
X={0,...,n-1}^D retain the original scalar assumptions
1<=a<=2m, mean(a)=m, mean((m/a)^p)<=M. Suppose additionally that
there are J pairwise disjoint integer cubes S_k, of side L_k>=1,
nonwrapping in this common root, satisfying

    c L_k(L_k-1)/4 <= a(x) <= beta L_k^2  (x in S_k),
    a(x) >= c n(n-1)/4                    (x outside their union).

There is a constant A_D>=1 depending only on D and an actual integer
rectangular partition P such that

    N=|P| <= A_D max(1,J),
    c ||U||^2 <= E_a(U) + c ||C_P U||^2,
    (C_P U)_(R,j) = sqrt(|R|) mean_R U_j,
    dim F = h N
          <= h A_D [1+2^p beta^p M]
             max(1,n^D/(1+m)^p).                         (1)

This holds for all cochains U and thus on the actual physical subspace.
No separation of cluster projections and no m>=gamma n^2 restriction
are required. The displayed coefficient/cube assumptions remain real
additional assumptions: their existence has NOT been derived for every
profile in the original critical class. The original question stays open.

## 2. Primary geometric input and its precise specialization

Mark de Berg, *Linear Size Binary Space Partitions for Uncluttered
Scenes*, Utrecht technical report UU-CS-1998-12:
https://ics-archive.science.uu.nl/research/techreps/repo/CS-1998/1998-12.pdf
(checked4November2026, printed pp.4,7-9).

Source input: Lemmas2.1/2.4 give a linear-size axis-parallel intermediate
partition with bounded object occupancy per cell for uncluttered scenes.
Section2.1 separates remaining polygonal fragments using their facet
planes. Corollary2.9 applies to disjoint full-dimensional fat objects
of constant complexity. Cubes have fixed fatness in each fixed dimension.

Specialization: for axis-aligned solid cubes every facet plane is also
axis-parallel. Thus BOTH stages use axis-parallel planes, and the final
BSP has at most B_D max(1,J) rectangular leaves, each open leaf meeting
at most one solid cube. Fragmenting input cubes is permitted. We do not
claim that a whole cube must survive as one leaf, or that arbitrary fat
objects admit a rectilinear final BSP. Surface-only fat rectangles in
three-space are a different class. This is a classical geometric input,
not a new linear-BSP theorem or an exhaustive originality finding.

## 3. Discrete boundary and membership adapter

Write S_k=product_i {b_ki,...,b_ki+L_k-1}. Replace it geometrically by

    Q_k=product_i [b_ki-1/4, b_ki+L_k-3/4].

Each Q_k is a positive-side solid cube, including L_k=1; its integer
points are exactly S_k and every such point is in its interior. If two
integer cubes are disjoint, some coordinate intervals of their integer
sets are disjoint. The corresponding closed Q intervals have gap at
least1/2. Hence these real solids are strictly disjoint even when the
original unit-cell interpretations would touch. Their fixed fatness
is unaffected by side length or J.

Apply section2 to Q_k. Intersect all leaves with the outer box
[-1/2,n-1/2]^D. Assign each splitting hyperplane to one child consistently,
e.g. t<=s versus t>s. These half-open/closed interval conventions give a
disjoint cover; taking integer points and deleting empty cells produces
integer rectangles and does not increase their number.

There is a boundary subtlety: the geometric BSP separation refers to OPEN
leaves. Nevertheless, any integer x of a leaf lying in some S_k is in
the interior of Q_k. An open ball about x is contained in Q_k. Every
full-dimensional leaf having x in its closure meets that ball in its
interior. Therefore that open leaf meets Q_k. It follows that the integer
points assigned to one leaf can belong to at most one S_k. Degenerate
clipped cells on the outer boundary contain no integer points, since
that boundary has half-integer coordinates. The original BSP leaves are
full-dimensional; boundary ownership creates no separate hyperplane cells.

A leaf with integer points in S_k can still contain integer points outside
S_k. Refine it using all 2D facet coordinates of Q_k. There are at most
three intervals per coordinate, hence at most3^D subrectangles. One lies
inside Q_k; all others lie outside Q_k. No integer lies on these facet
coordinates, and no other S_l has integer points in this leaf. Thus every
resulting integer rectangle is contained in a single S_k or is outside
ALL clusters. Leaves with no cluster integer points need no refinement.
Consequently N<=3^D B_D max(1,J); take A_D=max(1,3^D B_D).
For J=0 use the single root rectangle. This proves an ACTUAL partition
without assuming a Poincare/kernel/rank certificate. It is an existence
construction, not a measured implementation or an explicit sharp A_D.

## 4. Stability uses the original weighted edges

Unit116 section3 derives by path counting and product variance that for
a rectangle R with maximal integer side length L,

    sum_R |u-mean_R u|^2
       <= L(L-1)/4 sum_(internal directed +i edges of R) |du|^2.

For R contained in S_k its side lengths are <=L_k. The assumed lower
bound for every starting vertex in S_k therefore gives
c Var_R(u)<=E_(a,R)(u). For a rectangle outside all clusters its maximal
side is <=n, and the outside lower bound gives the same conclusion.
Singleton residuals vanish, so L_k=1 or n=1 needs no division by zero.

Sum over R and every real component of U_j. The retained original edges
are disjoint occurrences; omitted interblock and wrap occurrences are
nonnegative, including the parallel occurrences when n=2. Finally

    ||U||^2 = sum_(R,j) Var_R(U_j) + ||C_P U||^2

gives the GLOBAL fixed-penalty inequality in section1. This does not use
the false implication from a kernel-only bound to penalty K=c, nor does
it require averaging to preserve the divergence constraint. Fragmentation
causes no stability loss because smaller rectangular sides only improve
this variance estimate; no aspect-ratio estimate is being smuggled in.

## 5. Moment charge and all-budget target

For each supplied cluster, its actual upper bound gives

    sum_(x in S_k) a(x)^(-p)
      >= L_k^D/(beta L_k^2)^p = beta^(-p).

Disjointness and the original moment imply
J<=beta^p M n^D/m^p. This is a proved charge, not an assumed count.
Since m>=1, n^D/m^p<=2^p n^D/(1+m)^p. Combining with section3 and
max(1,J)<=1+J proves (1). Constants depend on D,c,Nc,M,beta as stated
(the geometric A_D only on D). All m are covered, including the regime
where the earlier arrangement bound (2J+1)^D was too large. Empty
clusters are not introduced; n=1, J=0 and J=1 are included.

## 6. What has and has not advanced

Projection separation, previously required for unit116's all-budget
linear count, has been removed by an applicable classical geometric
theorem plus the discrete and energy adapters above. Its high-budget
restriction is also unnecessary for this restricted coefficient class.
The polynomial arrangement remains a valid elementary fallback, not an
optimal general count. Whole-cluster preservation was unnecessary.

Still unproved: deriving suitable disjoint cubes with BOTH scale bounds
and a sufficiently strong complement from the original moment alone.
The very strong complement bound can fail for many original profiles.
No theorem here removes those coefficient restrictions, settles the
general critical target, constructs an interacting/covariant producer,
or proves a continuum/physical spectral gap. PR29:20/41,TermSource=0.

Analytic verification covers strict disjointness, solid rather than
surface fatness, both stages' cut directions, boundary ownership,
fragmentation, integer rectangle coverage, 3^D refinement, original
starting-edge weights, fixed penalty, singleton/wrap cases, critical
charge and m-to-(1+m) conversion. No local executable mathematics,
Lean, numerical run, Colab allocation, new score or independent review.
Same preparing Codex agent; served backend/effort unexposed. No old PDF
assessment applies to this note. No AIRR/ai.viXra deposit or publication.

One original active question only. Scaled-cluster route now has a second
substantive analytic unit, with geometry resolved for supplied cubes but
the coefficient-derived decomposition blocker still open. Earlier
mass-only/Schur/one-global-threshold stopped routes and counters remain
unchanged. Next bounded step: test whether a stopping-cube selection from
the coefficient field can supply the actual scale lower bounds and strong
complement, and document an explicit obstruction if not. Do not assume
this decomposition as a structure or count restricted progress as closure.
